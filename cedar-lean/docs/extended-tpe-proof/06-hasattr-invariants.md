# `hasAttr` Invariants and the Target Delegation Asymmetry

## 1. The Problem `hasAttr` Must Solve

In concrete Cedar, `hasAttr v a es` checks whether attribute `a` exists:

```lean
def hasAttr (v : Value) (a : Attr) (es : Entities) : Result Value := do
  let r ← attrsOf v (fun uid => .ok (es.attrsOrEmpty uid))
  .ok (r.contains a)
```

It always succeeds (never errors) for entities and records — it returns `true` or `false`. For entities, it uses `attrsOrEmpty`, which returns an empty map for missing entities (so `hasAttr` returns `false` for any attribute on a missing entity).

In the extended TPE, `hasAttr` must handle three levels of unknownness:
1. The receiver itself is unknown (not a value)
2. The receiver is a known entity but its attributes are unknown (`attrs = none`)
3. The receiver is a known entity/record with known attribute map, but a specific attribute's *value* is unknown

Each level produces a different residual, and each has different soundness obligations.

## 2. The Three `hasAttr` Paths in TPE

```lean
def hasAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty

  -- PATH A: Record literal with ResidualAttributes
  | .val (.record m) _ =>
    match m.find? a with
    | some (.present _) => true           -- known present → true
    | some (.unknown tgt _) => .hasAttr tgt a ty  -- unknown value → delegate to TARGET
    | none => false                       -- known absent → false

  -- PATH B: Entity UID with partial entity store
  | .val (.prim (.entityUID uid)) _ =>
    match es.attrs uid with
    | .some attrs =>
      match Map.find? attrs a with
      | .some (.present _) => true        -- known present → true
      | .some (.unknown _) => .hasAttr r a ty  -- unknown value → delegate to SELF
      | .none => false                    -- known absent → false
    | .none => .hasAttr r a ty            -- attrs entirely unknown → residual

  -- PATH C: Non-value receiver
  | _ => .hasAttr r a ty                  -- can't resolve → residual
```

## 3. The Critical Asymmetry: Target vs Self Delegation

This is the most subtle invariant in the entire target mechanism.

When `hasAttr` encounters an unknown attribute value:

- **On a record** (Path A): delegates to `.hasAttr tgt a ty` where `tgt` is the *target* stored in the `ResidualAttribute.unknown`
- **On an entity** (Path B): delegates to `.hasAttr r a ty` where `r` is *the entity residual itself* (i.e., `self`)

These are different expressions that must both be semantically correct, but for different reasons.

### 3a. Why records delegate to the target

A `ResidualValue.record` with unknown fields was produced by `PartialValue.toResidualValue`. The unknown field's target points to the *original container* — typically the entity that owns this record. When we ask "does attribute `a` exist?", we can't answer from the record alone (the value is unknown, but the attribute *key* is present in the partial map — does that mean it exists in the concrete record?).

The answer is: **yes, the key exists** — but the TPE doesn't exploit this. Instead, it conservatively delegates to the target, asking "does `a` exist on the original entity?". This is sound but potentially imprecise.

**Wait** — let me reconsider. If `m.find? a = some (.unknown tgt _)`, that means attribute `a` *is* in the `ResidualValue.record`'s map. In the concrete record, `a` definitely exists (the partial map was derived from the concrete map via `toResidualValue`, which preserves all keys). So `hasAttr` should return `true`, not a residual.

But the code returns `.hasAttr tgt a ty` — a residual. **This is conservative but not tight.** The attribute is guaranteed to exist, but the TPE doesn't prove this and instead defers to re-evaluation.

**Invariant (Record hasAttr conservatism)**: When `hasAttr` on a record delegates to the target for an unknown field, the concrete answer is always `true`. The residual `.hasAttr tgt a ty` will evaluate to `true` at re-evaluation time. This means the delegation is sound (it produces the right answer when fully evaluated) but imprecise (it could have been reduced to `true` immediately).

### 3b. Why entities delegate to self

When `hasAttr` on an entity finds `.some (.unknown _)` in the partial attribute map, it returns `.hasAttr r a ty` where `r` is the entity residual itself (e.g., `.val (.prim (.entityUID uid)) (.entity ety)`).

This is different from the record case because:
- The entity's partial attribute map comes from `PartialEntities`, not from `toResidualValue`
- There is no "target" stored in `PartialAttribute PartialValue` — the `PartialAttribute.unknown` only stores a `CedarType`, not a target expression
- The entity residual `r` is the natural expression to delegate to — "check if `uid` has attribute `a`"

**Invariant (Entity hasAttr self-delegation)**: `.hasAttr r a ty` where `r = .val (.prim (.entityUID uid)) _` evaluates via `Residual.evaluate` to `Spec.hasAttr (.prim (.entityUID uid)) a es`, which looks up `uid` in the concrete entity store. This is always sound.

### 3c. The asymmetry summarized

| Receiver | Unknown field source | Delegation target | Why |
|---|---|---|---|
| Record (`ResidualValue.record`) | `ResidualAttribute.unknown tgt ty` | `tgt` (stored target) | Record was derived from entity; target points back to entity |
| Entity (`EntityUID`) | `PartialAttribute.unknown ty` | `r` (self = entity residual) | Entity is the natural lookup target |

The asymmetry exists because records and entities store unknownness differently:
- `ResidualAttribute.unknown` (in records) carries a target expression
- `PartialAttribute.unknown` (in entity stores) carries only a type

## 4. Comparison with `getAttr` Delegation

`getAttr` has the same asymmetry:

```lean
-- Record: delegates to target
| .val (.record m) _ =>
  | some (.unknown tgt _) => .getAttr tgt a ty

-- Entity: delegates to self
| .val (.prim (.entityUID uid)) _ =>
  | .some (.unknown _) => .getAttr r a ty
```

But for `getAttr`, the delegation is *necessary* — we don't know the value, so we must defer. For `hasAttr`, the delegation is *conservative* — we could potentially resolve to `true` immediately (see Section 3a).

## 5. The `hasAttr` Soundness Obligation

The soundness proof for `hasAttr` (`partial_evaluate_is_sound_has_attr`) must show:

```
(x₁.hasAttr a bool_ty).evaluate req es).toOption =
  ((TPE.hasAttr (TPE.evaluate x₁ preq pes) a pes bool_ty).evaluate req es).toOption
```

This requires case-splitting on all three paths:

### Path A (record with unknown field):
- LHS: `Spec.hasAttr (.record concrete_r) a es = .ok (concrete_r.contains a)`
- RHS: `(.hasAttr tgt a ty).evaluate req es = Spec.hasAttr (tgt.evaluate req es) a es`
- Need: `tgt.evaluate req es = .ok container_val` and `Spec.hasAttr container_val a es = .ok (concrete_r.contains a)`
- The target evaluates to the entity, and `hasAttr` on the entity checks the concrete attribute map

### Path B (entity with unknown field):
- LHS: `Spec.hasAttr (.prim (.entityUID uid)) a es = .ok ((es.attrsOrEmpty uid).contains a)`
- RHS: `(.hasAttr r a ty).evaluate req es = Spec.hasAttr (r.evaluate req es) a es`
- Since `r = .val (.prim (.entityUID uid)) _`, `r.evaluate req es = .ok (.prim (.entityUID uid))`
- So RHS = `Spec.hasAttr (.prim (.entityUID uid)) a es` = LHS ✓

### Path B (entity with attrs = none):
- LHS: `Spec.hasAttr (.prim (.entityUID uid)) a es = .ok ((es.attrsOrEmpty uid).contains a)`
- RHS: same as above (`.hasAttr r a ty` with `r` = entity)
- Same reasoning ✓

### Path C (non-value receiver):
- Both sides produce the same residual structure, so the inductive hypothesis applies

## 6. The `hasAttr` on Records: A Missed Optimization

As noted in Section 3a, when `hasAttr` on a record finds `some (.unknown tgt _)`, the attribute key *is present* in the record's map. Since `toResidualValue` preserves all keys from the `PartialValue.record`, and the `PartialValue.record` was derived from a concrete record that has this key, the concrete answer is `true`.

The current code returns `.hasAttr tgt a ty` instead of `true`. This is:
- **Sound**: the residual will evaluate to `true`
- **Not tight**: it could be reduced immediately

If this were changed to return `true`, it would:
- Improve precision (fewer residuals)
- Simplify the soundness proof for this case (no need to reason about target evaluation)
- But require a new invariant: "if `m.find? a = some (.unknown _ _)`, then the concrete record has attribute `a`"

This invariant follows from the construction of `toResidualValue`, which maps every key in the `PartialValue.record` to a key in the `ResidualValue.record`. But it's not currently stated or proven.

**However**, there's a subtlety: the `cons_unknown_neq` constructor in `AttributesRefines` allows the partial record to have unknown entries for attributes that *don't exist* in the concrete record. If such an entry made it into a `ResidualValue.record`, then `m.find? a = some (.unknown _ _)` would NOT guarantee the concrete record has `a`.

So the optimization is only valid if we can prove that `toResidualValue` never introduces spurious keys. Looking at the code:

```lean
| .record m, .record rty => .record (m.mapKVsIntoValues₂ ...)
```

It maps over `m` (the `PartialValue.record`'s map), preserving exactly the same keys. So the keys in the `ResidualValue.record` are exactly the keys in the `PartialValue.record`. Whether those keys correspond to concrete attributes depends on how the `PartialValue.record` was constructed.

If the `PartialValue.record` came from `EntityData.asPartial`, all keys are concrete. If it came from a schema-derived partial entity with optional attributes, there could be keys for attributes that don't exist in the concrete entity. So the optimization is NOT universally safe — the current conservative approach is correct.

## 7. `hasAttr` with `none` (absent attribute)

When `m.find? a = none` (attribute not in the record/entity map):

- **Record**: returns `false` immediately
- **Entity with known attrs**: returns `false` immediately
- **Entity with unknown attrs** (`es.attrs uid = none`): returns `.hasAttr r a ty` (residual)

The `false` cases are sound because:
- For records: if the key isn't in the `ResidualValue.record` map, it wasn't in the `PartialValue.record` map, so it's not in the concrete record → `hasAttr` is `false`
- For entities with known attrs: if the key isn't in the partial attribute map, and the partial map refines the concrete map, then... **wait, this needs care**.

The refinement relation `AttributesRefines` allows the partial list to be *shorter* than the concrete list (via `cons_unknown_neq`, which can skip concrete attributes). So `attrs.find? a = none` in the partial map does NOT necessarily mean the concrete entity lacks attribute `a`.

But looking at the code more carefully, `es.attrs uid` returns `PartialAttributes = Option (Map Attr (PartialAttribute PartialValue))`. This is a `Map`, not a list — it's constructed from the entity data. If the entity data was loaded via `EntityData.asPartial`, every concrete attribute becomes a `present` entry. If it was loaded via a partial mechanism, unknown attributes get `unknown` entries.

The key question: can `attrs.find? a = none` when the concrete entity has attribute `a`?

If the partial entity was constructed with `EntityData.asPartial` (full loading), no — every attribute is present. If it was constructed with partial loading (some attributes unknown), then unknown attributes get `.unknown ty` entries, not absence. So `attrs.find? a = none` means the attribute genuinely doesn't exist in the partial map, which (given well-typed entities) means it doesn't exist in the concrete entity either.

**Invariant (Attribute absence soundness)**: If `(es.attrs uid).bind (·.find? a) = some none` (attribute map exists but attribute `a` is not in it), then the concrete entity either lacks attribute `a` or has it as an optional attribute that is absent. In either case, `Spec.hasAttr` returns `false`.

Actually, this is more nuanced. The partial attribute map should contain entries for all attributes that exist in the concrete entity. If an attribute exists concretely but is missing from the partial map, the refinement relation is violated. The `EntitiesRefine` definition requires `ValueRefines env (.record e₁.attrs) (.record attrs)`, which through `AttributesRefines` ensures every concrete attribute has a corresponding partial entry (either `present` or `unknown`).

So `attrs.find? a = none` → concrete entity lacks `a` → `hasAttr` returns `false` ✓.

## 8. `hasTag` Parallel

`hasTag` in the TPE evaluator:

```lean
def hasTag (uid : EntityUID) (tag : String) (es : PartialEntities) : Option Bool :=
  (es.tags uid).map (Map.contains · tag)
```

This is simpler than `hasAttr` because:
- Tags don't have the record/entity split — tags are always on entities
- `hasTag` returns `Option Bool`, not `Residual` — it either resolves or doesn't
- When tags are unknown (`es.tags uid = none`), it returns `none`, and the caller (`apply₂`) uses `someOrSelf` to produce a residual

There's no target delegation for `hasTag` — it's a binary operation, not an attribute access. The residual is `.binaryApp .hasTag uid tag ty`, which directly re-evaluates the `hasTag` operation.

**Invariant**: `hasTag` never interacts with the target mechanism. Unknown tag *values* (`.unknown ty` in the tag map) are handled by `getTag`, not `hasTag`. For `hasTag`, only the *presence* of the tag key matters, and `Map.contains` checks key presence regardless of whether the value is `present` or `unknown`.

Wait — let me re-check. `Map.contains` on a `PartialTags = Option (Map Tag (PartialAttribute PartialValue))` checks if the key exists in the map. If the tag exists with value `.unknown ty`, `Map.contains` returns `true`. This is correct: the tag exists, we just don't know its value.

**Invariant (hasTag on unknown values)**: `hasTag` returns `true` for tags with unknown values. This is sound because the tag key exists in the concrete entity (by refinement), so `Spec.hasTag` also returns `true`.

## 9. Summary of `hasAttr`/`hasTag` Invariants

| # | Invariant | Applies To |
|---|---|---|
| 1 | Record `hasAttr` with unknown field delegates to target, not self | `TPE.hasAttr` Path A |
| 2 | Entity `hasAttr` with unknown field delegates to self, not target | `TPE.hasAttr` Path B |
| 3 | Record delegation is conservative: concrete answer is always `true` | `TPE.hasAttr` Path A |
| 4 | Entity delegation is exact: residual evaluates to the concrete answer | `TPE.hasAttr` Path B |
| 5 | Absent attribute (`find? a = none`) implies concrete absence (by refinement) | `TPE.hasAttr` Paths A & B |
| 6 | `hasTag` never uses the target mechanism | `TPE.hasTag` |
| 7 | `hasTag` returns `true` for tags with unknown values | `TPE.hasTag` |
| 8 | `hasAttr` on entity with `attrs = none` produces residual (not `false`) | `TPE.hasAttr` Path B |
