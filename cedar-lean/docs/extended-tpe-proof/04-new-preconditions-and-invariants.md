# New Preconditions and Invariants in the Extended TPE

## 1. Introduction

The extended TPE introduces three major capabilities beyond a standard partial evaluator:

1. **Field-level partiality** — individual record/entity attributes can be known or unknown
2. **Batched entity loading** — entities are fetched incrementally across iterations
3. **Typed residuals with unknown targets** — `ResidualAttribute.unknown` stores a back-pointer to the expression that would compute the value

Each of these introduces new preconditions and invariants that the original TPE proofs did not need. This document analyzes each in depth.

---

## 2. Field-Level Partiality

### 2.1 The Refinement Relation

The central new precondition is `ValueRefines`, a mutually inductive relation with `AttributesRefines`:

```lean
inductive ValueRefines : TypeEnv → Value → PartialValue → Prop
  | prim : ValueRefines env (.prim p) (.prim p)
  | ext  : ValueRefines env (.ext e) (.ext e)
  | set  : ValueRefines env (.set vs) (.set vs)
  | record : AttributesRefines env a a' →
             ValueRefines env (.record (.mk a)) (.record (.mk a'))

inductive AttributesRefines : TypeEnv → List (Attr × Value) → List (Attr × PartialAttribute PartialValue) → Prop
  | nil : AttributesRefines env [] []
  | cons_present : ValueRefines env v v' → AttributesRefines env t t' →
                   AttributesRefines env ((a, v) :: t) ((a, .present v') :: t')
  | cons_unknown : InstanceOfType env v ty → AttributesRefines env t t' →
                   AttributesRefines env ((a, v) :: t) ((a, .unknown ty) :: t')
  | cons_unknown_neq : a ≠ a' → AttributesRefines env ((a, v) :: t) t' →
                       AttributesRefines env ((a, v) :: t) ((a', .unknown ty) :: t')
```

This is fundamentally different from a standard partial evaluator where values are either fully known or fully unknown. Here, a single record can have a mix:

```
Concrete:  { "name": "Alice", "age": 30, "role": "admin" }
Partial:   { "name": present "Alice", "age": unknown Int, "role": present "admin" }
```

#### Key invariant: Every `present` field matches the concrete value; every `unknown` field has a concrete value of the declared type.

The `cons_unknown_neq` constructor handles a subtle case: the partial record may contain `unknown` entries for attributes that don't appear in the concrete record at all. This happens because the partial record is derived from a schema that may declare optional attributes. The `a ≠ a'` guard ensures we don't confuse this with the case where the attribute exists but is unknown.

### 2.2 Entity-Level Refinement

`EntitiesRefine` lifts field-level partiality to the entity store:

```lean
def EntitiesRefine env es pes : Prop :=
  ∀ a e₂, pes.find? a = some e₂ → ∃ e₁, es.find? a = some e₁ ∧
    PartialIsValid (fun attrs => ValueRefines env (.record e₁.attrs) (.record attrs)) e₂.attrs ∧
    PartialIsValid (· = e₁.ancestors) e₂.ancestors ∧
    PartialIsValid (fun tags => ValueRefines env (.record e₁.tags) (.record tags)) e₂.tags
```

Three independent `PartialIsValid` conditions — attrs, ancestors, and tags can each be independently `none` (entirely unknown) or `some` (partially known). This is a 3-dimensional partiality space per entity.

#### Key invariant: If the partial store says an entity exists, the concrete store must also have it, and each known component must refine the concrete component.

Note the asymmetry: the partial store can be *smaller* than the concrete store (entities not yet loaded are simply absent from `pes`). But every entity *in* `pes` must correspond to a concrete entity.

### 2.3 The `PartialIsValid` Wrapper

```lean
inductive PartialIsValid {α} : (α → Prop) → Option α → Prop
  | some : p x → PartialIsValid p (.some x)
  | none : PartialIsValid p .none
```

This is the "option-lifted" predicate: if the value is present, the predicate holds; if absent, anything goes. It appears throughout the refinement definitions and captures the idea that "unknown" imposes no constraints.

### 2.4 Impact on Proofs

The old proofs (visible in commented-out sections of `GetAttr.lean`, `Binary.lean`) assumed a simpler refinement where entity attributes were either fully known maps or entirely absent. The new proofs must:

1. **Case-split on `PartialAttribute`**: Every attribute access must consider `present` vs `unknown`
2. **Thread `ValueRefines` through records**: When `getAttr` resolves a `present` field from a partial entity, the proof must show the resolved value matches the concrete value via `ValueRefines`
3. **Handle the `unknown` → residual delegation**: When `getAttr` encounters an `unknown` field, it produces a residual. The proof must show this residual evaluates correctly against the concrete value

The `cons_unknown_neq` case is particularly tricky for proofs — it means the partial attribute list can have entries that don't correspond to any concrete attribute, requiring careful alignment of the two lists.

---

## 3. The `ResidualAttribute.unknown` Target Invariant

### 3.1 The Target Expression

When a `PartialValue.record` is converted to a `ResidualValue` via `PartialValue.toResidualValue`, unknown fields store a *target* `Residual`:

```lean
def PartialValue.toResidualValue (target : Residual) : PartialValue → CedarType → ResidualValue
  | .record m, .record rty => .record (m.mapKVsIntoValues₂ λ kv =>
    match kv with
    | ⟨(a, .present pv), _⟩ =>
      let aty := Qualified.getType <$> rty.find? a |>.getD (.bool .anyBool)
      .present (PartialValue.toResidualValue (.getAttr target a (.record rty)) pv aty)
    | ⟨(_, .unknown ty), _⟩ => .unknown target ty)
```

The target is the expression that, when fully evaluated, would yield the entity/record containing this field. For a top-level entity attribute:

```
target = .val (.prim (.entityUID alice)) (.entity User)
```

For a nested record field:

```
target = .getAttr (.val (.prim (.entityUID eve)) (.entity User)) "address" outerRecTy
```

### 3.2 The Target Correctness Invariant

**Invariant**: For every `ResidualAttribute.unknown target ty` in a residual, evaluating `(.getAttr target attr ty)` against concrete request/entities must produce the same result as looking up the attribute in the concrete entity/record.

This is not stated as a standalone theorem in the codebase but is implicitly maintained by the construction in `PartialValue.toResidualValue` and relied upon by the soundness proof for `getAttr` and `hasAttr`.

Formally, if we have:
- `ResidualAttribute.unknown target ty` at attribute `a` in a `ResidualValue.record`
- The record was derived from entity `uid`'s attribute data
- The concrete entity has `uid.attrs.find? a = some v`

Then: `(.getAttr target a ty).evaluate req es = .ok v`

### 3.3 Target Threading Through Nesting

The target changes as we recurse into nested records:

```
Entity eve:
  info: present {
    address: present { city: present "Seattle", zip: unknown String }
    score: unknown Int
  }

After toResidualValue with target = eveVal:
  info → ResidualValue.record {
    address → .present (ResidualValue.record {
      city → .present (.prim (.string "Seattle"))
      zip  → .unknown (.getAttr eveVal "address" outerRecTy) .string
                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                       target for inner record = getAttr on outer target
    })
    score → .unknown eveVal .int
                     ^^^^^^
                     target for outer record = entity itself
  }
```

**Invariant**: The target at nesting depth `n` is a chain of `n` `getAttr` operations back to the entity. Each link in the chain must evaluate correctly.

### 3.4 Impact on Proofs

The target invariant creates a new proof obligation for every case where `getAttr`/`hasAttr` encounters a `ResidualAttribute.unknown`:

1. The soundness proof for `getAttr` on a record with unknown fields must show that delegating to the target expression is semantically equivalent to the concrete attribute lookup
2. The well-typedness proof must show the target expression is well-typed (so the delegated residual is well-typed)
3. The `ResidualValue.evaluate` proof must handle the record case where `present` fields are evaluated recursively and `unknown` fields delegate to `(.getAttr target attr ty).evaluate`

This is the primary reason the `ResidualValue.evaluate` function exists as a separate mutual recursive function — it needs to handle the `unknown` → `getAttr` delegation.

---

## 4. Batched Entity Loading

### 4.1 The Entity Loader Contract

```lean
abbrev EntityLoader.WellBehaved (store : Entities) (loader : EntityLoader) : Prop :=
  ∀ s, s ⊆ (loader s).keys ∧
       EntitiesRefine store ((loader s).mapOnValues MaybeEntityData.asPartial)
```

Two conditions:

1. **Completeness**: `s ⊆ (loader s).keys` — the loader returns an entry for every requested UID (the entry may be `none` if the entity doesn't exist)
2. **Refinement**: The loaded data refines the backing store

### 4.2 The Missing Entity Equivalence

```lean
def MaybeEntityData.asPartial : MaybeEntityData → PartialEntityData
  | none => { attrs := some Map.empty, ancestors := some Set.empty, tags := some Map.empty }
  | some d => d.asPartial
```

**Key design decision**: A missing entity (loader returns `none`) is converted to a `PartialEntityData` with *empty* (not unknown) attrs/ancestors/tags. This is sound because:

1. Cedar has no `entityExists` predicate — there's no way to distinguish a missing entity from an empty one
2. `getAttr` on a missing entity returns an error (attribute not found) — same as on an empty entity
3. `in` (membership) on a missing entity returns `false` — same as on an entity with empty ancestors
4. `hasTag`/`getTag` on a missing entity behaves the same as on an entity with empty tags

**Invariant**: `MaybeEntityData.asPartial none` must be semantically equivalent to the behavior of a non-existent entity in the concrete evaluator.

This is stated in the code comment:
> a missing entity behaves the same way as a concrete entity with empty attrs, ancestors, and tags.

But it is not formally proven as a standalone theorem. The proof relies on this equivalence holding for each operation (`getAttr`, `hasAttr`, `in`, `hasTag`, `getTag`) individually.

### 4.3 Store Monotonicity

The batched evaluation loop accumulates entities:

```lean
let newStore := newEntities ++ current_store
```

Using map append (`++`), where `newEntities` takes priority over `current_store` for duplicate keys.

**Invariant**: The entity store grows monotonically — entities loaded in earlier iterations are never removed.

The proof uses `entities_refine_append`:

```lean
theorem entities_refine_append (es : Entities) (m1 m2 : PartialEntities) :
  EntitiesRefine es m1 → EntitiesRefine es m2 → EntitiesRefine es (m2 ++ m1)
```

This works because:
- Both `m1` and `m2` individually refine `es`
- `m2 ++ m1` uses `m2`'s entry when both have the same key
- Since both refine `es`, either entry is valid

**Subtle point**: The append order matters. `newEntities ++ current_store` means newly loaded entities override existing ones. This is safe because both refine the same backing store, but it means an entity's partial data can *change* between iterations (e.g., from `attrs = none` to `attrs = some {...}`). The refinement relation is preserved because both the old and new data refine the concrete entity.

### 4.4 The Convergence Question

The loop terminates after at most `n` iterations (the `Nat` fuel parameter). But does it *converge* — i.e., does it eventually reach a fixed point?

The completeness condition (`s ⊆ (loader s).keys`) is described in the code as:
> required for convergence of batched evaluation, which has not been proven. It is unused in the code base at the moment.

The current soundness proof does NOT prove convergence. It proves that *whatever* the loop produces after `n` iterations, evaluating that residual against concrete data gives the same result as direct evaluation. This is a weaker but still useful property.

**Open question**: Can we prove that if the expression references a finite set of entities, the loop converges in a bounded number of iterations?

### 4.5 Well-Typedness Across Iterations

Each iteration of the loop must preserve well-typedness:

```lean
have h₈ := partial_eval_preserves_well_typed h₃ h₆ h₁
-- h₁ : Residual.WellTyped env x
-- h₆ : RequestAndEntitiesRefine req es req.asPartialRequest newStore
-- Result: Residual.WellTyped env (TPE.evaluate x req.asPartialRequest newStore)
```

**Invariant**: If the residual entering an iteration is well-typed, the residual leaving the iteration is well-typed.

This is critical because the soundness lemma (`partial_evaluate_is_sound`) requires well-typedness as a precondition. Without this invariant, the inductive argument over iterations would break.

### 4.6 The `allLiteralUIDs` Discovery Mechanism

```lean
let toLoad := residual.allLiteralUIDs.filter (λ uid => (store.find? uid).isNone)
```

The loop discovers which entities to load by scanning the residual for literal `EntityUID` values. This is a syntactic scan, not a semantic one.

**Limitation**: If an entity UID is computed (e.g., via `getAttr` returning an entity reference), it won't appear as a literal in the residual. The loop can only discover UIDs that are syntactically present.

**Invariant**: `allLiteralUIDs` must be a sound overapproximation — it must find all UIDs that could affect evaluation. It does NOT need to be complete (finding all UIDs that *will* affect evaluation), because the loop has a fuel parameter.

The current implementation traverses the entire residual tree, collecting UIDs from:
- `ResidualValue.prim (.entityUID uid)` — literal entity values
- Recursively through all sub-expressions and record values

---

## 5. Interaction Between the Three Extensions

### 5.1 Field-Level Partiality × Batched Loading

When the loader returns entity data, it's converted to `PartialEntityData` where all fields are `present` (via `EntityData.asPartial`). But the *existing* store may have entries with `attrs = none` (entirely unknown). After `newEntities ++ current_store`, the new `present` data overrides the old `none`.

**Invariant**: The refinement relation is preserved across this transition because:
- The old `none` trivially satisfies `PartialIsValid` (anything goes)
- The new `some (present ...)` satisfies `PartialIsValid` because the loader is well-behaved

### 5.2 Unknown Targets × Batched Loading

When an entity's attributes are unknown (`attrs = none`), `getAttr` produces a residual like `.getAttr (.val uid _) "name" .string`. In the next iteration, if the entity is loaded, this residual can be resolved.

**Invariant**: The target expression in `ResidualAttribute.unknown` must remain valid across iterations. Since targets point to entity UIDs (which are immutable) or chains of `getAttr` on entity UIDs, and entity data only grows more concrete across iterations, this is preserved.

### 5.3 Field-Level Partiality × Unknown Targets

When a loaded entity has a record-valued attribute with some unknown fields, `PartialValue.toResidualValue` creates `ResidualAttribute.unknown` entries with targets pointing back to the entity. In the next iteration, if the entity is re-loaded with more complete data, the targets still point to the same entity UID, so they remain valid.

**Invariant**: Target validity is independent of the partial store's state — targets are expressions over entity UIDs, not over the partial store.

---

## 6. Summary of New Preconditions

| # | Precondition | Where Established | Where Used |
|---|---|---|---|
| 1 | `ValueRefines env v pv` for every present partial value | `isValidAndConsistent` → `consistent_checks_ensure_refinement` | Soundness of `getAttr`, `hasAttr`, `apply₂` |
| 2 | `InstanceOfType env v ty` for every unknown partial attribute | `isValidAndConsistent` (via `entitiesIsValid`) | Soundness of `getAttr` delegation |
| 3 | `MaybeEntityData.asPartial none ≈ empty entity` | By construction (definitional) | Batched evaluation soundness |
| 4 | `EntityLoader.WellBehaved` (completeness + refinement) | Assumed as precondition | `batched_eval_eq_evaluate` |
| 5 | Store monotonicity (`newEntities ++ current_store` refines `es`) | `entities_refine_append` | Loop induction |
| 6 | Target expression validity | By construction in `toResidualValue` | `ResidualValue.evaluate` soundness |
| 7 | Well-typedness preservation across iterations | `partial_eval_preserves_well_typed` | Loop induction |

## 7. Summary of New Invariants

| # | Invariant | Maintained By | Broken If |
|---|---|---|---|
| 1 | Refinement preserved across partial evaluation | `partial_evaluate_is_sound` | Smart constructors don't preserve semantics |
| 2 | Well-typedness preserved across partial evaluation | `partial_eval_preserves_well_typed` | Type annotations are wrong |
| 3 | `typeOf` preserved across partial evaluation | `partial_eval_preserves_typeof` | Smart constructors change the type tag |
| 4 | Entity store only grows | Map append semantics | If entities were removed between iterations |
| 5 | Target expressions evaluate to the containing entity/record | `toResidualValue` construction | If targets pointed to stale expressions |
| 6 | `errorFree` correctly identifies non-erroring residuals | `error_free_evaluate_ok` | If `errorFree` was too optimistic |
| 7 | Missing entities ≡ empty entities | Cedar language design (no `entityExists`) | If Cedar added entity existence checks |
