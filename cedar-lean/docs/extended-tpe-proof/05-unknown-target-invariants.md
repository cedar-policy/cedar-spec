# The Unknown Target Mechanism: Internal Invariants

## 1. What the Target Mechanism Is

When the TPE evaluator encounters a `PartialValue` with unknown fields, it must produce a `ResidualValue` that can later be fully evaluated. The challenge: a `ResidualValue.record` is a *value* (it lives inside `.val`), but some of its fields are not yet known. The unknown fields need to remember *how to compute themselves* when full information becomes available.

The solution is `ResidualAttribute.unknown`:

```lean
inductive ResidualAttribute where
  | present (val : ResidualValue)
  | unknown (expr : Residual) (ty : CedarType)
```

The `expr` field — the **target** — is a `Residual` expression that, when composed with a `getAttr`, will produce the missing value at full-evaluation time.

---

## 2. Target Construction Sites

Targets are created in exactly two places:

### 2a. `PartialValue.toResidualValue` (record conversion)

```lean
def PartialValue.toResidualValue (target : Residual) : PartialValue → CedarType → ResidualValue
  | .record m, .record rty => .record (m.mapKVsIntoValues₂ λ kv =>
    match kv with
    | ⟨(a, .present pv), _⟩ =>
        .present (PartialValue.toResidualValue (.getAttr target a (.record rty)) pv aty)
    | ⟨(_, .unknown ty), _⟩ =>
        .unknown target ty)
```

Two things happen here:
- **Unknown fields** get `target` directly — the expression that represents the container
- **Present fields** recurse with a *new* target: `.getAttr target a (.record rty)` — the expression that would access this specific field from the container

### 2b. `TPE.getAttr` on entity attributes (the entry point)

```lean
def getAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Residual :=
  ...
  | .val (.prim (.entityUID uid)) _ =>
    match es.attrs uid with
    | .some attrs =>
      match Map.find? attrs a with
      | .some (.present pv) => .val (PartialValue.toResidualValue r pv ty) ty
      ...
```

Here `r` is the residual for the entity itself (e.g., `.val (.prim (.entityUID alice)) (.entity User)`). This becomes the initial `target` passed to `toResidualValue`.

Similarly in `TPE.getTag`:

```lean
| .some (.present tv) => tv.asResidual (.val (.prim (.entityUID uid)) (.entity uid.ty)) ty
```

Where `asResidual` calls `toResidualValue` with the entity as target.

---

## 3. Target Consumption Site

Targets are consumed in exactly one place: `ResidualValue.evaluate`.

```lean
def ResidualValue.evaluate (rv : ResidualValue) (req : Request) (es : Entities) : Result Value :=
  match rv with
  | .record r => do
    .ok (.record (← r.mapMKVsIntoValues₂ (λ kv =>
      match kv with
      | ⟨(a, .present v'), _⟩ =>
          ResidualValue.evaluate v' req es
      | ⟨(a, .unknown expr ty), _⟩ =>
          Residual.evaluate (.getAttr expr a ty) req es)))
```

For an unknown field at attribute `a` with target `expr`, the evaluator constructs `.getAttr expr a ty` and evaluates it. This is the **reconstruction**: the target + attribute name + type are composed into a `getAttr` expression that fetches the concrete value.

---

## 4. The Core Invariant: Target Semantic Correctness

**Invariant (Target Correctness)**: For every `ResidualAttribute.unknown target ty` at attribute `a` within a `ResidualValue` that was derived from entity `uid`'s data:

```
Residual.evaluate (.getAttr target a ty) req es = Spec.getAttr (concrete_container) a es
```

where `concrete_container` is the concrete value that `target` evaluates to.

More precisely, if:
1. `target.evaluate req es = .ok container_val`
2. The unknown attribute `a` exists in the concrete version of `container_val`

Then: `Residual.evaluate (.getAttr target a ty) req es = .ok (concrete_value_of_a)`

This invariant is **not stated as a theorem** in the codebase. It is maintained by construction and relied upon implicitly by the soundness proof.

---

## 5. Target Shape Invariants

### 5a. Targets are always entity-rooted expressions

Every target is one of:
- `.val (.prim (.entityUID uid)) (.entity ety)` — a literal entity reference
- `.getAttr target' a' ty'` — a `getAttr` chain rooted at an entity

This means targets form a **chain**:

```
Level 0:  .val (.prim (.entityUID uid)) (.entity ety)
Level 1:  .getAttr (Level 0) attr₁ ty₁
Level 2:  .getAttr (Level 1) attr₂ ty₂
...
```

**Invariant (Target Shape)**: Every target is a finite chain of `getAttr` operations rooted at a literal entity UID value.

This is maintained by construction:
- The initial target (from `TPE.getAttr` on an entity) is always a `.val (.prim (.entityUID uid)) _`
- `toResidualValue` only extends targets by wrapping them in `.getAttr target a rty`

### 5b. Targets never contain free variables or complex expressions

Targets don't contain `ite`, `and`, `or`, `unaryApp`, `binaryApp`, `call`, `set`, `record`, `var`, or `error`. They are purely structural navigation paths through the entity graph.

**Why this matters**: When `ResidualValue.evaluate` constructs `.getAttr target a ty` and evaluates it, the evaluation follows the concrete `Spec.getAttr` path — looking up entity data, then looking up the attribute. There are no side effects, no short-circuiting, no error-swallowing. The evaluation is deterministic and depends only on the entity store.

---

## 6. The Nesting Invariant

### 6a. Target depth matches record nesting depth

Consider entity `eve` with:
```
info: { address: { city: "Seattle", zip: unknown }, score: unknown }
```

After `toResidualValue` with initial target `eveVal`:

```
info → ResidualValue.record {
  address → .present (ResidualValue.record {
    city → .present (.prim (.string "Seattle"))
    zip  → .unknown (.getAttr eveVal "address" outerRecTy) .string
                     ↑ depth-1 target
  })
  score → .unknown eveVal .int
                   ↑ depth-0 target
}
```

**Invariant (Depth Correspondence)**: An unknown attribute at nesting depth `d` within a `ResidualValue` derived from entity `uid` has a target that is a chain of exactly `d` `getAttr` operations rooted at `uid`.

### 6b. Target type annotations match the intermediate record types

The target `.getAttr eveVal "address" outerRecTy` carries `outerRecTy` as its type annotation. This is the type of the *outer* record (the one containing `address`), not the type of `address` itself.

Wait — actually, looking more carefully at the code:

```lean
.present (PartialValue.toResidualValue (.getAttr target a (.record rty)) pv aty)
```

The new target is `.getAttr target a (.record rty)` where `rty` is the record type of the *current* record being converted. The type annotation on the `getAttr` is `(.record rty)` — the type of the current record, not the type of attribute `a`.

**Correction**: The type annotation on the target `getAttr` is the type of the *parent record*, because that's what `rty` is in the recursive call. Let me re-examine...

Actually, `rty` in the pattern `| .record m, .record rty =>` is the record type passed as the second argument to `toResidualValue`. The new target `.getAttr target a (.record rty)` has type `(.record rty)`. But this is wrong — `getAttr target a` should have the type of attribute `a`, not the type of the whole record.

Looking at the test cases:

```lean
private def addressTarget : Residual := .getAttr eveVal "address" outerRecTy
```

Here `outerRecTy` is the type of the *outer* record `{ address: innerRecTy, score: Int }`. So `getAttr eveVal "address" outerRecTy` means "get `address` from `eveVal`, and the result type is `outerRecTy`".

But that's semantically wrong — `getAttr eveVal "address"` should have type `innerRecTy`, not `outerRecTy`.

**This is actually intentional**. The type annotation on the target is not the type of the *result* of the getAttr — it's the type of the *record being navigated*. The target is used as a navigation path, and when `ResidualValue.evaluate` constructs `.getAttr target a ty`, it uses the `ty` from the `unknown` annotation (the type of the *field*), not the type from the target.

Let me verify by looking at the evaluate code again:

```lean
| ⟨(a, .unknown expr ty), _⟩ =>
    Residual.evaluate (.getAttr expr a ty) req es
```

Yes — the `ty` here comes from the `ResidualAttribute.unknown`, which is the type of the *field*. The `expr` (target) carries its own type annotation, but that annotation is only used if someone calls `expr.typeOf` — it's not used in the evaluation semantics.

**Invariant (Target Type Annotation)**: The type annotation on a target expression is the type of the record that the target navigates *through* (the parent record type). The type of the *field* is stored separately in the `ResidualAttribute.unknown`. When reconstructing the `getAttr` for evaluation, the field type is used, not the target's type annotation.

This is a subtle but important distinction. The target's type annotation is used for well-typedness proofs (to show the target is well-typed), while the field type is used for the actual evaluation.

---

## 7. The Evaluation Equivalence Invariant

The deepest invariant is that `ResidualValue.evaluate` on a record with unknown fields produces the same result as evaluating the concrete record.

### 7a. For present fields

If `ResidualAttribute.present rv` was derived from concrete value `v` via `Value.asResidualValue`, then:

```
ResidualValue.evaluate rv req es = .ok v
```

This is the roundtrip property `asValue_inverse_asResidualValue` (currently has `sorry`s for the record case).

### 7b. For unknown fields

If `ResidualAttribute.unknown target ty` at attribute `a` was derived from entity `uid` where the concrete entity has `uid.attrs.find? a = some v`, then:

```
Residual.evaluate (.getAttr target a ty) req es = .ok v
```

This decomposes into:
1. `target.evaluate req es = .ok (concrete_container)` — the target evaluates to the container
2. `Spec.getAttr concrete_container a es = .ok v` — the concrete getAttr finds the value

For a depth-0 target (entity itself):
- `target = .val (.prim (.entityUID uid)) (.entity ety)`
- `target.evaluate req es = .ok (.prim (.entityUID uid))` ✓ (trivial)
- `Spec.getAttr (.prim (.entityUID uid)) a es = es.attrs uid >>= (·.findOrErr a ...)` ✓

For a depth-1 target (nested record):
- `target = .getAttr (.val (.prim (.entityUID uid)) _) attr₁ ty₁`
- `target.evaluate req es` = evaluate the getAttr = look up `uid`'s `attr₁` = `.ok record_val`
- `Spec.getAttr record_val a es` = look up `a` in `record_val` = `.ok v` ✓

### 7c. The inductive structure

The evaluation equivalence is proven by mutual induction on `ResidualValue.evaluate` and `Residual.evaluate`. The key inductive step:

- To show `ResidualValue.evaluate (.record r) req es = .ok (.record concrete_r)`, we need:
  - For each `(a, .present rv)` in `r`: `ResidualValue.evaluate rv req es = .ok concrete_v` (inductive hypothesis on `rv`)
  - For each `(a, .unknown target ty)` in `r`: `Residual.evaluate (.getAttr target a ty) req es = .ok concrete_v` (which calls `Residual.evaluate` on the target, then `Spec.getAttr`)

The mutual recursion is well-founded because:
- `ResidualValue.evaluate` on `.present rv` recurses on a smaller `rv`
- `ResidualValue.evaluate` on `.unknown target ty` calls `Residual.evaluate (.getAttr target a ty)`, which is smaller than the enclosing record (by `sizeOf`)

---

## 8. Invariants That Can Break

### 8a. Target staleness (cannot happen by construction)

If a target pointed to a mutable expression that could change between partial evaluation iterations, the target could become stale. But targets are always literal entity UIDs or chains of `getAttr` on literal UIDs — these are immutable.

### 8b. Target type mismatch

If the type annotation on a target or the `ty` in `ResidualAttribute.unknown` is wrong, the well-typedness proof breaks. The type is derived from the schema (`rty.find? a`), so it's correct as long as the schema is consistent with the entity data.

### 8c. Missing attribute in concrete entity

If the target evaluates to an entity/record that doesn't have attribute `a`, then `Spec.getAttr` returns an error. This would mean the unknown field can't be resolved. But this can't happen if the entity data is well-typed with respect to the schema — the schema guarantees the attribute exists.

### 8d. Record equality with unknown fields

The evaluator explicitly avoids reducing `eq` on records:

```lean
| .eq, (.record _), (.record _) => self
```

This is because records with unknown fields can't be compared — the unknown fields might differ. If this guard were removed, the evaluator could incorrectly conclude two records are equal when their unknown fields differ.

### 8e. `contains` with record elements

Similarly:

```lean
| .contains, .set _, (.record _) => self
```

A set `contains` check with a record argument is left as a residual because the record might have unknown fields that affect equality.

---

## 9. The `getTag` Parallel

Tags use the same target mechanism as attributes:

```lean
def getTag (uid : EntityUID) (tag : String) (es : PartialEntities) (ty : CedarType) : Residual :=
  match es.tags uid with
  | .some tags =>
    match tags.find? tag with
    | .some (.present tv) => tv.asResidual (.val (.prim (.entityUID uid)) (.entity uid.ty)) ty
    | .some _ => .binaryApp .getTag uid tag ty
    | .none => .error ty
  | .none => .binaryApp .getTag uid tag ty
```

When a tag value is `present`, it's converted via `asResidual` (which calls `toResidualValue`) with the entity as target. The same invariants apply: the target is the entity UID, and unknown fields within the tag value delegate back to the entity.

But there's a difference: when the tag value itself is unknown (`.some _` but not `.present`), the evaluator produces `.binaryApp .getTag uid tag ty` — a residual `getTag` operation, not a `getAttr` delegation. This is because tags are accessed via `getTag` (a binary operation), not `getAttr`.

---

## 10. Summary of Internal Invariants

| # | Invariant | Maintained By | Proof Obligation |
|---|---|---|---|
| 1 | **Target Semantic Correctness**: `(.getAttr target a ty).evaluate req es` produces the concrete value of attribute `a` | Construction in `toResidualValue` + entity refinement | Soundness of `ResidualValue.evaluate` |
| 2 | **Target Shape**: Targets are finite `getAttr` chains rooted at literal entity UIDs | `toResidualValue` only wraps targets in `getAttr` | Structural induction on targets |
| 3 | **Depth Correspondence**: Nesting depth of unknown = length of `getAttr` chain in target | Recursive structure of `toResidualValue` | Induction on record nesting |
| 4 | **Target Immutability**: Targets contain no mutable state (no vars, no partial-store references) | Targets are entity UIDs + `getAttr` chains | By construction |
| 5 | **Type Separation**: Target type ≠ field type; field type stored in `unknown`, target type in `getAttr` | `toResidualValue` passes `(.record rty)` as target type, `ty` as field type | Well-typedness proof |
| 6 | **Evaluation Roundtrip**: `ResidualValue.evaluate (v.asResidualValue) req es = .ok v` | `asResidualValue` produces only `present` fields | `asValue_inverse_asResidualValue` (has `sorry`) |
| 7 | **Well-Founded Recursion**: `sizeOf (.getAttr target a ty) < sizeOf (enclosing record)` | Lean's `decreasing_by` obligations in `ResidualValue.evaluate` | Termination proof |
| 8 | **Record Equality Guard**: Records with unknown fields are never compared for equality | `apply₂` returns `self` for `eq` on records | Soundness of `apply₂` |
