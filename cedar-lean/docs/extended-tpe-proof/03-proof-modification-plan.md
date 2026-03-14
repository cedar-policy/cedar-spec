# Proof Modification Plan

## Overview

This document catalogs the current state of the proofs, identifies all `sorry`s and incomplete areas, and outlines the modifications needed to complete the correctness proof for the extended TPE algorithm.

## Current Proof Status

### Proof Architecture

```
Cedar/Thm/TPE.lean                    ← Top-level authorization theorems
├── Cedar/Thm/TPE/Authorizer.lean     ← Reauthorization & policy set theorems
├── Cedar/Thm/TPE/Policy.lean         ← Single-policy soundness
├── Cedar/Thm/TPE/Soundness.lean      ← Expression-level soundness (main lemma)
│   └── Cedar/Thm/TPE/Soundness/      ← Per-constructor soundness lemmas
│       ├── Basic.lean, Var.lean, And.lean, Or.lean, IfThenElse.lean
│       ├── Unary.lean, Binary.lean
│       ├── HasAttr.lean, GetAttr.lean
│       ├── Set.lean, Record.lean, Call.lean
├── Cedar/Thm/TPE/WellTyped.lean      ← Type preservation (main theorem)
│   └── Cedar/Thm/TPE/WellTyped/      ← Per-constructor type preservation
├── Cedar/Thm/TPE/PreservesTypeOf.lean ← typeOf preservation
├── Cedar/Thm/TPE/Conversion.lean     ← TypedExpr ↔ Residual equivalence
├── Cedar/Thm/TPE/ErrorFree.lean      ← Error-free evaluation
├── Cedar/Thm/TPE/Input.lean          ← Refinement definitions & lemmas
├── Cedar/Thm/TPE/Residual.lean       ← Residual utility lemmas
├── Cedar/Thm/BatchedEvaluator.lean   ← Batched evaluation soundness
```

### Completed Proofs (✅)

| Theorem | File | Status |
|---|---|---|
| `partial_evaluate_is_sound` (main lemma) | `Soundness.lean` | ✅ Complete (dispatches to per-constructor lemmas) |
| `partial_eval_preserves_well_typed` | `WellTyped.lean` | ✅ Complete |
| `batched_eval_loop_eq_evaluate` | `BatchedEvaluator.lean` | ✅ Complete |
| `batched_eval_eq_evaluate` | `BatchedEvaluator.lean` | ✅ Complete |
| `reauthorize_is_sound` | `TPE.lean` | ✅ Complete |
| `partial_authorize_decision_is_sound` | `TPE.lean` | ✅ Complete (modulo sub-lemma sorrys) |
| `reauthorize_satisfied_policies_equiv` | `Authorizer.lean` | ✅ Complete (modulo sub-lemma sorrys) |
| `reauthorize_error_policies_equiv` | `Authorizer.lean` | ✅ Complete |
| `error_free_spec` | `ErrorFree.lean` | ✅ Complete |
| `Residual.error_free_spec` | `ErrorFree.lean` | ✅ Complete |

### Proofs with `sorry` (⚠️)

The `sorry`s cluster around a single root cause: the introduction of `ResidualValue` as a separate type from `Value`, and the fact that `Residual.evaluate` for the `.val` case now goes through `ResidualValue.evaluate` instead of directly returning a value.

---

## Catalog of `sorry`s

### Category 1: `ResidualValue.evaluate` for `.val` case

**Root cause**: `Residual.evaluate (.val v ty)` now calls `ResidualValue.evaluate v req es` instead of directly returning `v`. Many proofs assumed the old behavior.

#### 1a. `conversion_preserves_evaluation` — lit case
**File**: `Cedar/Thm/TPE/Conversion.lean`
**Location**: `case lit p ty`
```lean
| lit p ty =>
    sorry -- Residual.evaluate changed: val case now goes through ResidualValue.evaluate
```
**Fix**: Need to show `ResidualValue.evaluate (.prim p) req es = .ok (.prim p)`, which follows directly from the definition. The `residual_value_prim_evaluates` simp lemma in `Residual.lean` already covers this — the sorry likely predates that lemma or the proof needs a `simp` update.

#### 1b. `error_free_evaluate_ok` — val case
**File**: `Cedar/Thm/TPE/ErrorFree.lean`
**Location**: `case val`
```lean
case val => sorry -- Residual.evaluate for val now goes through ResidualValue.evaluate
```
**Fix**: Need a general lemma `ResidualValue.evaluate_ok_of_well_typed` showing that evaluating a well-typed `ResidualValue` succeeds. For primitive/ext/set cases this is trivial. The record case requires showing that all `present` fields evaluate successfully and all `unknown` fields' target expressions evaluate successfully.

#### 1c. `partial_authorize_allow_determining_policies_is_sound` — val evaluate
**File**: `Cedar/Thm/TPE.lean`
```lean
sorry -- Residual.evaluate for .val now goes through ResidualValue.evaluate
```
**Fix**: Same pattern — need `Residual.evaluate (.val (.prim (.bool true)) ty) req es = .ok true`.

#### 1d. `partial_authorize_satisfied_forbid_is_determining` — val evaluate
**File**: `Cedar/Thm/TPE.lean`
```lean
sorry -- Residual.evaluate for .val now goes through ResidualValue.evaluate
```
**Fix**: Same as 1c.

### Category 2: `ResidualValue ↔ Value` roundtrip

#### 2a. `asValue_inverse_asResidualValue` — record case
**File**: `Cedar/Thm/TPE/Residual.lean`
```lean
theorem asValue_inverse_asResidualValue (v : Value) :
  v.asResidualValue.asValue = some v
```
Two `sorry`s in the record case. Need to show that `mapMOnValues` over `present ∘ asResidualValue` reconstructs the original map.

**Fix**: Prove by induction on the record's attribute list. Each field goes through `Value.asResidualValue` → `ResidualAttribute.present` → `ResidualAttribute.asValue` → `ResidualValue.asValue` → back to the original value (by inductive hypothesis).

#### 2b. `asValue_some` — val case
**File**: `Cedar/Thm/TPE/Residual.lean`
```lean
exact ⟨ty, by sorry⟩ -- need: ResidualValue.asValue rv = some v → rv = v.asResidualValue
```
**Fix**: Need a lemma `ResidualValue.asValue_eq_some_implies`: if `rv.asValue = some v` then `rv = v.asResidualValue`. Prove by cases on `rv`.

#### 2c. `asValue_evaluate_val`
**File**: `Cedar/Thm/TPE/Residual.lean`
```lean
sorry -- need: ResidualValue.evaluate (v.asResidualValue) req es = .ok v
```
**Fix**: Prove `ResidualValue.evaluate_asResidualValue`: evaluating `v.asResidualValue` always returns `v`. By induction on `v`; the record case requires showing that all `present` fields roundtrip.

### Category 3: `InstanceOfType.toResidualValueType` — record case

**File**: `Cedar/Thm/WellTyped/Residual/Definition.lean`
```lean
| instance_of_record r rty h₁ h₂ h₃ =>
    sorry -- TODO: record case needs to bridge Map Attr Value → List (Attr × ResidualAttribute)
```
**Fix**: Need to show that `Value.asResidualValue` on a well-typed record produces a well-typed `ResidualValue.record`. This requires threading the `InstanceOfType` proof for each field through `asResidualValue` and constructing `InstanceOfResidualValueType.instance_of_record`.

The `instance_of_record` constructor currently has `(h₁ : True)` as a placeholder — this needs to be strengthened to a proper record well-typedness condition.

### Category 4: Refinement from `isValidAndConsistent`

**File**: `Cedar/Thm/TPE/Input.lean`
```lean
theorem consistent_checks_ensure_refinement :
  isValidAndConsistent schema req es preq pes = .ok () →
  RequestAndEntitiesRefine env req es preq pes
```
Two `sorry`s:
- Context refinement: `valueIsConsistent` changed shape
- Entities refinement: `entitiesMatch`/`valueIsConsistent` restructured

**Fix**: The `ValueRefines` relation needs to be connected to `valueIsConsistent`. Need a lemma: `valueIsConsistent env v pv = true → ValueRefines env v pv`. Then thread this through the context and entity cases.

### Category 5: `PreservesTypeOf` — various constructors

**File**: `Cedar/Thm/TPE/PreservesTypeOf.lean`

Multiple `sorry`s in:
- `partial_eval_preserves_typeof_unaryApp`
- `partial_eval_preserves_typeof_binaryApp`
- `partial_eval_preserves_typeof_getAttr`
- `partial_eval_preserves_typeof_hasAttr`
- `partial_eval_preserves_typeof` (var/context case)

**Fix**: These all follow the same pattern — case-split on the smart constructor's behavior and show that each branch preserves `typeOf`. The `sorry`s are due to the `Residual.evaluate` restructuring changing case tags.

### Category 6: Authorization-level `sorry`s

**File**: `Cedar/Thm/TPE/Authorizer.lean`

- `no_satisfied_effect_if_empty_satisfied_and_residual_policies`: Two `sorry`s related to `Residual.isTrue`/`isFalse` definitions changing with `ResidualValue`
- `satisfied_effect_if_non_empty_satisfied_policies`: Same issue
- `partial_authorize_satisfied_policies_is_sound`: Same issue

**Fix**: Need updated lemmas connecting `Residual.isTrue` (which pattern-matches on `ResidualValue`) to `Residual.evaluate` returning `.ok true`. Specifically:
```lean
-- Needed:
theorem isTrue_implies_evaluate_true :
  r.isTrue → r.evaluate req es = .ok (.prim (.bool true))

theorem isFalse_implies_evaluate_false :
  r.isFalse → r.evaluate req es = .ok (.prim (.bool false))
```

---

## Modification Plan

### Phase 1: Foundation — `ResidualValue` evaluation lemmas

**Priority: Highest** — unblocks almost everything else.

1. **Prove `ResidualValue.evaluate_prim`**: `(.prim p).evaluate req es = .ok (.prim p)` ✅ (already exists as `residual_value_prim_evaluates`)

2. **Prove `ResidualValue.evaluate_asResidualValue`**: For any `Value v`, `(v.asResidualValue).evaluate req es = .ok v`. By induction on `v`. The record case is the hard part — need to show `mapMKVsIntoValues₂` succeeds when all fields are `present` with recursively-correct values.

3. **Prove `Residual.val_evaluate`**: `(.val v ty).evaluate req es = ResidualValue.evaluate v req es`. This is definitional.

4. **Prove `isTrue_implies_evaluate_true`** and **`isFalse_implies_evaluate_false`**: Pattern match on the `isTrue`/`isFalse` definitions and use the prim evaluation lemma.

**Files to modify**: `Cedar/Thm/TPE/Residual.lean`

### Phase 2: Roundtrip lemmas

5. **Complete `asValue_inverse_asResidualValue`**: Remove the two `sorry`s in the record case. Requires induction on the map's list representation and the Phase 1 results.

6. **Prove `asValue_eq_some_implies`**: `rv.asValue = some v → rv = v.asResidualValue`.

7. **Complete `asValue_evaluate_val`**: Uses result from step 2.

**Files to modify**: `Cedar/Thm/TPE/Residual.lean`

### Phase 3: Well-typedness

8. **Strengthen `InstanceOfResidualValueType.instance_of_record`**: Replace `(h₁ : True)` with a proper condition relating record fields to the record type.

9. **Complete `InstanceOfType.toResidualValueType`** record case.

10. **Complete `conversion_preserves_typedness`** — the `entityUID` sub-case has a `sorry` for `EntityUID.WellFormed`.

**Files to modify**: `Cedar/Thm/WellTyped/Residual/Definition.lean`

### Phase 4: Conversion and PreservesTypeOf

11. **Fix `conversion_preserves_evaluation`** lit case: Use the new `ResidualValue.evaluate_prim` lemma.

12. **Fix `PreservesTypeOf` sorry cases**: Update case splits to match the restructured smart constructors.

**Files to modify**: `Cedar/Thm/TPE/Conversion.lean`, `Cedar/Thm/TPE/PreservesTypeOf.lean`

### Phase 5: ErrorFree

13. **Fix `error_free_evaluate_ok`** val case: Use `ResidualValue.evaluate_asResidualValue` or a well-typed variant.

**Files to modify**: `Cedar/Thm/TPE/ErrorFree.lean`

### Phase 6: Refinement

14. **Prove `valueIsConsistent_implies_ValueRefines`**: Bridge the boolean check to the inductive relation.

15. **Complete `consistent_checks_ensure_refinement`**: Use step 14 for context and entities.

**Files to modify**: `Cedar/Thm/TPE/Input.lean`

### Phase 7: Authorization

16. **Fix authorization-level `sorry`s**: Use `isTrue_implies_evaluate_true` and `isFalse_implies_evaluate_false` from Phase 1.

**Files to modify**: `Cedar/Thm/TPE/Authorizer.lean`, `Cedar/Thm/TPE.lean`

---

## Dependency Graph

```
Phase 1 (ResidualValue eval lemmas)
  ├── Phase 2 (Roundtrip lemmas)
  │     └── Phase 5 (ErrorFree)
  ├── Phase 4 (Conversion + PreservesTypeOf)
  └── Phase 7 (Authorization)

Phase 3 (Well-typedness)
  └── Phase 5 (ErrorFree)

Phase 6 (Refinement) — independent
```

## Estimated Effort

| Phase | Files | Estimated Difficulty | `sorry` Count |
|---|---|---|---|
| Phase 1 | 1 | Medium (record induction) | Unblocks ~10 |
| Phase 2 | 1 | Medium | 3 |
| Phase 3 | 1 | Medium-Hard (record WT) | 2 |
| Phase 4 | 2 | Low-Medium | 5 |
| Phase 5 | 1 | Low (uses Phase 1) | 1 |
| Phase 6 | 1 | Medium | 2 |
| Phase 7 | 2 | Low (uses Phase 1) | 5 |

**Total `sorry`s to resolve**: ~18 across 9 files.

The critical path is **Phase 1 → Phase 2 → Phase 5** and **Phase 1 → Phase 7**. Phase 1 is the keystone — once `ResidualValue.evaluate` is well-characterized, most other `sorry`s become straightforward.
