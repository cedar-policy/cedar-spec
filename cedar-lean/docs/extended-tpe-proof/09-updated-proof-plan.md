# Updated Proof Completion Plan

**Date:** 2026-03-14
**Status:** 31 sorry occurrences across 19 files. Conversion.lean is sorry-free.

## Paper Proof ↔ Lean Proof Mapping

The paper proof (docs 07-part1 through 07-part5) identifies key lemmas that must exist in the Lean formalization. Many of these are *not* currently present as named lemmas — they are implicit in the proof structure or were broken by the `ResidualValue` refactor. The plan must account for establishing these lemmas, not just mechanically fixing sorrys.

### Key Paper Lemmas and Their Lean Status

| Paper Lemma | Description | Lean Status |
|---|---|---|
| **Lemma 4.1** (absent attr → concrete absence) | If partial record has no entry for `a`, concrete record doesn't either | Needed by WellTyped/HasAttr, Soundness/HasAttr. Not currently a named lemma. Must be derived from `ValueRefines`. |
| **Lemma 4.2** (present attr matches) | Present partial entry corresponds to matching concrete value | Needed by Soundness/GetAttr, WellTyped/GetAttr. Must be derived from `ValueRefines`. |
| **Lemma 4.3** (unknown attr exists + well-typed) | Unknown partial entry has a concrete value of the declared type | Needed by Soundness/GetAttr (unknown case), WellTyped/GetAttr. Must be derived from `ValueRefines`. |
| **Lemma 5.1** (toRV target correctness) | `toResidualValue` produces target-correct values | Needed by Soundness/HasAttr (unknown→target delegation), Soundness/GetAttr (unknown→target delegation). Not currently formalized. |
| **Lemma 5.2** (evalRV roundtrip) | `(v.asResidualValue).evaluate = .ok v` | = `evaluate_asResidualValue`. Proven for prim/set/ext. Record case is sorry (Phase 1). |
| **Lemma 5.3** (evalRV for target-correct values) | Target-correct values evaluate to the concrete value | Needed by Soundness/GetAttr (present case with nested unknowns). Subsumed by Lemma 5.2 for fully-concrete values. For mixed values, follows from target correctness + IH. |
| **Lemma 6.2** (errorFree → evaluation succeeds) | = `error_free_evaluate_ok` | Proven except val case (Phase 7). |
| **Theorem 6.1** (main soundness) | = `partial_evaluate_is_sound` | Structure exists. Each case delegates to per-constructor lemma. Sorrys are in the per-constructor lemmas. |
| **Theorem 7.1** (type preservation) | = `partial_eval_preserves_well_typed` | Structure exists. Delegates to per-constructor WellTyped lemmas. Sorrys are in those lemmas. |
| **Theorem 11.1** (conversion soundness) | = `conversion_preserves_evaluation` | ✅ Done (sorry-free). |
| **Theorem 11.2** (conversion preserves types) | = `conversion_preserves_typedness` | ✅ Done (sorry-free). |
| **Lemma 7.2** (toRV well-typed) | `v.asResidualValue` is well-typed if `v` is | = `InstanceOfType.toResidualValueType`. Record case sorry in `WellTyped/Residual/Definition.lean:256`. |
| **Lemma 7.3** (targets are well-typed) | Every target in an `unknown` is well-typed | Not explicitly formalized. Needed by WellTyped/{GetAttr,HasAttr}. Follows from construction in `toResidualValue`. |
| **Theorem 8.3** (batched soundness) | Batched evaluation preserves ≃ | ✅ Done (sorry-free in `BatchedEvaluator.lean`). |
| **Theorem 12.1** (policy soundness) | = `partial_evaluate_policy_is_sound` | ✅ Done (sorry-free in `Policy.lean`). |
| **Theorem 13.1** (satisfied policies sound) | TPE satisfied ⊆ concrete satisfied | Sorrys in `Authorizer.lean` and `TPE.lean`. |
| **Corollary 13.3** (decision soundness) | Definite TPE decision = concrete decision | Depends on 13.1. |

### Missing Infrastructure Lemmas

The paper proof relies on several refinement lemmas (4.1–4.3) that don't currently exist as standalone Lean lemmas. These are needed by multiple downstream proofs and should be established early.

**Required new lemmas in `Cedar/Thm/TPE/Input.lean` or a new `Cedar/Thm/TPE/Refinement.lean`:**

1. `absent_partial_attr_implies_absent_concrete` (Lemma 4.1): If `ValueRefines env (.record concrete_attrs) (.record partial_attrs)` and `partial_attrs.find? a = none`, then `concrete_attrs.find? a = none`.

2. `present_partial_attr_implies_concrete_match` (Lemma 4.2): If `ValueRefines env (.record concrete_attrs) (.record partial_attrs)` and `partial_attrs.find? a = some (.present pv)`, then `∃ v, concrete_attrs.find? a = some v ∧ ValueRefines env v pv`.

3. `unknown_partial_attr_implies_concrete_typed` (Lemma 4.3): If `ValueRefines env (.record concrete_attrs) (.record partial_attrs)` and `partial_attrs.find? a = some (.unknown ty)`, then `∃ v, concrete_attrs.find? a = some v ∧ InstanceOfType env v ty`.

4. `toResidualValue_target_correct` (Lemma 5.1): If `ValueRefines env v pv` and `target.evaluate req es = .ok v_container`, then `(PartialValue.toResidualValue target pv ty).evaluate req es = .ok v`. This is the key lemma connecting the target mechanism to evaluation correctness.

These lemmas are the *conceptual core* of the extended TPE proof. Without them, the Soundness/HasAttr, Soundness/GetAttr, and WellTyped/GetAttr proofs cannot be completed — they aren't just "mechanical fixes."

## Current Sorry Inventory

| File | Sorrys | Root Cause |
|---|---|---|
| `Residual.lean` | 2 | `evaluate_asResidualValue` record case + `asValue_eq_some_val` record case |
| `Input.lean` | 2 | `consistent_checks_ensure_refinement` context + entities |
| `PreservesTypeOf.lean` | 6 | evaluate/apply₂/getAttr/hasAttr restructuring + context case |
| `WellTyped/Basic.lean` | 1 | `entity_data_from_partial` uses `ValueRefines` |
| `WellTyped/Var.lean` | 2 | context case restructured (`PartialValue.asResidual`, `ValueRefines`) |
| `WellTyped/Unary.lean` | 1 | `apply₁` case split on `asValue` changed |
| `WellTyped/Binary.lean` | 1 | `partial_eval_well_typed_app₂` full sorry |
| `WellTyped/HasAttr.lean` | 4 | `attrsOf` / `hasAttr` case restructuring + needs Lemmas 4.1–4.3 |
| `WellTyped/GetAttr.lean` | 1 | `partial_eval_well_typed_getAttr` full sorry + needs Lemmas 4.1–4.3, 5.1 |
| `WellTyped/Set.lean` | 1 | `Residual.asValue` split changed |
| `WellTyped/Record.lean` | 1 | `InstanceOfResidualValueType` for record |
| `WellTyped/Call.lean` | 2 | `ext_well_typed_after_map` + `partial_eval_well_typed_call` |
| `Soundness/Var.lean` | 4 | `RequestRefines` uses `PartialIsValid` |
| `Soundness/And.lean` | 1 | needs `error_free_evaluate_ok` val case (Lemma 6.2) |
| `Soundness/Or.lean` | 1 | needs `error_free_evaluate_ok` val case (Lemma 6.2) |
| `Soundness/Unary.lean` | 2 | `asValue` / `someOrError` case split |
| `Soundness/Binary.lean` | 1 | `asValue` both operands case |
| `Soundness/IfThenElse.lean` | 1 | `asValue` for condition |
| `Soundness/HasAttr.lean` | 1 | `attrsOf` restructuring + needs Lemmas 4.1–4.3, 5.1 |
| `Soundness/GetAttr.lean` | 1 | `attrsOf` restructuring + needs Lemmas 4.1–4.3, 5.1, 5.3 |
| `Soundness/Record.lean` | 1 | `mapM` / `bindAttr` restructuring |
| `Soundness/Call.lean` | 1 | `someOrError` result case |
| `ErrorFree.lean` | 1 | `error_free_evaluate_ok` val case (Lemma 6.2) |
| `Authorizer.lean` | 5 | `Residual.isTrue`/`evaluate` + `isValidAndConsistent` |
| `WellTyped/Residual/Definition.lean` | 1 | `InstanceOfType.toResidualValueType` record case (Lemma 7.2) |
| `WellTyped/Residual/Soundness.lean` | 1 | `residual_well_typed_is_sound_val` — evaluate goes through ResidualValue |
| `WellTyped/Residual.lean` | 1 | `residual_well_typed_is_sound` val case — same root cause |
| `TPE.lean` (top-level) | 2 | `partial_authorize_satisfied_*` — `.val (.prim (.bool true))` evaluate |
| **Total** | **49** | |

Note: The build reports 37 unique sorry *warnings* (per-declaration), but the source contains 49 sorry *occurrences* (some declarations have multiple sorrys). The plan tracks occurrences.

## Dependency Analysis

```
Root Cause A: evaluate_asResidualValue record case (Lemma 5.2)
  └─ Blocks: ErrorFree val case (Lemma 6.2)
       └─ Blocks: Soundness/And, Soundness/Or

Root Cause B: Residual.asValue / ResidualValue.evaluate mechanical changes
  └─ Blocks: Soundness/{Unary,Binary,IfThenElse,Call,Record}
  └─ Blocks: WellTyped/{Unary,Set,Record,Call}

Root Cause C: RequestRefines / PartialIsValid restructuring
  └─ Blocks: Input.lean (consistent_checks_ensure_refinement)
       └─ Blocks: Soundness/Var (all 4)
       └─ Blocks: Authorizer (isValidAndConsistent usage)

Root Cause D: EntitiesRefine / ValueRefines restructuring
  └─ Blocks: WellTyped/Basic (entity_data_from_partial)
       └─ Blocks: WellTyped/{Var,HasAttr,GetAttr,Binary}

Root Cause E: Missing refinement lemmas (paper Lemmas 4.1–4.3, 5.1)  ← NEW
  └─ Blocks: Soundness/{HasAttr,GetAttr} (the conceptually hard cases)
  └─ Blocks: WellTyped/{HasAttr,GetAttr} (type preservation for attr access)
```

Root Cause E is NEW compared to the previous plan. The old plan treated HasAttr/GetAttr sorrys as "smart constructor case restructuring" — a mechanical fix. But the paper proof shows these cases require *substantive new lemmas* about the refinement relation and target correctness. These are not just API changes; they are the conceptual heart of the extended TPE proof.

## Phased Plan

### Phase 0: Refinement Infrastructure (NEW — paper Lemmas 4.1–4.3)

**Goal:** Establish the refinement lemmas that the paper proof identifies as prerequisites for HasAttr/GetAttr cases.

**What's needed:**
1. Formalize `ValueRefines` inversion lemmas for records:
   - `absent_partial_attr_implies_absent_concrete` (Lemma 4.1)
   - `present_partial_attr_implies_concrete_match` (Lemma 4.2)
   - `unknown_partial_attr_implies_concrete_typed` (Lemma 4.3)
2. These are structural inversions of the `ValueRefines`/`AttributesRefines` inductive — they should follow by induction on the refinement derivation.

**Strategy:** Read the `ValueRefines` definition, then prove each lemma by cases/induction on the refinement proof. The `cons_unknown_neq` case (doc 04, §2.1) requires care — it means the partial list can have entries not in the concrete list.

**Files:** New file `Cedar/Thm/TPE/Refinement.lean` or additions to `Cedar/Thm/TPE/Input.lean`
**Sorrys eliminated:** 0 directly, but unblocks Phases 6 and 8
**Estimated difficulty:** Medium. The `cons_unknown_neq` case is the tricky part.

### Phase 1: Record Evaluation Roundtrip (paper Lemma 5.2)

**Goal:** Prove `evaluate_asResidualValue` record case.

**What's needed:** Show that `ResidualValue.evaluate` on a record produced by `Value.asResidualValue` returns the original value. The record has only `present` fields (no `unknown`), so `mapMKVsIntoValues₂` just evaluates each `present v.asResidualValue` via the IH.

**Strategy:**
1. Rewrite `mapMKVsIntoValues₂` and `mapOnValues₂` to their non-`₂` equivalents
2. Show the composed operation is identity using the IH
3. List-level induction wrapped in Map structure

**Files:** `Cedar/Thm/Data/Map.lean`, `Cedar/Thm/TPE/Residual.lean`
**Sorrys eliminated:** 1
**Estimated difficulty:** Hard.

### Phase 1a: InstanceOfType.toResidualValueType record case (paper Lemma 7.2) (NEW)

**Goal:** Prove that `v.asResidualValue` is well-typed when `v` is a well-typed record.

**What's needed:** Bridge `InstanceOfType env (.record m) (.record rty)` to `InstanceOfResidualValueType env (Value.asResidualValue (.record m)) (.record rty)`. The record case of `asResidualValue` maps each value to `present v.asResidualValue`, so we need to show each mapped entry is well-typed by the IH.

**Files:** `Cedar/Thm/WellTyped/Residual/Definition.lean`
**Sorrys eliminated:** 1
**Estimated difficulty:** Medium-Hard. Similar Map induction pattern to Phase 1.
**Note:** This also unblocks `residual_well_typed_is_sound` val case and `residual_well_typed_is_sound_val`.

### Phase 1b: Target Correctness (paper Lemma 5.1) (NEW)

**Goal:** Prove that `PartialValue.toResidualValue` produces values that evaluate correctly.

**What's needed:** If `ValueRefines env v pv` and the target evaluates to the container, then `(toResidualValue target pv ty).evaluate req es = .ok v`.

**Strategy:** By induction on `pv`:
- Primitive/set/ext: `toResidualValue` returns the value directly. Evaluation is immediate.
- Record with `present` fields: recurse with IH. The new target is `.getAttr target a rty`, which evaluates to the concrete sub-record.
- Record with `unknown` fields: the `unknown(target, ty)` entry evaluates via `.getAttr target a ty`, which by hypothesis evaluates to the concrete value at that attribute.

This lemma connects Phases 0 and 1: it uses the refinement lemmas (Phase 0) to know that unknown fields have concrete values, and it uses the evaluation roundtrip (Phase 1) for fully-concrete sub-values.

**Files:** `Cedar/Thm/TPE/Residual.lean` or new `Cedar/Thm/TPE/TargetCorrectness.lean`
**Sorrys eliminated:** 0 directly, but is the key lemma for Soundness/GetAttr
**Estimated difficulty:** Hard. This is the most conceptually novel lemma.
**Dependency:** Phases 0 and 1.

### Phase 2: Input Refinement (Root Cause C)

**Goal:** Fix `consistent_checks_ensure_refinement` in `Input.lean`.

**What's needed:** Two sorrys:
1. Context refinement: `valueIsConsistent` changed shape. Need to trace through the new `PartialIsValid` wrappers.
2. Entities refinement: `entitiesMatch`/`valueIsConsistent` restructured. Need to show `isValidAndConsistent.entitiesAreConsistent` implies `EntitiesRefine`.

**Files:** `Cedar/Thm/TPE/Input.lean`
**Sorrys eliminated:** 2, unlocks Soundness/Var (4) + Authorizer (5)
**Estimated difficulty:** Medium.

### Phase 3: Entity Data Extraction (Root Cause D)

**Goal:** Fix `entity_data_from_partial` in `WellTyped/Basic.lean`.

**What's needed:** Unfold `EntitiesRefine`, extract the entity data, and get `InstanceOfSchemaEntry` from `InstanceOfWellFormedEnvironment`.

**Files:** `Cedar/Thm/TPE/WellTyped/Basic.lean`
**Sorrys eliminated:** 1, unlocks all WellTyped sorrys
**Estimated difficulty:** Medium.

### Phase 4: Soundness/Var (depends on Phase 2)

**Goal:** Fix all 4 sorrys. Extract concrete values from `PartialIsValid` wrappers in `RequestRefines`.

**Files:** `Cedar/Thm/TPE/Soundness/Var.lean`
**Sorrys eliminated:** 4
**Estimated difficulty:** Medium.

### Phase 5: Mechanical Soundness Fixes (Root Cause B)

**Goal:** Fix Soundness sorrys that are purely mechanical `asValue`/`ResidualValue.evaluate` adaptations.

**What's needed:** Use `evaluate_asResidualValue` or the existing `@[simp]` lemmas for prim/set/ext where the old proof assumed `Residual.evaluate (.val v ty) = .ok v`.

**Files:** `Soundness/{Unary,Binary,IfThenElse,Call,Record}.lean`
**Sorrys eliminated:** 6
**Estimated difficulty:** Medium. Mostly mechanical.
**Note:** The Record case needs Phase 1. Other cases can proceed independently.

### Phase 6: Soundness/HasAttr and Soundness/GetAttr (depends on Phases 0, 1b)

**Goal:** Fix the HasAttr and GetAttr soundness proofs.

**Why this is NOT mechanical:** The paper proof (Theorem 6.1, HasAttr/GetAttr cases) shows these require:
- Lemma 4.1 (absent → concrete absence) for the `find(a) = ⊥` sub-case
- Lemma 4.2 (present → concrete match) for the `find(a) = present` sub-case
- Lemma 4.3 (unknown → concrete typed) for the `find(a) = unknown` sub-case
- Lemma 5.1 (target correctness) for the unknown→target delegation sub-case

**Strategy:** Follow the paper proof case-by-case:
1. Error case: trivial
2. Record value case: split on `find(a)` result, use Lemmas 4.1–4.3
3. Entity value case: split on `PE.attrs(uid)`, then on `find(a)`, use Lemmas 4.1–4.3
4. Unknown target delegation: use Lemma 5.1
5. Non-value case: direct from IH

**Files:** `Soundness/{HasAttr,GetAttr}.lean`
**Sorrys eliminated:** 2
**Estimated difficulty:** Hard. These are the conceptually deepest soundness cases.

### Phase 7: ErrorFree val case (depends on Phase 1)

**Goal:** Fix `error_free_evaluate_ok` val case.

**What's needed:** Show `(Residual.val rv ty).evaluate req es` is `.ok` when the residual is well-typed and error-free.

**Key question:** Can a well-typed `.val rv ty` have `unknown` fields in `rv`? If yes, evaluation could fail (the target `getAttr` might error). If no, then `rv = v.asResidualValue` for some `v` and `evaluate_asResidualValue` applies.

The paper proof says `errorFree(val(rv, τ)) = true` unconditionally, but the paper uses `≃` (toOption), not `isOk`. The Lean `error_free_evaluate_ok` claims `isOk`, which is stronger. This needs investigation:
- If `.val` residuals produced by TPE always have fully-concrete `ResidualValue`s → follows from Phase 1
- If `.val` residuals can have unknowns → need target correctness (Phase 1b) or a stronger hypothesis

**Files:** `Cedar/Thm/TPE/ErrorFree.lean`
**Sorrys eliminated:** 1, unlocks And/Or
**Estimated difficulty:** Medium-Hard.

### Phase 8: WellTyped + PreservesTypeOf Lemmas (depends on Phases 0, 3)

**Goal:** Fix all WellTyped/ sorrys and PreservesTypeOf sorrys.

**Sub-phases:**

**8a. WellTyped/{HasAttr,GetAttr}** — Need refinement lemmas (Phase 0) and `entity_data_from_partial` (Phase 3). The paper proof (Theorem 7.1) shows type preservation for attr access requires Lemmas 4.2, 4.3, and Lemma 7.3 (targets are well-typed).

**8b. WellTyped/{Unary,Binary,Set,Record,Call}** — Mostly mechanical: case-split on `asValue`, handle the `ResidualValue` layer.

**8c. WellTyped/Var** — Context case needs `PartialValue.asResidual` and `ValueRefines`.

**8d. PreservesTypeOf.lean (6 sorrys)** — Type preservation for individual PE rules. The sorrys are:
- 2 sorrys: `Residual.evaluate` changed shape for val case
- 1 sorry: case tags changed due to `TPE.apply₂` restructuring
- 1 sorry: `TPE.getAttr`/`someOrError` changed
- 1 sorry: `TPE.hasAttr` changed
- 1 sorry: context is now `PartialAttributes`, more complex

These are a mix of mechanical (val/apply₂) and conceptual (getAttr/hasAttr need refinement lemmas, context needs `ValueRefines`).

**Files:** `Cedar/Thm/TPE/WellTyped/*.lean`, `Cedar/Thm/TPE/PreservesTypeOf.lean`
**Sorrys eliminated:** 13 + 6 = 19
**Estimated difficulty:** Hard (HasAttr, GetAttr, Binary, Call, PreservesTypeOf getAttr/hasAttr) to Medium (others).

### Phase 9: Soundness/And and Soundness/Or (depends on Phase 7)

**Files:** `Cedar/Thm/TPE/Soundness/{And,Or}.lean`
**Sorrys eliminated:** 2
**Estimated difficulty:** Easy once Phase 7 is done.

### Phase 10: Authorizer + TPE.lean (depends on Phases 2, 5)

**Files:** `Cedar/Thm/TPE/Authorizer.lean`, `Cedar/Thm/TPE.lean`
**Sorrys eliminated:** 5 + 2 = 7
**Estimated difficulty:** Medium. The 2 sorrys in `TPE.lean` are identical to the Authorizer pattern — `Residual.evaluate (.val (.prim (.bool true)) ty)` goes through `ResidualValue.evaluate`. Use `residual_val_prim_evaluates`.

### Phase 10b: WellTyped/Residual sorrys (depends on Phase 1a) (NEW)

**Goal:** Fix `residual_well_typed_is_sound_val` and `residual_well_typed_is_sound` val case.

**What's needed:** Both need to show that if `InstanceOfResidualValueType env rv ty` and `rv.evaluate req es = .ok v`, then `InstanceOfType env v ty`. With the old code, `.val v ty` evaluated directly to `v`. Now it goes through `ResidualValue.evaluate`. Need to show `ResidualValue.evaluate` preserves types — i.e., if `rv` is well-typed and evaluates to `v`, then `v` has the same type.

**Files:** `Cedar/Thm/WellTyped/Residual/Soundness.lean`, `Cedar/Thm/WellTyped/Residual.lean`
**Sorrys eliminated:** 2
**Estimated difficulty:** Medium. Depends on Phase 1a for the record case.

## Execution Order

```
Phase 0 (refinement lemmas)     Phase 1 (record roundtrip)     Phase 2 (Input refinement)     Phase 3 (entity_data)
         │                               │                              │                              │
         ├───────────────────────────────┐│                              │                              │
         │                              ││                              │                              │
         ▼                              ▼▼                              ▼                              ▼
Phase 1b (target correctness)   Phase 7 (ErrorFree val)        Phase 4 (Soundness/Var)        Phase 8 (WellTyped/*)
         │                               │                              │
         ▼                               ▼                              ▼
Phase 6 (Soundness/HasAttr,GetAttr)  Phase 9 (And/Or)          Phase 10 (Authorizer)

Phase 5 (mechanical Soundness fixes) — independent, can run anytime
```

Phases 0, 1, 2, 3 are all independent starting points.

## Recommended Attack Order (Serial)

1. **Phase 0** — Refinement lemmas (new infrastructure, unblocks the hardest proofs)
2. **Phase 2** — Input.lean (2 sorrys, unblocks 9 downstream)
3. **Phase 3** — Basic.lean (1 sorry, unblocks 13 WellTyped sorrys)
4. **Phase 1** — Record roundtrip (hardest single sorry)
5. **Phase 5** — Mechanical Soundness fixes (6 sorrys, mostly independent)
6. **Phase 10** — Authorizer (5 sorrys, mechanical once Phase 2 done)
7. **Phase 4** — Soundness/Var (4 sorrys, mechanical once Phase 2 done)
8. **Phase 1b** — Target correctness (key conceptual lemma)
9. **Phase 7** — ErrorFree val (needs investigation + Phase 1)
10. **Phase 8** — WellTyped/* (13 sorrys, largest batch)
11. **Phase 6** — Soundness/HasAttr,GetAttr (conceptually deepest)
12. **Phase 9** — And/Or (2 sorrys, easy)

## Effort Estimates

| Phase | Sorrys | Difficulty | Est. Time | Paper Lemma |
|---|---|---|---|---|
| 0 | 0 (infra) | Medium | 2-3 hours | 4.1, 4.2, 4.3 |
| 1 | 1 | Hard | 3-4 hours | 5.2 |
| 1a | 1 | Medium-Hard | 1-2 hours | 7.2 |
| 1b | 0 (infra) | Hard | 3-4 hours | 5.1 |
| 2 | 2 | Medium | 1-2 hours | — |
| 3 | 1 | Medium | 1 hour | — |
| 4 | 4 | Medium | 1-2 hours | — |
| 5 | 6 | Medium | 2-3 hours | — |
| 6 | 2 | Hard | 2-3 hours | 6.1 (HasAttr/GetAttr cases) |
| 7 | 1 | Medium-Hard | 1-2 hours | 6.2 |
| 8 | 19 | Hard | 6-8 hours | 7.1 |
| 9 | 2 | Easy | 30 min | — |
| 10 | 7 | Medium | 2-3 hours | 13.1, 13.3 |
| 10b | 2 | Medium | 1 hour | — |
| **Total** | **49** | | **28-40 hours** |

## What Changed From the Previous Plan

1. **Added Phase 0 (refinement lemmas)** — The paper proof's Lemmas 4.1–4.3 are prerequisites for HasAttr/GetAttr but don't exist in the Lean codebase. The old plan missed this entirely.

2. **Added Phase 1b (target correctness)** — Paper Lemma 5.1 is the conceptual core of the extended TPE proof. It connects the `unknown` target mechanism to evaluation correctness. Without it, Soundness/GetAttr cannot be completed.

3. **Reclassified HasAttr/GetAttr as conceptually hard** — The old plan called these "smart constructor case restructuring." The paper proof reveals they require substantive new lemmas about refinement and target correctness.

4. **Identified the ErrorFree val question** — The paper proof uses `≃` (toOption) but the Lean `error_free_evaluate_ok` claims `isOk`. For `.val` residuals with `unknown` fields, `isOk` requires target correctness. This is a potential design issue.

5. **Added paper lemma cross-references** — Each phase now maps to the paper proof lemma it formalizes, making the connection between paper and Lean explicit.

6. **Increased time estimate** — From 15-22 hours to 25-36 hours, reflecting the new infrastructure phases and newly discovered sorrys.

7. **Found 5 additional sorrys outside `Cedar/Thm/TPE/`** — 1 in `WellTyped/Residual/Definition.lean` (Lemma 7.2 record case), 1 in `WellTyped/Residual/Soundness.lean`, 1 in `WellTyped/Residual.lean`, and 2 in `TPE.lean` (top-level authorization). Total is now 42, not 37.

8. **Added Phase 1a** (toResidualValueType record case) — Paper Lemma 7.2. This sorry was in `WellTyped/Residual/Definition.lean`, outside the `TPE/` directory, and was missed by the initial grep. It blocks the `residual_well_typed_is_sound` val case.

9. **Added Phase 10b** (WellTyped/Residual soundness sorrys) — 2 sorrys that need `ResidualValue.evaluate` to preserve types.
