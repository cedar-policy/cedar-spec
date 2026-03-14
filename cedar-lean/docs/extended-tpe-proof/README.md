# Extended TPE Proof: Document Index

Analysis of the extended Typed Partial Evaluation (TPE) algorithm in Cedar Lean, its correctness conditions, and the plan for completing the proofs.

## Documents

1. **[Algorithm Design Analysis](01-algorithm-design.md)** — Architecture, data representations, core evaluation, batched evaluation, authorization layer, and differences from standard TPE.

2. **[Correctness Conditions](02-correctness-conditions.md)** — Top-level theorems, required preconditions (well-typedness, refinement, well-formed environments, entity loader contracts), preservation properties, and invariant summary.

3. **[Proof Modification Plan](03-proof-modification-plan.md)** — Current proof status, catalog of all `sorry`s organized by root cause, phased modification plan with dependency graph and effort estimates.

4. **[New Preconditions and Invariants](04-new-preconditions-and-invariants.md)** — In-depth analysis of the preconditions and invariants introduced by field-level partiality, the `ResidualAttribute.unknown` target mechanism, and batched entity loading, including their interactions.

5. **[Unknown Target Invariants](05-unknown-target-invariants.md)** — Deep dive into the `ResidualAttribute.unknown` target mechanism: construction sites, consumption site, the core semantic correctness invariant, target shape/depth/type invariants, evaluation equivalence, and failure modes.

6. **[`hasAttr` Invariants](06-hasattr-invariants.md)** — The target delegation asymmetry between records and entities for `hasAttr`, the conservatism of record delegation, absent-attribute soundness, and the `hasTag` parallel.

7. **Paper Proof: Extended TPE Correctness (Simplified Cedar)** — A complete paper proof for a simplified Cedar with entity literals, `getAttr`, `hasAttr`, `&&`, records, and booleans.
    - [Part 1: Language and Residuals](07-paper-proof-part1.md) — Syntax, concrete semantics, partial values, residuals, `toRV` target construction.
    - [Part 2: Partial Evaluator and Refinement](07-paper-proof-part2.md) — PE rules for each expression form, value/store refinement, key refinement lemmas.
    - [Part 3: Target Correctness and Soundness](07-paper-proof-part3.md) — Target correctness definition, `toRV` correctness, `evalRV` correctness, main soundness theorem (Theorem 6.1) with all cases.
    - [Part 4: Type Preservation and Batched Evaluation](07-paper-proof-part4.md) — Type preservation, store monotonicity, missing entity equivalence, batched evaluation soundness (Theorem 8.3).
    - [Part 5: Policy & Authorization Soundness](07-paper-proof-part5.md) — `errorFree` definition, `≃` relation, conversion soundness, policy-level soundness, authorization decision soundness, end-to-end theorem, complete theorem index and dependency graph.

## Quick Reference

### Key Files

| Purpose | Definition | Proof |
|---|---|---|
| Core evaluator | `Cedar/TPE/Evaluator.lean` | `Cedar/Thm/TPE/Soundness.lean` + `Soundness/` |
| Residual types | `Cedar/TPE/Residual.lean` | `Cedar/Thm/TPE/Residual.lean` |
| Partial inputs | `Cedar/TPE/Input.lean` | `Cedar/Thm/TPE/Input.lean` |
| Batched eval | `Cedar/TPE/BatchedEvaluator.lean` | `Cedar/Thm/BatchedEvaluator.lean` |
| Authorization | `Cedar/TPE/Authorizer.lean` | `Cedar/Thm/TPE/Authorizer.lean` + `Cedar/Thm/TPE.lean` |
| Well-typedness | `Cedar/Thm/WellTyped/Residual/Definition.lean` | `Cedar/Thm/TPE/WellTyped.lean` + `WellTyped/` |
| Type preservation | — | `Cedar/Thm/TPE/PreservesTypeOf.lean` |
| Conversion | — | `Cedar/Thm/TPE/Conversion.lean` |
| Error-free | — | `Cedar/Thm/TPE/ErrorFree.lean` |

### Critical Path for Completing Proofs

```
ResidualValue.evaluate lemmas (Phase 1)
  → Roundtrip lemmas (Phase 2)
  → ErrorFree fix (Phase 5)
  → Authorization fixes (Phase 7)
```

### `sorry` Count by Root Cause

| Root Cause | Count | Phases |
|---|---|---|
| `ResidualValue.evaluate` for `.val` | ~10 | 1, 4, 5, 7 |
| `Value ↔ ResidualValue` roundtrip | 3 | 2 |
| Record well-typedness | 2 | 3 |
| Refinement from `isValidAndConsistent` | 2 | 6 |
| Smart constructor case restructuring | 5 | 4 |
