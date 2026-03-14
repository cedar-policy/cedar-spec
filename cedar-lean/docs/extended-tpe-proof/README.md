# Extended TPE Proof: Document Index

Analysis of the extended Typed Partial Evaluation (TPE) algorithm in Cedar Lean, its correctness conditions, and the plan for completing the proofs.

## Documents

1. **[Algorithm Design Analysis](01-algorithm-design.md)** — Architecture, data representations, core evaluation, batched evaluation, authorization layer, and differences from standard TPE.

2. **[Correctness Conditions](02-correctness-conditions.md)** — Top-level theorems, required preconditions (well-typedness, refinement, well-formed environments, entity loader contracts), preservation properties, and invariant summary.

3. *(Superseded by doc 09)*

4. **[New Preconditions and Invariants](04-new-preconditions-and-invariants.md)** — In-depth analysis of the preconditions and invariants introduced by field-level partiality, the `ResidualAttribute.unknown` target mechanism, and batched entity loading, including their interactions.

5. **[Unknown Target Invariants](05-unknown-target-invariants.md)** — Deep dive into the `ResidualAttribute.unknown` target mechanism: construction sites, consumption site, the core semantic correctness invariant, target shape/depth/type invariants, evaluation equivalence, and failure modes.

6. **[`hasAttr` Invariants](06-hasattr-invariants.md)** — The target delegation asymmetry between records and entities for `hasAttr`, the conservatism of record delegation, absent-attribute soundness, and the `hasTag` parallel.

7. **Paper Proof: Extended TPE Correctness (Simplified Cedar)** — A complete paper proof for a simplified Cedar with entity literals, `getAttr`, `hasAttr`, `&&`, records, and booleans.
    - [Part 1: Language and Residuals](07-paper-proof-part1.md) — Syntax, concrete semantics, partial values, residuals, `toRV` target construction.
    - [Part 2: Partial Evaluator and Refinement](07-paper-proof-part2.md) — PE rules for each expression form, value/store refinement, key refinement lemmas.
    - [Part 3: Target Correctness and Soundness](07-paper-proof-part3.md) — Target correctness definition, `toRV` correctness, `evalRV` correctness, main soundness theorem (Theorem 6.1) with all cases.
    - [Part 4: Type Preservation and Batched Evaluation](07-paper-proof-part4.md) — Type preservation, store monotonicity, missing entity equivalence, batched evaluation soundness (Theorem 8.3).
    - [Part 5: Policy & Authorization Soundness](07-paper-proof-part5.md) — `errorFree` definition, `≃` relation, conversion soundness, policy-level soundness, authorization decision soundness, end-to-end theorem, complete theorem index and dependency graph.

8. **[How to Effectively Write Proofs About Cedar in Lean](08-lean-proof-guide.md)** — Practical guide covering proof architecture, tactic selection, data structure patterns, termination proofs, debugging techniques, and Cedar-specific pitfalls.

9. **[Updated Proof Completion Plan](09-updated-proof-plan.md)** — Current sorry inventory (49 occurrences, 37 declarations, 22 files), dependency analysis of 5 root causes, 14-phase execution plan with paper proof cross-references and effort estimates.

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
Input refinement (Phase 3)  ──► Soundness/Var (Phase 4) ──► Authorizer (Phase 9)
entity_data_from_partial (Phase 5) ──► WellTyped/* (Phase 6)
evaluate_asResidualValue record (Phase 1) ──► ErrorFree val (Phase 7) ──► And/Or (Phase 8)
Soundness/* asValue adaptation (Phase 2) — mostly independent
```

### `sorry` Count by Root Cause

| Root Cause | Count | Phases |
|---|---|---|
| `Residual.asValue` / `ResidualValue.evaluate` changes | 8 | 2 |
| `RequestRefines` / `PartialIsValid` restructuring | 6 | 3, 4 |
| `EntitiesRefine` / `ValueRefines` restructuring | 1+13 | 5, 6 |
| `evaluate_asResidualValue` record case | 1+1+2 | 1, 7, 8 |
| `Residual.isTrue`/`evaluate` in Authorizer | 5 | 9 |
