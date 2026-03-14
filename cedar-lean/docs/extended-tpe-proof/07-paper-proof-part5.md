# Paper Proof Part 5: Auxiliary Definitions, Policy & Authorization Soundness, and Conclusion

## 10. Auxiliary Definitions

### 10.1 Error-Free Residuals

The `errorFree` predicate identifies residuals that cannot produce runtime errors.

**Definition 10.1 (errorFree).**
```
errorFree(val(rv, τ))       = true
errorFree(error(τ))         = false
errorFree(r₁ && r₂ : τ)    = errorFree(r₁) ∧ errorFree(r₂)
errorFree(r has a : τ)      = errorFree(r)
errorFree(r.a : τ)          = false
```

Note: `getAttr` residuals are never error-free because they can fail if the entity is missing or the attribute is absent. In the full Cedar, `getAttr` is also not error-free. The `hasAttr` residual *is* error-free (modulo its sub-expression) because `hasAttr` uses `attrsOrEmpty` which never errors.

### 10.2 The Equivalence Relation ≃

**Definition 10.2 (Result equivalence modulo error type).**
```
Ok(v₁) ≃ Ok(v₂)     iff  v₁ = v₂
Error(_) ≃ Error(_)  always
Ok(_) ≃ Error(_)     never
Error(_) ≃ Ok(_)     never
```

Equivalently: `r₁ ≃ r₂ ↔ r₁.toOption = r₂.toOption`.

This is the relation used in the Lean formalization (`Except.toOption`). The reason we don't require error equality is that TPE represents all errors uniformly as `error(τ)` residuals, which evaluate to `extensionError`, while the concrete evaluator may produce different error types (e.g., `entityDoesNotExist`, `typeError`). Since authorization only inspects `Ok` results, error type differences are irrelevant.

### 10.3 Well-Formed Environment

**Definition 10.3 (InstanceOfWellFormedEnvironment).**
A triple `(req, E, Γ)` is a well-formed environment if:
- `req` is an instance of the request type in `Γ`
- `E` is an instance of the entity schema in `Γ`
- The action schema in `Γ` is well-formed

This is the `InstanceOfWellFormedEnvironment` predicate in the Lean code. It is established by the `isValidAndConsistent` check that runs before TPE.

---

## 11. Conversion Soundness

Before partial evaluation, a well-typed expression (`TypedExpr`) is converted to a `Residual`. This conversion must preserve evaluation semantics.

### Theorem 11.1 (Conversion preserves evaluation)

For any well-typed expression `te`, request `req`, and entities `E`:
```
⟦te.toExpr⟧_E = ⟦te.toResidual⟧ᵣ_E
```

where `te.toExpr` converts back to a plain expression and `te.toResidual` converts to a residual.

*Proof.* By structural induction on `te`. Most cases are straightforward since `toResidual` mirrors the expression structure. The key observation is that `toResidual` for a literal `lit(p, τ)` produces `val(p.asRV, τ)`, and `evalRV(p.asRV, E) = p` (Lemma 5.2). All other cases (`and`, `or`, `getAttr`, `hasAttr`, etc.) follow by congruence with the IH. □

### Theorem 11.2 (Conversion preserves well-typedness)

If `te` is well-typed in environment `Γ`, then `te.toResidual` is a well-typed residual in `Γ`.

*Proof.* By structural induction on `te`, mapping each `TypedExpr.WellTyped` constructor to the corresponding `Residual.WellTyped` constructor. □

---

## 12. Policy-Level Soundness

### 12.1 Policy Evaluation

A policy is evaluated by:
1. Validating and type-checking the policy expression against the schema
2. Converting the typed expression to a residual
3. Partially evaluating the residual

```
evaluatePolicy(schema, policy, PE) =
  let env = schema.environment
  let te = typeCheck(policy.toExpr, env)
  let r = te.toResidual
  pe(r, PE)
```

### Theorem 12.1 (Policy evaluation soundness)

If:
1. `evaluatePolicy(schema, policy, PE) = Ok(r')`
2. `isValidAndConsistent(schema, req, E, preq, PE) = Ok(())`

Then:
```
⟦policy.toExpr⟧_E ≃ ⟦r'⟧ᵣ_E
```

*Proof.*

From (2), we obtain:
- `(req, E, Γ)` is a well-formed environment (Definition 10.3)
- `E ≼_Γ PE` (by `consistent_checks_ensure_refinement`)

From (1), we obtain a typed expression `te` such that:
- `te` is well-typed in `Γ`
- `r' = pe(te.toResidual, PE)`

Let `r₀ = te.toResidual`. By Theorem 11.2, `Γ ⊢ r₀ : τ`.

By Theorem 11.1: `⟦policy.toExpr⟧_E = ⟦r₀⟧ᵣ_E`.

By Theorem 6.1 (PE soundness): `⟦r₀⟧ᵣ_E ≃ ⟦pe(r₀, PE)⟧ᵣ_E = ⟦r'⟧ᵣ_E`.

Chaining: `⟦policy.toExpr⟧_E = ⟦r₀⟧ᵣ_E ≃ ⟦r'⟧ᵣ_E`. □

---

## 13. Authorization-Level Soundness

### 13.1 Authorization Structure

Cedar authorization collects policies into four categories per effect (permit/forbid):
- **satisfied**: residual evaluates to `true`
- **false**: residual evaluates to `false`
- **error**: residual evaluates to an error
- **residual**: residual is not fully reduced

The authorization decision is:
```
decision(satisfiedForbids, satisfiedPermits, residualPermits, residualForbids) =
  if satisfiedForbids ≠ ∅           then Deny
  else if satisfiedPermits = ∅ ∧ residualPermits = ∅  then Deny
  else if residualForbids ≠ ∅       then Unknown
  else if residualPermits ≠ ∅ ∧ satisfiedPermits = ∅  then Unknown
  else                                    Allow
```

### Theorem 13.1 (Satisfied policies are sound)

If `isAuthorized(schema, policies, PE) = Ok(response)` and `isValidAndConsistent(schema, req, E, preq, PE) = Ok(())`, then for each effect:

```
response.satisfiedPolicies(effect) ⊆ Spec.satisfiedPolicies(effect, policies, req, E)
```

*Proof.* For each residual policy `rp` in `response.satisfiedPolicies(effect)`:
- `rp.residual` evaluates to `Ok(true)` under `(req, E)`
- By Theorem 12.1, `⟦policy.toExpr⟧_E ≃ ⟦rp.residual⟧ᵣ_E`
- Since `⟦rp.residual⟧ᵣ_E = Ok(true)`, we have `⟦policy.toExpr⟧_E = Ok(true)` (by ≃)
- So the policy is satisfied in the concrete semantics. □

### Theorem 13.2 (Error policies are sound)

Under the same hypotheses:
```
response.errorPolicies(effect) ⊆ Spec.isAuthorized(req, E, policies).erroringPolicies
```

*Proof.* Analogous: if the residual errors, by ≃ the concrete evaluation also errors. □

### Corollary 13.3 (Authorization decision soundness)

If the TPE authorization returns `decision = Some(Deny)`, then `Spec.isAuthorized(req, E, policies) = Deny`.

*Proof.* `Some(Deny)` is returned when either:
- `satisfiedForbids ≠ ∅`: By Theorem 13.1, there exists a concrete satisfied forbid. By the basic authorization theorem, the request is denied.
- `satisfiedPermits = ∅ ∧ residualPermits = ∅`: Every permit policy is either false or errored. By Theorem 13.1 (contrapositive), no permit policy is satisfied concretely. By the basic authorization theorem, the request is denied.

If the TPE authorization returns `decision = Some(Allow)`, then `Spec.isAuthorized(req, E, policies) = Allow`.

*Proof.* `Some(Allow)` requires `satisfiedForbids = ∅`, `residualForbids = ∅`, and `satisfiedPermits ≠ ∅`. Every forbid policy is either false or errored (not satisfied). By Theorem 13.1, no forbid is concretely satisfied. There exists a satisfied permit. By the basic authorization theorem, the request is allowed. □

---

## 14. End-to-End Theorem

### Theorem 14.1 (End-to-end batched authorization soundness)

If:
1. The schema, policies, and entity loader are well-formed
2. `WellBehaved(E, L)` (the loader faithfully represents `E`)
3. The batched evaluator runs for `n` iterations

Then the authorization decision produced by the batched evaluator (if definite) agrees with `Spec.isAuthorized(req, E, policies)`.

*Proof.* Compose:
- Theorem 8.3 (batched evaluation preserves ≃ at each iteration)
- Theorem 12.1 (policy-level soundness)
- Corollary 13.3 (authorization decision soundness)

Each iteration of the batched loop:
1. Loads new entities into the partial store
2. Partially evaluates each policy residual
3. By Theorem 8.3, the new residual is ≃-equivalent to the original

When the loop terminates with a definite decision, Corollary 13.3 applies. □

---

## 15. Summary

### Theorem and Lemma Index

| # | Name | Statement | Proved in |
|---|------|-----------|-----------|
| 4.1 | Absent attribute | `find(a) = ⊥ ⟹ a ∉ dom(concrete)` | Part 2, §4.3 |
| 4.2 | Present attribute | `find(a) = present(pv) ⟹ E(uid).a ≼ pv` | Part 2, §4.3 |
| 4.3 | Unknown attribute | `find(a) = unknown(τ) ⟹ E(uid).a : τ` | Part 2, §4.3 |
| 5.1 | toRV target-correct | `TC(toRV(tgt, pv, τ), E)` | Part 3, §5 |
| 5.2 | Concrete roundtrip | `evalRV(v.asRV, E) = Ok(v)` | Part 3, §5 |
| 5.3 | Target-correct evalRV | `TC(rv, E) ⟹ evalRV(rv, E) = Ok(v)` | Part 3, §5 |
| 6.1 | **PE Soundness** | `⟦r⟧ᵣ_E ≃ ⟦pe(r, PE)⟧ᵣ_E` | Part 3, §6 |
| 6.2 | ErrorFree evaluates | `errorFree(r) ⟹ ⟦r⟧ᵣ_E is Ok` | Part 3, §6 |
| 7.1 | Type preservation | `Γ ⊢ pe(r, PE) : τ` | Part 4, §7 |
| 7.2 | toRV well-typed | `toRV(tgt, pv, τ)` well-typed | Part 4, §7 |
| 8.1 | Store monotonicity | `E ≼ store₁ ∧ E ≼ store₂ ⟹ E ≼ store₁ ∪ store₂` | Part 4, §8 |
| 8.2 | Missing entity equiv | Missing entity ≡ empty entity | Part 4, §8 |
| 8.3 | **Batched soundness** | `⟦batchLoop(...)⟧ᵣ_E ≃ ⟦r⟧ᵣ_E` | Part 4, §8 |
| 10.1 | errorFree definition | Syntactic predicate on residuals | Part 5, §10 |
| 11.1 | Conversion eval | `⟦te.toExpr⟧_E = ⟦te.toResidual⟧ᵣ_E` | Part 5, §11 |
| 11.2 | Conversion types | `te` well-typed ⟹ `te.toResidual` well-typed | Part 5, §11 |
| 12.1 | **Policy soundness** | `⟦policy⟧_E ≃ ⟦evaluatePolicy(...)⟧ᵣ_E` | Part 5, §12 |
| 13.1 | Satisfied sound | TPE satisfied ⊆ concrete satisfied | Part 5, §13 |
| 13.2 | Error sound | TPE error ⊆ concrete error | Part 5, §13 |
| 13.3 | **Decision sound** | Definite TPE decision = concrete decision | Part 5, §13 |
| 14.1 | **End-to-end** | Batched authorization is sound | Part 5, §14 |

### Proof Dependency Graph

```
Lemma 4.1–4.3 (Refinement)
    │
    ├──► Lemma 5.1 (toRV target-correct)
    │        │
    │        ▼
    │    Lemma 5.3 (evalRV correct)
    │        │
    ▼        ▼
Theorem 6.1 (PE Soundness) ◄── Lemma 6.2 (errorFree)
    │
    ├──► Theorem 7.1 (Type Preservation)
    │        │
    │        ▼
    │    Theorem 8.3 (Batched Soundness) ◄── Lemma 8.1, 8.2
    │
    ├──► Theorem 11.1 (Conversion Eval)
    │    Theorem 11.2 (Conversion Types)
    │        │
    │        ▼
    ├──► Theorem 12.1 (Policy Soundness)
    │        │
    │        ▼
    └──► Theorem 13.1–13.2 (Policy Set Soundness)
             │
             ▼
         Corollary 13.3 (Decision Soundness)
             │
             ▼
         Theorem 14.1 (End-to-End)
```

### Key Insights

1. **Target mechanism is the crux.** The `unknown(target, τ)` representation in `ResidualAttribute` is what makes extended TPE non-trivial. The target correctness lemma (5.1) is the foundation — it ensures that unknown fields can be recovered by evaluating the target expression.

2. **Asymmetric delegation is sound.** Records delegate `hasAttr`/`getAttr` on unknown fields to the *target* (the entity that owns the record), while entities delegate to *self*. Both are sound because: for records, the target points to the containing entity which has the field; for entities, the entity UID is already the correct lookup key.

3. **errorFree enables the And-RF optimization.** The `r₂' = false ∧ errorFree(r₁')` case in `&&` is the only place where PE reorders evaluation. Soundness requires that `errorFree` implies successful evaluation (Lemma 6.2), which in turn requires well-typedness.

4. **Batched evaluation is a simple inductive wrapper.** Each iteration applies PE soundness (Theorem 6.1) with a growing store. Store monotonicity (Lemma 8.1) ensures the refinement invariant is maintained. The missing entity equivalence (Lemma 8.2) justifies treating absent entities as empty.

5. **The ≃ relation (error-type erasure) is essential.** TPE collapses all errors into `error(τ)` residuals. The proof cannot show error-type equality, only that both sides are errors or both are the same `Ok` value. This suffices for authorization because the decision logic only inspects `Ok(true)` results.

∎
