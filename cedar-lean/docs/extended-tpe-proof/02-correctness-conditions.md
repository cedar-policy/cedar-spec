# Correctness Conditions for Extended TPE

## Overview

This document identifies the key correctness properties that the extended TPE algorithm must satisfy, the preconditions required, and the formal statements as they appear (or should appear) in the Lean codebase.

## Top-Level Correctness Theorems

### 1. Expression-Level Soundness (`partial_evaluate_is_sound`)

**Statement**: Partially evaluating a well-typed residual and then fully evaluating the result produces the same value as directly fully evaluating the original residual.

```lean
theorem partial_evaluate_is_sound :
  Residual.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine env req es preq pes →
  (x.evaluate req es).toOption = ((TPE.evaluate x preq pes).evaluate req es).toOption
```

**Key aspects**:
- Equivalence is via `Except.toOption` — errors are treated as equivalent regardless of error type
- This is deliberate: TPE collapses all errors to `.error ty` (which evaluates to `extensionError`), while concrete evaluation may produce different error types
- The theorem says: if concrete evaluation succeeds, partial+re-evaluation succeeds with the same value; if concrete evaluation errors, partial+re-evaluation also errors

### 2. Policy-Level Soundness (`partial_evaluate_policy_is_sound`)

**Statement**: Evaluating a residual produced by `evaluatePolicy` is equivalent to evaluating the original policy expression.

```lean
theorem partial_evaluate_policy_is_sound :
  evaluatePolicy schema policy preq pes = .ok residual →
  isValidAndConsistent schema req es preq pes = .ok () →
  (Spec.evaluate policy.toExpr req es).toOption = (Residual.evaluate residual req es).toOption
```

This composes: type checking → type lifting → conversion to residual → partial evaluation → soundness.

### 3. Authorization-Level Soundness (`reauthorize_is_sound`)

**Statement**: Re-authorizing a partial response with concrete data produces the same result as direct concrete authorization.

```lean
theorem reauthorize_is_sound :
  isValidAndConsistent schema req es preq pes = Except.ok () →
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  response.reauthorize req es = Spec.isAuthorized req es policies
```

### 4. Partial Decision Soundness (`partial_authorize_decision_is_sound`)

**Statement**: If partial authorization reaches a definite decision, concrete authorization reaches the same decision.

```lean
theorem partial_authorize_decision_is_sound :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  response.decision = some decision →
  (Spec.isAuthorized req es policies).decision = decision
```

### 5. Batched Evaluation Soundness (`batched_eval_eq_evaluate`)

**Statement**: Batched evaluation with an entity loader produces the same result as evaluation with the complete entity store.

```lean
theorem batched_eval_eq_evaluate :
  EntityLoader.WellBehaved es loader →
  TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvaluate x req loader iters) req es).toOption =
    (evaluate x.toExpr req es).toOption
```

## Required Preconditions

### Precondition 1: Well-Typed Residuals (`Residual.WellTyped`)

Every residual must be well-typed in the type environment. This is established by:
1. Type checking the policy expression (`typeOf`)
2. Converting `TypedExpr` to `Residual` (`TypedExpr.toResidual`)
3. Proving conversion preserves well-typedness (`conversion_preserves_typedness`)

### Precondition 2: Well-Formed Environment (`InstanceOfWellFormedEnvironment`)

The concrete request and entities must be valid with respect to the schema/type environment. This ensures that type-directed reasoning in the proofs is sound.

### Precondition 3: Refinement (`RequestAndEntitiesRefine`)

The partial request/entities must be a *refinement* of the concrete ones:

```lean
def RequestAndEntitiesRefine env req es preq pes : Prop :=
  RequestRefines env req preq ∧ EntitiesRefine env es pes
```

Where:
- **`RequestRefines`**: If the partial request specifies a principal/resource/action/context, it matches the concrete request
- **`EntitiesRefine`**: For every entity in the partial store, there exists a corresponding concrete entity, and every `present` partial attribute matches the concrete value; every `unknown` attribute has a concrete value of the declared type

The refinement relation uses `ValueRefines` which is mutually inductive with `AttributesRefines`:

```lean
inductive ValueRefines : TypeEnv → Value → PartialValue → Prop
  | prim : ValueRefines env (.prim p) (.prim p)
  | ext  : ValueRefines env (.ext e) (.ext e)
  | set  : ValueRefines env (.set vs) (.set vs)
  | record : AttributesRefines env a a' →
             ValueRefines env (.record (.mk a)) (.record (.mk a'))
```

### Precondition 4: Validity and Consistency (`isValidAndConsistent`)

This is the runtime check that establishes refinement:

```lean
def isValidAndConsistent schema req es preq pes : Except ConcretizationError Unit
```

It checks:
1. The schema has an environment for the partial request's action
2. Both request and entities pass validation
3. Concrete values are consistent with partial values (via `valueIsConsistent`)
4. The environment is well-formed

### Precondition 5: Well-Behaved Entity Loader

For batched evaluation:

```lean
abbrev EntityLoader.WellBehaved (store : Entities) (loader : EntityLoader) : Prop :=
  ∀ s, s ⊆ (loader s).keys ∧
       EntitiesRefine store ((loader s).mapOnValues MaybeEntityData.asPartial)
```

Two conditions:
1. **Completeness**: The loader returns entries for all requested UIDs
2. **Refinement**: The loaded data refines the backing store

## Preservation Properties

### Type Preservation (`partial_eval_preserves_well_typed`)

```lean
theorem partial_eval_preserves_well_typed :
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine env req es preq pes →
  Residual.WellTyped env res →
  Residual.WellTyped env (TPE.evaluate res preq pes)
```

Partial evaluation preserves well-typedness. This is critical for:
- The inductive soundness proof (each recursive call needs well-typedness)
- The batched evaluation loop (each iteration needs well-typedness of the residual)

### Type-Of Preservation (`partial_eval_preserves_typeof`)

```lean
theorem partial_eval_preserves_typeof :
  ∀ res, Residual.WellTyped env res →
    (TPE.evaluate res preq pes).typeOf = res.typeOf
```

The `typeOf` accessor returns the same type before and after partial evaluation.

### Conversion Preservation (`conversion_preserves_evaluation`)

```lean
theorem conversion_preserves_evaluation (te : TypedExpr) (req : Request) (es : Entities) :
  Spec.evaluate te.toExpr req es = (TypedExpr.toResidual te).evaluate req es
```

Converting a `TypedExpr` to a `Residual` and evaluating the residual gives the same result as evaluating the original expression.

## Error-Free Residuals

The `ErrorFree` property is used to justify optimizations in smart constructors:

```lean
inductive Residual.ErrorFree : Residual → Prop
  | val : ErrorFree (.val v ty)
  | var : ErrorFree (.var v ty)
  | binary : ¬ op.CanError → ErrorFree x₁ → ErrorFree x₂ → ErrorFree (.binaryApp op x₁ x₂ ty)
  ...
```

**Key theorem**: An error-free, well-typed residual always evaluates successfully:

```lean
theorem error_free_evaluate_ok :
  InstanceOfWellFormedEnvironment req es env →
  Residual.WellTyped env r →
  r.ErrorFree →
  (r.evaluate req es).isOk
```

This justifies, e.g., `TPE.and l (.val false _) ty` → `false` when `l.errorFree`, because we know `l` won't error.

## Invariant Summary

For the extended TPE to be correct, the following invariants must hold at each step:

1. **Input well-typedness**: The initial expression is well-typed
2. **Refinement**: Partial inputs refine concrete inputs
3. **Type preservation**: Each evaluation step produces a well-typed residual
4. **Semantic equivalence**: Each evaluation step preserves the evaluation semantics (modulo error types)
5. **Entity loader well-behavedness**: The loader faithfully represents the backing store
6. **Missing entity equivalence**: Missing entities behave like empty entities
