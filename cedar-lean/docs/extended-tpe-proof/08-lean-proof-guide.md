# How to Effectively Write Proofs About Cedar in Lean

A practical guide for contributors working on the Cedar Lean formalization. This document distills patterns, pitfalls, and techniques observed across the Cedar codebase — from the mature SymCC and Validation proofs to the in-progress TPE proof — and supplements them with general Lean 4 proof engineering advice.

## 1. Understand the Codebase Architecture Before You Prove

Cedar's proof files mirror the definition files:

| Definition layer | Definition path | Proof path |
|---|---|---|
| Spec (evaluator) | `Cedar/Spec/` | `Cedar/Thm/Authorization/` |
| Validation (typechecker) | `Cedar/Validation/` | `Cedar/Thm/Validation/` |
| TPE (partial evaluator) | `Cedar/TPE/` | `Cedar/Thm/TPE/` |
| SymCC (symbolic compiler) | `Cedar/SymCC/` | `Cedar/Thm/SymCC/` |
| Data structures | `Cedar/Data/` | `Cedar/Thm/Data/` |

Before writing a proof, read the definition you are proving about. Understand which functions it calls, what monads it uses (`Except`, `Option`, `do`-notation), and whether it is recursive. The proof structure should follow the definition structure.

## 2. Follow the Style Guide

Cedar has an explicit style guide in `GUIDE.md`. The key proof-relevant rules:

- **`simp only` over `simp`** in non-terminal positions. Bare `simp` is fine to close a goal, but mid-proof `simp` is fragile — it depends on the global `@[simp]` set, which changes across Lean versions.
- **`have` over `rcases`** for deconstructing values. Use `rcases` only for splitting disjunctions.
- **`exact` over `apply`** whenever possible. `exact` is more stable because it doesn't leave unification variables.
- **Fully spell out types** in declarations. Don't rely on inference for theorem signatures.
- **Minimize named hypotheses.** Prefer `Even n → ¬ Odd n` over `(isEven : Even n) : ¬ Odd n`.

## 3. The Proof Should Follow the Definition

This is the single most important principle. If a function pattern-matches on an expression constructor, the proof should case-split on the same constructor. If a function recurses, the proof should use induction with the same termination measure.

### 3.1 Case-splitting on expression forms

Cedar's main proofs (typechecking soundness, TPE soundness, SymCC correctness) all follow the same pattern: the top-level theorem does `match e with` or `induction h₁` on the expression/residual form, then delegates each case to a per-constructor lemma in a separate file.

Example from `Cedar/Thm/Validation/Typechecker.lean`:
```lean
theorem type_of_is_sound ... := by
  intro h₁ h₂ h₃
  match e with
  | .lit l => exact type_of_lit_is_sound h₃
  | .var var => exact type_of_var_is_sound h₂ h₃
  | .ite x₁ x₂ x₃ =>
    have ih₁ := @type_of_is_sound x₁
    have ih₂ := @type_of_is_sound x₂
    have ih₃ := @type_of_is_sound x₃
    exact type_of_ite_is_sound h₁ h₂ h₃ ih₁ ih₂ ih₃
  ...
```

The same pattern appears in `Cedar/Thm/SymCC/Compiler.lean` and `Cedar/Thm/TPE/Soundness.lean`. When adding a new proof for a new expression form, follow this delegation pattern: add a new file under the appropriate `Soundness/` or `WellTyped/` directory.

### 3.2 Mutual recursion

Cedar uses `mutual` blocks for definitions that recurse over expressions and their sub-structures (e.g., lists of sub-expressions in sets/records). The corresponding proofs use `mutual` theorem blocks with the same structure.

Example from `Cedar/Thm/TPE/Conversion.lean`:
```lean
mutual
theorem conversion_preserves_evaluation_forall2 :
  List.Forall₂ ... ls ls := by
  cases ls with
  | nil => simp
  | cons head tail =>
    constructor
    case left => apply conversion_preserves_evaluation
    case right => apply conversion_preserves_evaluation_forall2

theorem conversion_preserves_evaluation (te : TypedExpr) ... := by
  cases te with
  | lit p ty => ...
  | set ls ty => ... -- uses conversion_preserves_evaluation_forall2
  ...
end
```

### 3.3 Functional induction

For recursive functions that are not structurally recursive, Lean generates a `.induct` principle. Use `induction x using foo.induct` to get cases matching the function's branches with the induction hypothesis already specialized. This avoids repeating the termination argument and pattern match. Cedar's SymCC proofs use this pattern extensively.

## 4. Tactic Selection Guide

### 4.1 `simp` family

| Tactic | When to use |
|---|---|
| `simp only [f, g]` | Mid-proof unfolding of specific definitions. Stable across versions. |
| `simp [f, g]` | Closing a goal. OK because it's terminal. |
| `simp [f, *]` | Closing a goal using local hypotheses as rewrite rules. |
| `simp_all [f]` | Closing a goal by simplifying both the goal and all hypotheses. Powerful but less predictable. |
| `simp at h` | Simplifying a specific hypothesis. |

**Pitfall:** `simp [foo]` can loop if `foo` is a recursive function whose equational lemma matches its own RHS. Use `rw [foo]` or `unfold foo` instead, then `simp` on the result.

**Pitfall:** `simp` may not reduce a function defined with `termination_by` because the kernel doesn't unfold WF-recursive definitions by default. Use `simp [FunctionName]` to explicitly provide the equational lemma, or use `rw`.

### 4.2 `omega`

Closes goals involving linear arithmetic over `Nat` and `Int`. Used extensively in Cedar for:
- Termination proofs (`decreasing_by simp_wf; omega`)
- `sizeOf` obligations
- List length reasoning

### 4.3 `grind`

A more powerful automation tactic that combines congruence closure, case splitting, and arithmetic. Used in Cedar for:
- Boolean decision procedures (`grind [BinaryOp.can_error_spec]`)
- Authorization-level reasoning (`grind [hasError]`)
- Simple propositional goals

**Advice:** Use `grind` EXTENSIVLY when you think it should be easy close a goal. Sometimes the simpler tactics don't work where `grind` does.
**Advice:** DO NOT use `grind` where the goal does not seem simple. It will rairly work, so you MUST make progress yourself.


### 4.4 `split`

Eliminates `match` or `if-then-else` in the goal. Often used after `unfold`:
```lean
unfold Residual.errorFree
split
case val => ...
case error => ...
```

### 4.5 `generalize`

Names a complex sub-expression to simplify the goal:
```lean
generalize (satisfiedPolicies .forbid policies request entities) = forbids
```

Used in the authorization proofs to avoid repeating long expressions.

## 5. Working with Cedar's Data Structures

### 5.1 Maps (`Cedar.Data.Map`)

Maps are the most proof-intensive data structure in Cedar. They are canonical sorted lists of key-value pairs.

Key lemmas in `Cedar/Thm/Data/Map.lean`:
- `Map.WellFormed` / `wf_iff_sorted` — a map is well-formed iff its underlying list is sorted
- `Map.find?` lemmas — relating `find?` to list membership
- `mapOnValues` / `mapMOnValues` — functorial and monadic map over values
- `mapOnValues₂_eq_mapOnValues` — the `₂` variant (with sizeOf subtype) equals the plain variant
- `mapMOnValues₂_eq_mapMOnValues` — same for the monadic version
- `mapMOnValues_some_of_id` — if `f v = some v` for all values, then `mapMOnValues f m = some m`

**The `₂` variants and `mapMKVsIntoValues₂`:** These use `{kv // sizeOf kv < sizeOf map}` subtypes for termination. They are NOT directly convertible via `mapM₁_eq_mapM` (which expects `{x // x ∈ list}`). When proving properties about these, you often need to:
1. Prove a list-level lemma by induction on the underlying list
2. Wrap it back into the Map using `mapOnValues₂_eq_mapOnValues` or similar

### 5.2 Sets (`Cedar.Data.Set`)

Sets are canonical sorted lists. Similar proof patterns to Maps but simpler.

### 5.3 `sizeOf` infrastructure

`Cedar/Data/SizeOf.lean` provides critical lemmas for termination proofs:
- `Map.sizeOf_lt_of_value` — a value in a map is smaller than the map
- `Map.sizeOf_lt_of_values` — same, via the `values` projection
- `Map.sizeOf_lt_of_find?` — a value found by `find?` is smaller
- `Set.sizeOf_lt_of_mem` — an element of a set is smaller than the set
- `List.sizeOf_attach₂` / `sizeOf_attach₃` — for pairs in lists

These are essential for `decreasing_by` blocks.

## 6. Working with Monads (`Except` and `Option`)

Cedar uses `Except Error Value` for evaluation and `Option` for partial operations. The `do`-notation desugars to `bind`, which `simp` doesn't always handle well.

### 6.1 The `Cedar/Thm/Data/Control.lean` toolkit

This file provides `@[simp]` lemmas that let `simp` reduce `do`-notation:
```lean
@[simp] theorem Except.bind_ok (a : α) (f : α → Except ε β) :
  (bind (Except.ok a) f : Except ε β) = f a

@[simp] theorem Except.bind_err (e : ε) (f : α → Except ε β) :
  (bind (Except.error e) f : Except ε β) = (Except.error e)
```

And structural lemmas:
```lean
theorem do_eq_ok {res : Except ε α} {f : α → Except ε β} :
  (do let v ← res ; f v) = .ok b ↔ ∃ a, res = .ok a ∧ f a = .ok b
```

### 6.2 `Except.toOption` bridge

TPE soundness uses `Except.toOption` to state equivalence (ignoring error details). Key lemmas:
- `to_option_some` — `res.toOption = some v ↔ res = .ok v`
- `to_option_left_ok` — if `toOption` results match and one side is `.ok v`, so is the other

### 6.3 The `simp_do_let` custom tactic

The SymCC proofs define a custom tactic for simplifying `do`-let bindings:
```lean
syntax "simp_do_let" term (" at " ident)? : tactic
```
It performs `cases` on the bound expression and simplifies. Useful when a proof gets stuck on a `do`-block.

## 7. Termination Proofs

### 7.1 Standard pattern

```lean
theorem my_theorem (v : Value) ... := by
  match v with
  | .prim p => ...
  | .record as => ...
    have ih := my_theorem v'
    ...
termination_by sizeOf v
decreasing_by
  simp_wf
  have h := Map.sizeOf_lt_of_values hv'
  simp [Value.record.sizeOf_spec]
  omega
```

### 7.2 Common termination measures

- `sizeOf v` for `Value` recursion
- `sizeOf x` for `Expr` / `Residual` recursion
- `xs.length + ys.length` for alternating list recursion
- `sizeOf m` for `Map` recursion

### 7.3 The `simp_wf` + `omega` pattern

Almost all Cedar termination proofs use:
```lean
decreasing_by
  simp_wf
  -- possibly some sizeOf lemmas
  omega
```

`simp_wf` unfolds the well-founded relation, then `omega` handles the arithmetic.

## 8. Common Proof Patterns in Cedar

### 8.1 The `split_type_of` custom tactic

Defined in `Cedar/Thm/Validation/Typechecker/Basic.lean`, this tactic splits a hypothesis of the form `(typeOf x c env).typeOf = .ok (ty, c')` into three parts. Used extensively in the validation proofs:
```lean
split_type_of h₃ ; rename_i h₃
```

### 8.2 Inversion lemmas

Many proofs need to invert a hypothesis like "if this function returned `.ok`, then its inputs must have had this shape." The SymCC proofs name these `*_ok_implies`:
```lean
theorem compile_record_ok_implies (hok : compile (.record axs) εnv = .ok t) :
  ∃ ats, List.Forall₂ ... axs ats ∧ t = ...
```

### 8.3 `List.Forall₂` for parallel structure

When proving properties about lists processed in parallel (e.g., compiling a list of expressions), use `List.Forall₂` to relate input and output lists element-wise. The SymCC record proof is the canonical example.

### 8.4 The `EvaluatesTo` pattern

Validation soundness uses `EvaluatesTo` to allow for certain runtime errors:
```lean
def EvaluatesTo (e : Expr) (request : Request) (entities : Entities) (v : Value) : Prop :=
  evaluate e request entities = .error .entityDoesNotExist ∨
  evaluate e request entities = .error .extensionError ∨
  evaluate e request entities = .error .arithBoundsError ∨
  evaluate e request entities = .ok v
```

This is a disjunctive pattern — the proof must show one of the four cases holds.

### 8.5 Refinement / simulation arguments

TPE soundness uses a refinement relation: partial inputs refine concrete inputs, and partial evaluation refines concrete evaluation. The key predicates are:
- `RequestAndEntitiesRefine` — partial request/entities are consistent with concrete ones
- `InstanceOfWellFormedEnvironment` — concrete inputs match the type environment
- `Residual.WellTyped` — the residual is well-typed in the environment

The proof pattern is: assume refinement, show that partial evaluation produces a residual whose concrete evaluation matches the original.

## 9. Debugging Stuck Proofs

### 9.1 Use `set_option pp.all true` or `set_option pp.proofs true`

When Lean's pretty-printer hides critical details (coercions, universe levels, implicit arguments), enable verbose printing to see what's really going on.

### 9.2 Use `#check` and `#print` liberally

```lean
#check @BinaryResidualWellTyped.eq_val
#print Value.asResidualValue
```

### 9.3 The `change` tactic

When the goal is definitionally equal to something more convenient but `rfl` doesn't work (e.g., because of `termination_by` blocking reduction), use `change` to restate the goal. If `change` also fails, the terms are not definitionally equal — use `rw` or `simp` with the relevant equational lemma instead.

### 9.4 The `show` tactic

Like `change` but for providing the expected type explicitly. Useful when Lean's elaborator is confused about which instance to use.

### 9.5 `conv` for surgical rewriting

When `rw` rewrites in the wrong place, use `conv` to target a specific subterm:
```lean
conv => rhs ; unfold sizeOf _sizeOf_inst _sizeOf_1 ; simp only
```

### 9.6 Build incrementally

```bash
lake build Cedar.Thm.TPE.Residual 2>&1 | grep "error:" | head -5
lake build Cedar.Thm.TPE.Residual 2>&1 | grep "sorry"
```

Build the specific file you're working on, not the whole project. Check for both errors and sorry warnings.

## 10. Pitfalls Specific to Cedar

### 10.1 `Value` vs `ResidualValue`

The introduction of `ResidualValue` as a separate type from `Value` means that `Residual.evaluate` for the `.val` case goes through `ResidualValue.evaluate` instead of directly returning a value. Many proofs that assumed the old behavior broke. The key roundtrip lemmas are:
- `asValue_inverse_asResidualValue` — `v.asResidualValue.asValue = some v`
- `evaluate_asResidualValue` — `(v.asResidualValue).evaluate req es = .ok v`

### 10.2 `termination_by` blocks definitional reduction

Functions defined with `termination_by` (like `Value.asResidualValue`) do NOT reduce by `rfl` or `change`. You must use `simp [Value.asResidualValue]` to apply the equational lemma. This is a common source of "type mismatch: rfl" errors.

### 10.3 The `₂` variant trap

`mapOnValues₂`, `mapMOnValues₂`, `mapMKVsIntoValues₂` use sizeOf-based subtypes for termination. They are provably equal to their non-`₂` counterparts (`mapOnValues₂_eq_mapOnValues`, etc.), but the subtype structure means you can't directly apply generic `mapM` lemmas. Always rewrite to the non-`₂` variant first.

### 10.4 Record cases are always the hardest

In virtually every Cedar proof, the record case is the most difficult because:
- Records contain maps, which are lists of pairs
- Map operations use `₂` variants with sizeOf subtypes
- Induction over map values requires threading through the list structure
- The `mapMKVsIntoValues₂` function is particularly hard to reason about

Strategy: prove the list-level property first by induction, then lift to the Map level.

## 11. Workflow Recommendations

1. **Read the definition first.** Understand what you're proving about.
2. **Check if a similar proof exists.** The SymCC proofs are the most complete — look there for patterns.
3. **Start with `sorry` and refine.** Write the proof skeleton with `sorry` in each case, build to check the structure compiles, then fill in cases one at a time.
4. **Prove easy cases first.** Prim, set, ext cases are usually trivial. Record is always last.
5. **Build frequently.** Don't write 50 lines before checking if it compiles.
6. **Use `lake build ModuleName 2>&1 | grep "error:\|sorry"` to track progress.**
7. **When stuck, check the goal state.** Add `trace "{← ppGoal (← getMainGoal)}"` or use VS Code's Lean infoview.
8. **Factor out helper lemmas.** If a sub-proof is reusable, put it in `Cedar/Thm/Data/` with a clear name.
9. **Name lemmas descriptively.** Follow the `module_operation_property` pattern (e.g., `mapMOnValues_some_of_id`).
10. **Add `@[simp]` judiciously.** Only tag lemmas where the LHS is strictly more complex than the RHS and the lemma is universally useful.
