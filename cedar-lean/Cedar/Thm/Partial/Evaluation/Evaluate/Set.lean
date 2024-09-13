/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Partial.Evaluator
import Cedar.Spec.Policy
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.LT
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Evaluate.Set

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Expr Result)

/--
  Lemma (used for both the Set and Call cases):

  Inductive argument that `mapM`'ing partial evaluation over a list of exprs
  gives the same output as `mapM`'ing concrete evaluation over the same exprs
-/
theorem mapM_partial_eval_eqv_concrete_eval {xs : List Expr} {request : Spec.Request} {entities : Spec.Entities} :
  (∀ x ∈ xs, PartialEvalEquivConcreteEval x request entities) →
  xs.mapM (λ x => Partial.evaluate x request entities) = (xs.mapM (Spec.evaluate · request entities)).map λ vs => vs.map Partial.Value.value
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  induction xs
  case nil => simp [Except.map, pure, Except.pure]
  case cons hd tl ih =>
    specialize ih (by
      intro x' h₁
      exact ih₁ x' (List.mem_cons_of_mem hd h₁)
    )
    cases h₁ : Spec.evaluate hd request entities
    <;> cases h₂ : Partial.evaluate hd request entities
    <;> simp only [h₁, h₂, List.mapM_cons, Except.bind_err, Except.bind_ok]
    case error.error e₁ e₂ =>
      simp only [ih₁ hd, h₁, Except.map, List.mem_cons, true_or, Except.error.injEq] at h₂
      simp only [h₂, Except.map]
    case ok.error val e | error.ok e pval =>
      simp [ih₁ hd, h₁, Except.map] at h₂
    case ok.ok val pval =>
      simp only [ih₁, h₁, Except.map, List.mem_cons, true_or, Except.ok.injEq] at h₂
      subst h₂
      -- the remaining goal is just a statement about `tl`, not `hd` itself
      -- so we can dispatch it using `ih`
      generalize h₃ : (tl.mapM λ x => Partial.evaluate x request entities) = pres at *
      generalize h₄ : (tl.mapM λ x => Spec.evaluate x request entities) = sres at *
      cases pres <;> cases sres
      <;> simp only [Except.map, pure, Except.pure, List.mem_cons, Except.error.injEq, Except.ok.injEq, Except.bind_ok, Except.bind_err, List.cons.injEq, List.map_cons, forall_eq_or_imp, true_and] at *
      case error.error e₁ e₂ => exact ih
      case ok.ok pvals vals => exact ih

/--
  Inductive argument that, for an `Expr.set` with concrete request/entities,
  partial evaluation and concrete evaluation give the same output
-/
theorem on_concrete_eqv_concrete_eval {xs : List Expr} {request : Spec.Request} {entities : Spec.Entities} :
  (∀ x ∈ xs, PartialEvalEquivConcreteEval x request entities) →
  PartialEvalEquivConcreteEval (Expr.set xs) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate
  simp only
  rw [List.mapM₁_eq_mapM (Partial.evaluate · request entities)]
  rw [List.mapM₁_eq_mapM (Spec.evaluate · request entities)]
  rw [mapM_partial_eval_eqv_concrete_eval ih₁]
  cases xs.mapM (Spec.evaluate · request entities) <;> simp only [Except.map, Except.bind_err, Except.bind_ok]
  case ok vs => simp [List.mapM_map, List.mapM_some]

/--
  Inductive argument that if partial-evaluating an `Expr.set` produces
  `ok` with some value, that value is well-formed
-/
theorem partial_eval_wf {xs : List Expr} {request : Partial.Request} {entities : Partial.Entities}
  (ih : ∀ x ∈ xs, EvaluatesToWellFormed x request entities) :
  EvaluatesToWellFormed (Expr.set xs) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  rw [List.mapM₁_eq_mapM (Partial.evaluate · request entities)]
  cases hx : xs.mapM (Partial.evaluate · request entities)
  <;> simp only [Except.bind_ok, Except.bind_err, false_implies, implies_true]
  case ok pvals =>
    split <;> simp only [Except.ok.injEq, forall_eq']
    · simp only [Partial.Value.WellFormed, Spec.Value.WellFormed]
      rename_i vs h₂
      apply And.intro (Set.make_wf vs)
      intro v h₃
      replace h₃ := (Set.make_mem _ _).mpr h₃
      replace ⟨pval, h₄, h₂⟩ := List.mapM_some_implies_all_from_some h₂ v h₃
      replace ⟨x, h₅, hx⟩ := List.mapM_ok_implies_all_from_ok hx pval h₄
      split at h₂ <;> simp at h₂
      rename_i v' ; subst v'
      simpa [Partial.Value.WellFormed] using ih x h₅ (.value v) hx
    · simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]

/--
  If partial-evaluating an `Expr.set` produces `ok` with a concrete
  value, then so would partial-evaluating any of the elements
-/
theorem evals_to_concrete_then_elts_eval_to_concrete {xs : List Expr} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Expr.set xs) request entities →
  ∀ x ∈ xs, EvaluatesToConcrete x request entities
:= by
  unfold EvaluatesToConcrete
  intro h₁ x h₂
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  rw [List.mapM₁_eq_mapM (Partial.evaluate · request entities)] at h₁
  cases h₃ : xs.mapM (Partial.evaluate · request entities)
  <;> simp only [h₃, Except.bind_err, Except.bind_ok] at h₁
  case ok pvals =>
    replace ⟨pval, h₃, h₄⟩ := List.mapM_ok_implies_all_ok h₃ x h₂
    split at h₁ <;> simp only [Except.ok.injEq, Partial.Value.value.injEq] at h₁
    subst h₁
    rename_i vs h₁
    replace ⟨v, _, h₁⟩ := List.mapM_some_implies_all_some h₁ pval h₃
    cases pval <;> simp only [Option.some.injEq] at h₁
    case value v' => subst v' ; exists v

/--
  Lemma (used for both the Set and Call cases):

  Inductive argument that if `mapM` on a list of partial exprs produces `.ok`
  with a list of concrete vals, then it produces the same list of concrete vals
  after any substitution of unknowns
-/
theorem mapM_subst_preserves_evaluation_to_values {xs : List Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih : ∀ x ∈ xs, SubstPreservesEvaluationToConcrete x req req' entities subsmap) :
  req.subst subsmap = some req' →
  ∀ (pvals : List Partial.Value),
    xs.mapM (Partial.evaluate · req entities) = .ok pvals →
    IsAllConcrete pvals →
    xs.mapM (Partial.evaluate · req' (entities.subst subsmap)) = .ok pvals
:= by
  intro h_req pvals h₁ h₂
  cases xs
  case nil =>
    simp only [List.not_mem_nil, false_implies, forall_const, List.mapM_nil, pure, Except.pure,
      Except.ok.injEq, List.map_nil] at *
    exact h₁
  case cons hd tl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.mapM_cons, pure, Except.pure,
      List.map_cons] at *
    have ⟨ih_hd, ih_tl⟩ := ih ; clear ih
    cases h₃ : Partial.evaluate hd req entities
    <;> simp only [h₃, Except.bind_ok, Except.bind_err] at h₁
    case ok hd_pval =>
      unfold IsAllConcrete at h₂
      replace ⟨vs, h₂⟩ := h₂
      replace ⟨h₂, h₂'⟩ := And.intro (List.mapM_some_implies_all_some h₂) (List.mapM_some_implies_all_from_some h₂)
      cases h₅ : tl.mapM (Partial.evaluate · req entities)
      <;> simp only [h₅, Except.bind_ok, Except.bind_err, Except.ok.injEq] at h₁
      case ok tl_pvals =>
        subst h₁
        cases h₄ : Partial.evaluate hd req' (entities.subst subsmap)
        <;> simp only [Except.bind_ok, Except.bind_err]
        case error e =>
          replace ⟨v, _, h₂⟩ := h₂ hd_pval (by simp)
          cases hd_pval <;> simp only [Option.some.injEq] at h₂
          case value v' =>
            subst v'
            unfold SubstPreservesEvaluationToConcrete at ih_hd
            simp only [ih_hd h_req v h₃] at h₄
        case ok hd'_pval =>
          have ih₂ := mapM_subst_preserves_evaluation_to_values ih_tl h_req tl_pvals h₅ (by
            unfold IsAllConcrete
            apply List.all_some_implies_mapM_some
            intro tl_pval h₆
            replace ⟨v, _, h₂⟩ := h₂ tl_pval (by simp [h₆])
            exists v
          )
          simp only [ih₂, Except.bind_ok, Except.ok.injEq, List.cons.injEq, and_true]
          cases hd_pval <;> simp only [List.mem_cons, forall_eq_or_imp, and_false, false_and,
            exists_const, Option.some.injEq] at h₂
          case value hd_val =>
            unfold SubstPreservesEvaluationToConcrete at ih_hd
            simp only [ih_hd h_req hd_val h₃, Except.ok.injEq] at h₄
            exact h₄.symm

/--
  Inductive argument that if partial-evaluation of an `Expr.set` returns
  a concrete value, then it returns the same value after any substitution of
  unknowns
-/
theorem subst_preserves_evaluation_to_value {xs : List Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih : ∀ x ∈ xs, SubstPreservesEvaluationToConcrete x req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Expr.set xs) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete
  unfold Partial.evaluate
  intro h_req v
  rw [List.mapM₁_eq_mapM (Partial.evaluate · req entities)]
  cases h₁ : xs.mapM (Partial.evaluate · req entities)
  <;> simp only [Except.bind_err, Except.bind_ok, Bool.not_eq_true', false_implies]
  case ok pvals =>
    split <;> simp only [Except.ok.injEq, Partial.Value.value.injEq, false_implies]
    rename_i vs h₂
    -- vs are the concrete values produced by evaluating the set elements pre-subst
    intro h ; subst h
    rw [List.mapM₁_eq_mapM (Partial.evaluate · req' (entities.subst subsmap))]
    rw [mapM_subst_preserves_evaluation_to_values ih h_req pvals h₁ (by unfold IsAllConcrete ; exists vs)]
    simp only [h₂, Except.bind_ok]

/--
  Inductive argument that if partial-evaluation of an `Expr.set`
  returns an error, then it also returns an error (not necessarily the same
  error) after any substitution of unknowns
-/
theorem subst_preserves_errors {xs : List Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih : ∀ x ∈ xs, SubstPreservesEvaluationToError x req req' entities subsmap) :
  SubstPreservesEvaluationToError (Expr.set xs) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToError at *
  simp only [Partial.evaluate]
  intro h_req e
  rw [List.mapM₁_eq_mapM (Partial.evaluate · req entities)]
  rw [List.mapM₁_eq_mapM (Partial.evaluate · req' (entities.subst subsmap))]
  cases hxs : xs.mapM (Partial.evaluate · req entities)
  case error e' =>
    simp only [Except.bind_err, Except.error.injEq, List.mapM_map]
    intro _ ; subst e'
    replace ⟨x, hx, hxs⟩ := List.mapM_error_implies_exists_error hxs
    replace ⟨e', ih⟩ := ih x hx h_req e hxs
    have ⟨e'', h₁⟩ := List.element_error_implies_mapM_error hx (f := λ x => Partial.evaluate x req' (entities.subst subsmap)) ih
    simp only [h₁, Except.bind_err, Except.error.injEq, exists_eq']
  case ok pvals =>
    simp only [Except.bind_ok]
    intro h₁
    split at h₁ <;> simp at h₁

end Cedar.Thm.Partial.Evaluation.Evaluate.Set
