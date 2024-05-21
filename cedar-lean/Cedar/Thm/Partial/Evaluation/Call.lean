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
import Cedar.Spec.Evaluator
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.Basic
import Cedar.Thm.Partial.Evaluation.Set

namespace Cedar.Thm.Partial.Evaluation.Call

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (Error ExtFun Result)

/--
  `Partial.evaluateCall` on concrete arguments gives the same output as
  `Spec.call` on those same arguments
-/
theorem evaluateCall_on_concrete_eqv_concrete {vs : List Spec.Value} {xfn : ExtFun} :
  Partial.evaluateCall xfn (vs.map Partial.Value.value) = (Spec.call xfn vs).map Partial.Value.value
:= by
  unfold Partial.evaluateCall
  simp only [List.mapM_map, List.mapM_some, Except.map]
  cases Spec.call xfn vs <;> simp

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.call`
  expression gives the same output as concrete-evaluating the `Spec.Expr.call`
  with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {xs : List Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {xfn : ExtFun} :
  (∀ x ∈ xs, PartialEvalEquivConcreteEval x request entities) →
  PartialEvalEquivConcreteEval (Spec.Expr.call xfn xs) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only
  rw [List.map₁_eq_map Spec.Expr.asPartialExpr]
  rw [List.mapM₁_eq_mapM (Partial.evaluate · request entities)]
  rw [List.mapM₁_eq_mapM (Spec.evaluate · request entities)]
  rw [List.mapM_map]
  rw [Set.mapM_partial_eval_eqv_concrete_eval ih₁]
  cases xs.mapM (Spec.evaluate · request entities) <;> simp only [Except.bind_ok, Except.bind_err]
  case error e => simp [Except.map]
  case ok vs => exact evaluateCall_on_concrete_eqv_concrete

/--
  If `Partial.evaluateCall` produces `ok` with a concrete value, then all of the
  arguments are concrete
-/
theorem partialEvaluateCall_concrete_then_args_concrete {args : List Partial.Value} {xfn : ExtFun} :
  Partial.evaluateCall xfn args = .ok (.value v) →
  ∀ arg ∈ args, ∃ v, arg = .value v
:= by
  unfold Partial.evaluateCall
  split <;> intro h₁ arg h₂
  · rename_i vs h₃
    replace ⟨v, h₃, h₄⟩ := List.mapM_some_implies_all_some h₃ arg h₂
    cases arg <;> simp at h₄
    subst v ; rename_i v
    exists v
  · rename_i h₃
    replace ⟨arg', h₃, h₄⟩ := List.mapM_none_iff_exists_none.mp h₃
    cases arg' <;> simp at h₁ h₄

/--
  If partial-evaluating a `Partial.Expr.call` produces `ok` with a concrete
  value, then so would partial-evaluating any of the arguments
-/
theorem evals_to_concrete_then_args_eval_to_concrete {xs : List Partial.Expr} {request : Partial.Request} {entities : Partial.Entities} {xfn : ExtFun} :
  EvaluatesToConcrete (Partial.Expr.call xfn xs) request entities →
  ∀ x ∈ xs, EvaluatesToConcrete x request entities
:= by
  unfold EvaluatesToConcrete
  intro h₁ x h₂
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  rw [List.mapM₁_eq_mapM (Partial.evaluate · request entities)] at h₁
  cases h₃ : xs.mapM (Partial.evaluate · request entities) <;> simp [h₃] at h₁
  case ok pvals =>
    replace ⟨pval, h₃, h₄⟩ := List.mapM_ok_implies_all_ok h₃ x h₂
    replace ⟨v, h₁⟩ := partialEvaluateCall_concrete_then_args_concrete h₁ pval h₃
    subst pval
    exists v

/--
  Inductive argument that if partial-evaluation of a `Partial.Expr.call` returns
  a concrete value, then it returns the same value after any substitution of
  unknowns
-/
theorem subst_preserves_evaluation_to_value {args : List Partial.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value} {xfn : ExtFun}
  (ih : ∀ arg ∈ args, SubstPreservesEvaluationToConcrete arg req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Partial.Expr.call xfn args) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete
  unfold Partial.evaluate Partial.evaluateCall Spec.Value.asBool
  intro h_req v
  rw [List.mapM₁_eq_mapM (Partial.evaluate · req entities)]
  cases h₁ : args.mapM (Partial.evaluate · req entities) <;> simp [h₁]
  case ok pvals =>
    split
    · rename_i vs h₂
      -- vs are the concrete values produced by evaluating the args pre-subst
      unfold Partial.Expr.subst
      rw [List.map₁_eq_map]
      simp
      rw [List.mapM₁_eq_mapM (Partial.evaluate · req' (entities.subst subsmap))]
      rw [Set.mapM_subst_preserves_evaluation_to_values ih h_req pvals h₁ (by unfold is_all_concrete ; exists vs)]
      cases h₃ : Spec.call xfn vs <;> simp
      case ok v' =>
        intro h ; subst v'
        simp [h₂, h₃]
    · rename_i h₂
      replace ⟨pval, h₂, h₃⟩ := List.mapM_none_iff_exists_none.mp h₂
      cases pval <;> simp at h₃
      case residual r => simp

end Cedar.Thm.Partial.Evaluation.Call
