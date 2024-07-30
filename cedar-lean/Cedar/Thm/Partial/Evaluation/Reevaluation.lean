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
import Cedar.Thm.Data.Map
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Evaluation.Reevaluation.AndOr
import Cedar.Thm.Partial.Evaluation.Reevaluation.Binary
import Cedar.Thm.Partial.Evaluation.Reevaluation.Call
import Cedar.Thm.Partial.Evaluation.Reevaluation.GetAttr
import Cedar.Thm.Partial.Evaluation.Reevaluation.HasAttr
import Cedar.Thm.Partial.Evaluation.Reevaluation.Ite
import Cedar.Thm.Partial.Evaluation.Reevaluation.Record
import Cedar.Thm.Partial.Evaluation.Reevaluation.Set
import Cedar.Thm.Partial.Evaluation.Reevaluation.Unary
import Cedar.Thm.Partial.Evaluation.Reevaluation.Var
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

/-!
  This file contains theorems about re-evaluating residuals.
-/

namespace Cedar.Thm.Partial.Evaluation.Reevaluation

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)

/--
  Main PE soundness theorem (for evaluation):

  Re-evaluation with a substitution on the residual expression, is equivalent to
  substituting first and then evaluating on the original expression.
-/
theorem reeval_eqv_substituting_first (expr : Spec.Expr) {entities : Partial.Entities} {req : Partial.Request} (req' : Partial.Request) (subsmap : Subsmap)
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  ReevalEquivSubstFirst expr req req' entities subsmap
:= by
  cases expr
  case lit p =>
    unfold ReevalEquivSubstFirst Partial.evaluate
    simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
  case var v => exact Var.reeval_eqv_substituting_first v req req' entities subsmap wf_r wf_e wf_s
  case and x₁ x₂ | or x₁ x₂ =>
    first
      | apply (AndOr.reeval_eqv_substituting_first wf_r wf_e wf_s _ _).left
      | apply (AndOr.reeval_eqv_substituting_first wf_r wf_e wf_s _ _).right
    · exact reeval_eqv_substituting_first x₁ req' subsmap wf_r wf_e wf_s
    · exact reeval_eqv_substituting_first x₂ req' subsmap wf_r wf_e wf_s
  case ite x₁ x₂ x₃ =>
    apply Ite.reeval_eqv_substituting_first wf_r wf_e wf_s
    · exact reeval_eqv_substituting_first x₁ req' subsmap wf_r wf_e wf_s
    · exact reeval_eqv_substituting_first x₂ req' subsmap wf_r wf_e wf_s
    · exact reeval_eqv_substituting_first x₃ req' subsmap wf_r wf_e wf_s
  case unaryApp op x₁ =>
    apply Unary.reeval_eqv_substituting_first wf_r wf_e
    · exact reeval_eqv_substituting_first x₁ req' subsmap wf_r wf_e wf_s
  case binaryApp op x₁ x₂ =>
    apply Binary.reeval_eqv_substituting_first wf_r wf_e wf_s
    · exact reeval_eqv_substituting_first x₁ req' subsmap wf_r wf_e wf_s
    · exact reeval_eqv_substituting_first x₂ req' subsmap wf_r wf_e wf_s
  case hasAttr x₁ attr =>
    apply HasAttr.reeval_eqv_substituting_first wf_r wf_e wf_s
    · exact reeval_eqv_substituting_first x₁ req' subsmap wf_r wf_e wf_s
  case getAttr x₁ attr =>
    apply GetAttr.reeval_eqv_substituting_first wf_r wf_e wf_s
    · exact reeval_eqv_substituting_first x₁ req' subsmap wf_r wf_e wf_s
  case set xs =>
    apply Set.reeval_eqv_substituting_first wf_r wf_e wf_s
    · intro x h₁
      have := List.sizeOf_lt_of_mem h₁
      exact reeval_eqv_substituting_first x req' subsmap wf_r wf_e wf_s
  case record attrs =>
    apply Record.reeval_eqv_substituting_first wf_r wf_e wf_s
    · intro (k, v) h₁
      have := List.sizeOf_lt_of_mem h₁
      apply reeval_eqv_substituting_first v req' subsmap wf_r wf_e wf_s
  case call xfn xs =>
    apply Call.reeval_eqv_substituting_first wf_r wf_e wf_s
    · intro x h₁
      have := List.sizeOf_lt_of_mem h₁
      exact reeval_eqv_substituting_first x req' subsmap wf_r wf_e wf_s
termination_by expr
decreasing_by
  all_goals simp_wf
  all_goals try omega
  case _ => -- record
    have h₂ : sizeOf v < sizeOf (k, v) := by simp only [sizeOf, Prod._sizeOf_1] ; omega
    apply Nat.lt_trans h₂
    omega


end Cedar.Thm.Partial.Evaluation.Reevaluation
