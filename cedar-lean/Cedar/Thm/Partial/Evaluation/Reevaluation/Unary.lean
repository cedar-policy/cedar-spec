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
import Cedar.Thm.Partial.Evaluation.Evaluate
import Cedar.Thm.Partial.Evaluation.Evaluate.Unary
import Cedar.Thm.Partial.Evaluation.ReevaluateUnaryApp
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Reevaluation.Unary

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Prim UnaryOp)

/--
  Inductive argument that re-evaluation of a `Spec.Expr.unaryApp` with a
  substitution on the residual expression, is equivalent to substituting first
  and then evaluating on the original `Spec.Expr.unaryApp`.
-/
theorem reeval_eqv_substituting_first {x₁ : Spec.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (ih₁ : ReevalEquivSubstFirst x₁ req req' entities subsmap) :
  ReevalEquivSubstFirst (Spec.Expr.unaryApp op x₁) req req' entities subsmap
:= by
  unfold ReevalEquivSubstFirst at *
  simp only [Partial.evaluate]
  split <;> try simp only [implies_true]
  rename_i hₑ h₁ ; simp only [bind_assoc, Prod.mk.injEq] at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
  intro h_req ; specialize ih₁ h_req
  simp only at ih₁ ; split at ih₁ <;> rename_i ih₁'
  · exfalso
    rename_i hₑ _ e₁ e₂
    simp only [bind_assoc, Prod.mk.injEq] at ih₁' ; replace ⟨ih₁', ih₁''⟩ := ih₁'
    simp only [ih₁'', Except.bind_err, Except.error.injEq, imp_false, forall_apply_eq_imp_iff] at hₑ
    cases hx₁ : Partial.evaluate x₁ req entities
    <;> simp only [hx₁, Except.bind_ok, Except.bind_err, Except.error.injEq, forall_eq'] at ih₁' hₑ
    · rename_i pval₁
      have wf_pval₁ : pval₁.WellFormed := Evaluate.partial_eval_wf wf_r wf_e pval₁ hx₁
      have h := ReevaluateUnaryApp.reeval_eqv_substituting_first op pval₁ entities subsmap wf_pval₁
      simp only at h ; split at h <;> rename_i h'
      <;> simp only [Prod.mk.injEq] at h' <;> replace ⟨h', h''⟩ := h'
      · simp only [h', Except.error.injEq, forall_eq'] at hₑ
      · subst h' h''
        simp only [ih₁', h, Except.bind_err, Except.error.injEq, forall_eq'] at hₑ
  · rename_i hₑ'
    simp only [Prod.mk.injEq] at ih₁' ; replace ⟨ih₁', ih₁''⟩ := ih₁' ; subst ih₁' ih₁''
    simp only [← ih₁, bind_assoc]
    simp only [← ih₁, imp_false] at hₑ'
    cases hx₁ : Partial.evaluate x₁ req entities
    <;> simp only [hx₁, Except.bind_ok, Except.bind_err] at ih₁ hₑ'
    <;> simp only [Except.bind_ok, Except.bind_err]
    case ok pval₁ =>
      have wf₁ : pval₁.WellFormed := Evaluate.partial_eval_wf wf_r wf_e _ hx₁
      have h := ReevaluateUnaryApp.reeval_eqv_substituting_first op pval₁ entities subsmap wf₁
      simp only at h ; split at h <;> rename_i h'
      <;> simp only [Prod.mk.injEq] at h' <;> replace ⟨h', h''⟩ := h'
      · simp [h', h'', ← ih₁, hx₁] at hₑ
      · rename_i hₑ''
        subst h' h''
        cases h₁ : Partial.evaluateUnaryApp op pval₁ <;> simp [h₁] at *
        case error => simp [← h] at *
        case ok => simp only [h] at *


end Cedar.Thm.Partial.Evaluation.Reevaluation.Unary
