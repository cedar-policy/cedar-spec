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
import Cedar.Thm.Partial.Evaluation.EvaluateGetAttr
import Cedar.Thm.Partial.Evaluation.ReevaluateGetAttr
import Cedar.Thm.Partial.Evaluation.ReevaluateValue
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Reevaluation.GetAttr

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr EntityUID Error Prim)

/--
  Inductive argument that re-evaluation of a `Spec.Expr.getAttr` with a
  substitution on the residual expression, is equivalent to substituting first
  and then evaluating on the original `Spec.Expr.getAttr`.
-/
theorem reeval_eqv_substituting_first {x₁ : Spec.Expr} {attr : Attr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih₁ : ReevalEquivSubstFirst x₁ req req' entities subsmap) :
  ReevalEquivSubstFirst (Spec.Expr.getAttr x₁ attr) req req' entities subsmap
:= by
  unfold ReevalEquivSubstFirst at *
  simp only [Partial.evaluate]
  split <;> try simp only [implies_true]
  rename_i hₑ h₁
  simp at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
  intro h_req ; specialize ih₁ h_req
  simp only at ih₁
  split at ih₁ <;> rename_i ih₁'
  <;> simp at ih₁' <;> replace ⟨ih₁', ih₁''⟩ := ih₁'
  <;> simp [ih₁'']
  · -- the case where ih₁' and ih₁'' tell us they're both errors
    exfalso
    rename_i e e'
    simp [ih₁''] at hₑ
    cases hx₁ : Partial.evaluate x₁ req entities <;> simp [hx₁] at hₑ ih₁'
    case ok pval₁ =>
      have wf₁ : pval₁.WellFormed := Evaluate.partial_eval_wf wf_r wf_e pval₁ hx₁
      have h₁ := ReevaluateGetAttr.reeval_eqv_substituting_first pval₁ attr wf_e wf_s wf₁
      simp only at h₁ ; split at h₁ <;> rename_i h₁'
      <;> simp only [Prod.mk.injEq] at h₁' <;> replace ⟨h₁', h₁''⟩ := h₁'
      · simp only [h₁', Except.error.injEq, forall_eq'] at hₑ
      · rename_i hₑ'
        subst h₁' h₁''
        simp only [ih₁', Except.bind_err, Except.error.injEq, imp_false, forall_apply_eq_imp_iff] at hₑ'
        simp only [ih₁', Except.bind_err] at h₁
        apply hₑ' e ; clear hₑ'
        apply h₁ ; clear h₁
        intro v pv pv' wf_v h₁ h₂
        apply ReevaluateValue.reeval_eqv_substituting_first _ wf_e wf_s h₂
        exact EvaluateGetAttr.getAttr_wf wf_v wf_e _ h₁
  · rename_i hₑ' -- the case where hₑ' tells us they're not both errors
    subst ih₁' ih₁''
    cases hx₁ : Partial.evaluate x₁ req entities
    case error e₁ =>
      have ⟨e₁', hx₁'⟩ := Evaluate.subst_preserves_errors wf_r wf_e wf_s h_req hx₁
      simp [hx₁, hx₁'] at hₑ
    case ok pval₁ =>
      have wf₁ : pval₁.WellFormed := Evaluate.partial_eval_wf wf_r wf_e pval₁ hx₁
      simp only [Except.bind_ok]
      have h₁ := ReevaluateGetAttr.reeval_eqv_substituting_first pval₁ attr wf_e wf_s wf₁
      simp only at h₁ ; split at h₁ <;> rename_i h₁'
      <;> simp only [Prod.mk.injEq] at h₁' <;> replace ⟨h₁', h₁''⟩ := h₁'
      · exfalso
        simp only [hx₁, Except.bind_ok] at ih₁ hₑ hₑ'
        simp only [ih₁] at hₑ' h₁''
        cases h₂ : Partial.evaluate x₁ req' (entities.subst subsmap)
        <;> simp only [h₂, Except.bind_ok, Except.bind_err] at *
        case error e => exact hₑ' e e rfl rfl
        case ok x₁' =>
          simp only [h₁'', Except.error.injEq, forall_apply_eq_imp_iff] at hₑ
          cases h₃ : Partial.evaluateGetAttr pval₁ attr entities
          <;> simp only [h₃, Except.bind_ok, Except.bind_err] at *
          case error e => exact hₑ e rfl
          case ok pval₁' => simp only [h₁', Except.error.injEq, imp_false, forall_eq'] at hₑ
      · rename_i hₑ''
        subst h₁' h₁''
        simp only [← ih₁] at *
        simp only [hx₁, Except.bind_ok]
        apply h₁ ; clear h₁
        intro v pv pv' wf_v h₁ h₂
        apply ReevaluateValue.reeval_eqv_substituting_first _ wf_e wf_s h₂
        exact EvaluateGetAttr.getAttr_wf wf_v wf_e _ h₁


end Cedar.Thm.Partial.Evaluation.Reevaluation.GetAttr
