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
import Cedar.Thm.Partial.Evaluation.EvaluateBinaryApp
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Reevaluation.Binary

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (BinaryOp Error)

/--
  Inductive argument that re-evaluation of a `Spec.Expr.binaryApp` with a
  substitution on the residual expression, is equivalent to substituting first
  and then evaluating on the original `Spec.Expr.binaryApp`.
-/
theorem reeval_eqv_substituting_first {x₁ x₂ : Spec.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih₁ : ReevalEquivSubstFirst x₁ req req' entities subsmap)
  (ih₂ : ReevalEquivSubstFirst x₂ req req' entities subsmap) :
  ReevalEquivSubstFirst (Spec.Expr.binaryApp op x₁ x₂) req req' entities subsmap
:= by
  unfold ReevalEquivSubstFirst at *
  simp only [Partial.evaluate]
  intro h_req ; specialize ih₁ h_req ; specialize ih₂ h_req
  simp only at ih₁ ih₂
  split <;> try trivial
  rename_i hₑ h₁
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> cases hx₂ : Partial.evaluate x₂ req entities
  <;> simp [hx₁] at ih₁ h₁
  <;> simp [hx₂] at ih₂ h₁
  <;> replace ⟨h₁, h₁'⟩ := h₁ <;> subst h₁ h₁'
  case error.error e₁ e₂ | error.ok e₁ pval₂ =>
    have ⟨e₁', hx₁'⟩ := Evaluate.subst_preserves_errors wf_r wf_e wf_s h_req hx₁
    simp [hx₁, hx₁'] at hₑ
  case ok.error pval₁ e₂ =>
    specialize hₑ e₂
    have ⟨e₂', hx₂'⟩ := Evaluate.subst_preserves_errors wf_r wf_e wf_s h_req hx₂
    simp only [hx₂', Except.bind_err, imp_false, true_implies] at hₑ
    cases hx₁' : Partial.evaluate x₁ req' (entities.subst subsmap)
    <;> simp [hx₁'] at hₑ
  case ok.ok pval₁ pval₂ =>
    simp only [Except.bind_ok]
    have wf₁ : pval₁.WellFormed := Evaluate.partial_eval_wf wf_r wf_e _ hx₁
    have wf₂ : pval₂.WellFormed := Evaluate.partial_eval_wf wf_r wf_e _ hx₂
    have h₁ := EvaluateBinaryApp.reeval_eqv_substituting_first op pval₁ pval₂ entities subsmap wf₁ wf₂
    split at ih₁ <;> rename_i ih₁'
    <;> simp only [Prod.mk.injEq] at ih₁' <;> replace ⟨ih₁', ih₁''⟩ := ih₁'
    <;> split at ih₂ <;> rename_i ih₂'
    <;> simp only [Prod.mk.injEq] at ih₂' <;> replace ⟨ih₂', ih₂''⟩ := ih₂'
    <;> simp only [ih₁'', ih₂'', Except.bind_err, Except.error.injEq, imp_false,
      forall_apply_eq_imp_iff] at hₑ
    <;> simp [ih₁, ih₁', ih₁'', ih₂, ih₂', ih₂''] at h₁
    · exfalso
      split at h₁ <;> rename_i h₁'
      <;> simp only [Prod.mk.injEq] at h₁' <;> replace ⟨h₁', h₁''⟩ := h₁'
      · rename_i e₁ e₂ _ e₃ e₄ _ e₅ e₆
        apply hₑ e₅ ; clear hₑ
        simp only [h₁', Except.error.injEq, forall_eq']
      · rename_i hₑ'
        subst h₁' h₁''
        simp only [h₁, Except.error.injEq, imp_false, forall_apply_eq_imp_iff, forall_eq'] at hₑ'
    · exfalso
      split at h₁ <;> rename_i h₁'
      <;> simp only [Prod.mk.injEq] at h₁' <;> replace ⟨h₁', h₁''⟩ := h₁'
      · simp [h₁'] at hₑ
      · subst ih₂' ih₂'' h₁' h₁''
        rename_i hₑ'
        simp [h₁] at hₑ'
    · exfalso
      subst ih₁' ih₁''
      split at h₁ <;> rename_i h₁'
      <;> simp only [Prod.mk.injEq] at h₁' <;> replace ⟨h₁', h₁''⟩ := h₁'
      · rename_i e₁ e₂ _ _ e₃ e₄
        specialize hₑ e₃
        simp only [h₁', true_implies] at hₑ
        cases h₂ : Partial.evaluate x₁ req' (entities.subst subsmap)
        <;> simp only [h₂, Except.bind_ok, Except.bind_err, Except.error.injEq, forall_eq'] at h₁'' hₑ
      · subst h₁' h₁''
        rename_i e₁ e₂ _ _ hₑ'
        cases h₂ : Partial.evaluate x₁ req' (entities.subst subsmap)
        <;> simp only [h₂, Except.bind_ok, Except.bind_err, Except.error.injEq, imp_false,
          forall_apply_eq_imp_iff] at ih₁ h₁ hₑ'
        case error e₃ =>
          specialize hₑ' e₃
          simp only [h₁, not_true_eq_false] at hₑ'
        case ok pv =>
          simp only [h₁, Except.error.injEq, forall_eq'] at hₑ'
    · subst ih₁' ih₁'' ih₂' ih₂''
      simp only [imp_false, ih₁, h₁, ih₂] at *


end Cedar.Thm.Partial.Evaluation.Reevaluation.Binary
