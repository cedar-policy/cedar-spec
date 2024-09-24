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
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Subst

namespace Cedar.Thm.Partial.Evaluation.Reevaluation.Ite

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Prim)

/--
  Inductive argument that re-evaluation of a `Spec.Expr.ite` with a
  substitution on the residual expression, is equivalent to substituting first
  and then evaluating on the original `Spec.Expr.ite`.
-/
theorem reeval_eqv_substituting_first {x₁ x₂ x₃ : Spec.Expr} {entities : Partial.Entities} {req req' : Partial.Request} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih₁ : ReevalEquivSubstFirst x₁ req req' entities subsmap)
  (ih₂ : ReevalEquivSubstFirst x₂ req req' entities subsmap)
  (ih₃ : ReevalEquivSubstFirst x₃ req req' entities subsmap) :
  ReevalEquivSubstFirst (Spec.Expr.ite x₁ x₂ x₃) req req' entities subsmap
:= by
  unfold ReevalEquivSubstFirst at *
  simp only [Partial.evaluate, bind_assoc]
  intro h_req
  have wf_r' : req'.WellFormed := Subst.req_subst_preserves_wf wf_r wf_s h_req
  specialize ih₁ h_req ; specialize ih₂ h_req ; specialize ih₃ h_req
  split <;> try trivial
  rename_i hₑ h₁
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> simp [hx₁] at ih₁ h₁ <;> simp [hx₁]
  <;> replace ⟨h₁, h₁'⟩ := h₁ <;> subst h₁ h₁'
  case error e₁ =>
    have ⟨e₁', hx₁'⟩ := Evaluate.subst_preserves_errors wf_r wf_e wf_s h_req hx₁
    simp [hx₁, hx₁'] at hₑ
  case ok pval₁ =>
    have wf₁ : pval₁.WellFormed := Evaluate.partial_eval_wf wf_r wf_e _ hx₁
    cases pval₁
    <;> simp only [bind_assoc, Except.bind_ok]
    <;> simp only [Partial.Value.WellFormed] at wf₁
    case value v₁ =>
      simp at hₑ
      split at ih₁ <;> rename_i ih₁'
      <;> simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value v₁] at ih₁'
      <;> replace ⟨ih₁', ih₁''⟩ := ih₁' <;> subst ih₁' ih₁''
      <;> simp [← ih₁]
      <;> simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value v₁]
      <;> cases v₁
      <;> simp only [Spec.Value.asBool]
      <;> simp only [Spec.Value.asBool] at hₑ
      case prim p₁ _ =>
        cases p₁ <;> simp
        case bool b₁ _ =>
          simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value b₁] at ih₁
          cases hx₂ : Partial.evaluate x₂ req entities
          <;> cases hx₃ : Partial.evaluate x₃ req entities
          <;> simp [hx₂] at ih₂ hₑ
          <;> simp [hx₃] at ih₃ hₑ
          <;> cases b₁ <;> simp at hₑ
          -- in the following, case names are (x₂ evaluation result, x₃ evaluation result, b₁ value)
          case ok.ok.true pval₂ pval₃ _ | ok.error.true pval₂ e₃ _ =>
            have wf₂ : pval₂.WellFormed := Evaluate.partial_eval_wf wf_r wf_e _ hx₂
            cases pval₂ <;> simp <;> simp [Partial.Value.WellFormed] at wf₂
            case value v₂ =>
              split at ih₂ <;> rename_i ih₂'
              · simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value v₂] at ih₂'
              · simp at ih₂' ; replace ⟨ih₂', ih₂''⟩ := ih₂' ; subst ih₂' ih₂''
                simp [← ih₂]
            case residual r₂ =>
              split at ih₂ <;> rename_i ih₂'
              <;> simp at ih₂' <;> replace ⟨ih₂', ih₂''⟩ := ih₂'
              · rename_i e₂'' e₂'
                simp only [ih₂'']
                simp only [← ih₁, ih₂'', Except.bind_ok] at hₑ
                simp [Partial.Value.subst] at ih₂' hₑ
                simp [ih₂'] at hₑ
              · subst ih₂' ih₂''
                simp only [← ih₂]
          case ok.ok.false pval₂ pval₃ _ | error.ok.false e₂ pval₃ _ =>
            have wf₃ : pval₃.WellFormed := Evaluate.partial_eval_wf wf_r wf_e _ hx₃
            cases pval₃ <;> simp <;> simp [Partial.Value.WellFormed] at wf₃
            case value v₃ =>
              split at ih₃ <;> rename_i ih₃'
              · simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value v₃] at ih₃'
              · simp at ih₃' ; replace ⟨ih₃', ih₃''⟩ := ih₃' ; subst ih₃' ih₃''
                simp [← ih₃]
            case residual r₃ =>
              split at ih₃ <;> rename_i ih₃'
              <;> simp at ih₃' <;> replace ⟨ih₃', ih₃''⟩ := ih₃'
              · rename_i e₃'' e₃'
                simp only [ih₃'']
                simp only [← ih₁, ih₃'', Except.bind_ok] at hₑ
                simp [Partial.Value.subst] at ih₃' hₑ
                simp [ih₃'] at hₑ
              · subst ih₃' ih₃''
                simp only [← ih₃]
          case error.error.true e₂ e₃ _ | error.ok.true e₂ pval₃ _ =>
            split at ih₂ <;> rename_i ih₂'
            <;> simp at ih₂' <;> replace ⟨ih₂', ih₂''⟩ := ih₂'
            · rename_i e₂'' e₂'
              simp [← ih₁, ih₂'', Except.bind_ok] at hₑ
            · subst ih₂' ih₂''
              simp [← ih₁, ← ih₂, Except.bind_ok] at hₑ
          case error.error.false e₂ e₃ _ | ok.error.false pval₂ e₃ _ =>
            split at ih₃ <;> rename_i ih₃'
            <;> simp at ih₃' <;> replace ⟨ih₃', ih₃''⟩ := ih₃'
            · rename_i e₃'' e₃'
              simp [← ih₁, ih₃'', Except.bind_ok] at hₑ
            · subst ih₃' ih₃''
              simp [← ih₁, ← ih₃, Except.bind_ok] at hₑ
      all_goals simp only [Except.bind_err]
    case residual r₁ =>
      simp only [Partial.Value.subst, Except.bind_ok, Partial.ResidualExpr.subst,
        Partial.evaluateValue, Partial.evaluateResidual, imp_false] at *
      split at ih₁ <;> rename_i ih₁'
      <;> simp at ih₁' <;> replace ⟨ih₁', ih₁''⟩ := ih₁'
      · exfalso
        simp only [ih₁', Except.bind_err, Except.error.injEq, ih₁'', forall_apply_eq_imp_iff,
          imp_false, forall_eq'] at hₑ
      · subst ih₁' ih₁''
        simp only [ih₁]
        cases hx₁' : Partial.evaluate x₁ req' (entities.subst subsmap)
        <;> simp only [Except.bind_ok, Except.bind_err]
        case ok pv₁' =>
          cases pv₁' <;> simp only [Except.ok.injEq, Partial.Value.residual.injEq,
            Partial.ResidualExpr.ite.injEq, true_and]
          case residual r₁' =>
            exact And.intro (Subst.subst_substToPartialValue x₂ h_req) (Subst.subst_substToPartialValue x₃ h_req)
          case value v₁' =>
            rw [Subst.subst_substToPartialValue x₂ h_req]
            rw [Subst.subst_substToPartialValue x₃ h_req]
            cases v₁'.asBool <;> simp only [Except.bind_ok, Except.bind_err]
            case ok b₁' =>
              cases b₁' <;> simp only [Bool.false_eq_true, reduceIte]
              case true =>
                split at ih₂ <;> rename_i ih₂' <;> simp only [Prod.mk.injEq] at ih₂' <;> replace ⟨_, ih₂'⟩ := ih₂'
                · simp only [ih₂']
                  rw [Evaluate.evaluate_eqv_evalValue_substToPartialValue x₂ _ wf_r'] at ih₂'
                  exact ih₂'
                · exact (Evaluate.evaluate_eqv_evalValue_substToPartialValue x₂ _ wf_r').symm
              case false =>
                split at ih₃ <;> rename_i ih₃' <;> simp only [Prod.mk.injEq] at ih₃' <;> replace ⟨_, ih₃'⟩ := ih₃'
                · simp only [ih₃']
                  rw [Evaluate.evaluate_eqv_evalValue_substToPartialValue x₃ _ wf_r'] at ih₃'
                  exact ih₃'
                · exact (Evaluate.evaluate_eqv_evalValue_substToPartialValue x₃ _ wf_r').symm


end Cedar.Thm.Partial.Evaluation.Reevaluation.Ite
