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

namespace Cedar.Thm.Partial.Evaluation.Reevaluation.AndOr

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Prim)

/--
  Inductive argument that re-evaluation of a `Spec.Expr.and` or
  `Spec.Expr.or` with a substitution on the residual expression, is
  equivalent to substituting first and then evaluating on the original
  `Spec.Expr.and` or `Spec.Expr.or`.
-/
theorem reeval_eqv_substituting_first {x₁ x₂ : Spec.Expr} {entities : Partial.Entities} {req req' : Partial.Request} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih₁ : ReevalEquivSubstFirst x₁ req req' entities subsmap)
  (ih₂ : ReevalEquivSubstFirst x₂ req req' entities subsmap) :
  ReevalEquivSubstFirst (Spec.Expr.and x₁ x₂) req req' entities subsmap ∧
  ReevalEquivSubstFirst (Spec.Expr.or x₁ x₂) req req' entities subsmap
:= by
  unfold ReevalEquivSubstFirst at *
  simp [Partial.evaluate]
  constructor <;> intro h_req
  <;> have wf_r' : req'.WellFormed := Subst.req_subst_preserves_wf wf_r wf_s h_req
  all_goals {
    specialize ih₁ h_req ; specialize ih₂ h_req
    split <;> try trivial
    rename_i hₑ h₁
    cases hx₁ : Partial.evaluate x₁ req entities
    <;> simp [hx₁] at ih₁ h₁ <;> simp [hx₁]
    <;> replace ⟨h₁, h₁'⟩ := h₁ <;> subst h₁ h₁'
    case error e₁ =>
      have ⟨e₁', hx₁'⟩ := Evaluate.subst_preserves_errors wf_r wf_e wf_s h_req hx₁
      simp only [hx₁', Except.error.injEq, Except.bind_err, imp_false, forall_apply_eq_imp_iff,
        forall_eq'] at ih₁ hₑ
    case ok pval₁ =>
      have wf₁ : pval₁.WellFormed := Evaluate.partial_eval_wf wf_r wf_e _ hx₁
      cases pval₁
      <;> simp only [bind_assoc, Except.bind_ok]
      <;> simp only [Partial.Value.WellFormed] at wf₁
      case value v₁ =>
        simp only [bind_assoc, imp_false] at hₑ
        split at ih₁ <;> rename_i ih₁'
        <;> simp only [Subst.subst_concrete_value, EvaluateValue.eval_spec_value v₁,
          Prod.mk.injEq, false_and] at ih₁'
        <;> replace ⟨ih₁', ih₁''⟩ := ih₁' <;> subst ih₁' ih₁''
        <;> simp only [← ih₁]
        <;> simp only [Subst.subst_concrete_value, EvaluateValue.eval_spec_value v₁,
          Except.bind_ok]
        <;> cases v₁
        <;> simp only [Spec.Value.asBool, Except.bind_err]
        <;> simp only [Spec.Value.asBool] at hₑ
        case prim p₁ _ =>
          cases p₁ <;> simp only [Except.bind_ok, Except.bind_err]
          case bool b₁ _ =>
            cases b₁ <;> simp only [Partial.Value.subst, Except.bind_ok, reduceIte, Bool.true_eq_false, Bool.false_eq_true, bind_assoc]
            all_goals try { simp [EvaluateValue.eval_spec_value] } -- this dispatches the `false` case for `and`, and the `true` case for `or`
            simp only at ih₂ <;> split at ih₂ <;> rename_i ih₂'
            <;> simp at ih₂' <;> replace ⟨ih₂', ih₂''⟩ := ih₂'
            <;> cases hx₂ : Partial.evaluate x₂ req entities
            <;> simp [hx₂] at ih₂ ih₂' hₑ
            <;> simp [ih₂'']
            <;> simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value] at ih₁
            <;> simp [← ih₁, ih₂''] at hₑ
            case h_1.ok pval₂ =>
              cases pval₂
              case value v₂ =>
                cases v₂ <;> simp
                case prim p₂ =>
                  cases p₂
                  case bool b₂ =>
                    simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value b₂] at ih₂'
                  all_goals simp [EvaluateValue.eval_spec_value false] at hₑ
                all_goals simp [EvaluateValue.eval_spec_value false] at hₑ
              case residual r₂ =>
                exfalso
                simp [Partial.Value.subst] at ih₂'
                simp [Partial.Value.subst, Partial.ResidualExpr.subst, EvaluateValue.eval_spec_value false] at hₑ
                simp [Partial.evaluateValue, Partial.evaluateResidual, Spec.Value.asBool] at hₑ
                simp [ih₂'] at hₑ
            case h_2.ok pval₂ =>
              subst ih₂' ih₂''
              cases pval₂ <;> simp
              case value v₂ hₑ' =>
                rw [Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req hx₂] at hₑ'
                simp at hₑ'
                simp [Subst.subst_concrete_value, EvaluateValue.eval_spec_value v₂] at ih₂
                simp [← ih₂]
                cases v₂
                case prim p₂ =>
                  cases p₂
                  case bool b₂ =>
                    simp only [Subst.subst_concrete_value, Except.bind_ok,
                      EvaluateValue.eval_spec_value b₂]
                  all_goals simp only [Except.bind_err]
                all_goals simp only [Except.bind_err]
              case residual r₂ =>
                simp [← ih₂, Partial.Value.subst, Partial.ResidualExpr.subst]
                conv => lhs ; simp [Partial.evaluateValue, Partial.evaluateResidual, Spec.Value.asBool]
            case error e₂ =>
              subst ih₂''
              simp [← ih₂, hx₂] at hₑ
      case residual r₁ =>
        simp only [Partial.Value.subst, Except.bind_ok, Partial.ResidualExpr.subst,
          Partial.evaluateValue, Partial.evaluateResidual, Bool.not_eq_true', imp_false] at *
        split at ih₁ <;> rename_i ih₁'
        <;> simp at ih₁' <;> replace ⟨ih₁', ih₁''⟩ := ih₁'
        · simp [ih₁', ih₁''] at hₑ
        · rename_i hₑ'
          subst ih₁' ih₁''
          simp only [ih₁] at hₑ
          cases hx₁' : Partial.evaluate x₁ req' (entities.subst subsmap)
          <;> simp only [Except.bind_ok, Except.bind_err] <;> simp [hx₁'] at ih₁ hₑ hₑ'
          case ok pv₁' =>
            simp [ih₁]
            cases pv₁' <;> simp only [Except.ok.injEq, Partial.Value.residual.injEq,
              Partial.ResidualExpr.and.injEq, Partial.ResidualExpr.or.injEq, true_and]
            case value v₁' =>
              cases hv₁' : v₁'.asBool <;> simp only [Except.bind_ok, Except.bind_err] <;> simp [hv₁'] at hₑ
              case ok b₁' =>
                cases b₁' <;> simp only [Bool.true_eq_false, Bool.false_eq_true, reduceIte]
                simp at hₑ
                split at ih₂ <;> rename_i ih₂'
                <;> simp at ih₂' <;> replace ⟨ih₂', ih₂''⟩ := ih₂'
                · simp [ih₂', ih₂''] at hₑ
                  simp [ih₂'']
                  cases h₁ : Partial.evaluateValue ((x₂.substToPartialValue req).subst subsmap) (entities.subst subsmap)
                  <;> simp [h₁] at hₑ
                  case ok pv₂ =>
                    exfalso -- h₁ and ih₂'' contradict
                    simp only [Subst.subst_substToPartialValue x₂ h_req] at h₁
                    simp only [← Evaluate.evaluate_eqv_evalValue_substToPartialValue _ _ wf_r', ih₂''] at h₁
                · rename_i hₑ''
                  subst ih₂' ih₂''
                  simp only [ih₂] at hₑ''
                  simp only [Subst.subst_substToPartialValue x₂ h_req]
                  simp only [Evaluate.evaluate_eqv_evalValue_substToPartialValue _ _ wf_r']
            case residual r₁' => exact Subst.subst_substToPartialValue x₂ h_req
  }

end Cedar.Thm.Partial.Evaluation.Reevaluation.AndOr
