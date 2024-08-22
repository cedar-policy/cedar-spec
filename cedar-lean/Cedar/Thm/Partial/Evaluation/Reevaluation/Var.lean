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
import Cedar.Thm.Data.Control
import Cedar.Thm.Partial.Evaluation.Evaluate
import Cedar.Thm.Partial.Evaluation.Evaluate.Var
import Cedar.Thm.Partial.Evaluation.ReevaluateValue
import Cedar.Thm.Partial.WellFormed
import Cedar.Thm.Partial.Subst

namespace Cedar.Thm.Partial.Evaluation.Reevaluation.Var

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr Error Result Var)

theorem do_error {res : Result α} {e : Error} {f : α → β} :
  (do let v ← res ; .ok (f v)) = .error e →
  res = .error e
:= by cases res <;> simp

/--
  If `Partial.evaluateVar` returns a residual, re-evaluating that residual with
  a substitution on `req`, is equivalent to substituting first, evaluating the
  context values if the var is `context`, and then calling `Partial.evaluateVar`
  on the substituted/evaluated request
-/
theorem reeval_eqv_substituting_first_evaluateVar (var : Var) (entities : Partial.Entities) {req req' : Partial.Request} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  let re_evaluated := Partial.evaluateVar var req entities >>= λ residual => Partial.evaluateValue (residual.subst subsmap) (entities.subst subsmap)
  let subst_first := Partial.evaluateVar var req' (entities.subst subsmap)
  match (re_evaluated, subst_first) with
  | (Except.error _, Except.error _) => true -- don't require that the errors are equal
  | (_, _) => re_evaluated = subst_first
:= by
  intro h_req
  cases h_var : Partial.evaluateVar var req entities
  case error e =>
    cases var <;> simp at *
    case principal | action | resource => split <;> trivial
    case context =>
      split <;> try { trivial }
      rename_i hₑ h₁
      simp only [Prod.mk.injEq] at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
      have ⟨e', h₁⟩ := Evaluate.Var.subst_preserves_evaluateVar_to_error wf_r wf_e wf_s h_req h_var
      simp only [h₁, Except.error.injEq, imp_false, forall_apply_eq_imp_iff, forall_eq'] at hₑ
  case ok pval =>
    unfold Partial.evaluateVar at *
    cases var <;> simp at *
    case principal =>
      subst pval
      cases h₁ : req.principal <;> simp
      case known uid =>
        simp only [Subst.subst_concrete_value, EvaluateValue.eval_spec_value, Except.ok.injEq]
        rw [Subst.req_subst_preserves_known_principal h₁ h_req]
      case unknown u =>
        simp only [Partial.Request.subst, Partial.UidOrUnknown.subst, h₁, Option.bind_eq_bind,
          Option.bind_eq_some, Option.some.injEq] at h_req
        replace ⟨p, h_p, a, h_a, r, h_r, h_req⟩ := h_req
        subst req'
        simp only
        split at h_p <;> simp at h_p <;> subst p <;> rename_i h_subs
        <;> simp only [Partial.Value.subst, Partial.ResidualExpr.subst, h_subs]
        · simp only [EvaluateValue.eval_spec_value]
        · simp only [Partial.evaluateValue, Partial.evaluateResidual]
        · simp only [Partial.evaluateValue, Partial.evaluateResidual]
    case action =>
      subst pval
      cases h₁ : req.action <;> simp
      case known uid =>
        simp only [Subst.subst_concrete_value, EvaluateValue.eval_spec_value, Except.ok.injEq]
        rw [Subst.req_subst_preserves_known_action h₁ h_req]
      case unknown u =>
        simp only [Partial.Request.subst, Partial.UidOrUnknown.subst, h₁, Option.bind_eq_bind,
          Option.bind_eq_some, Option.some.injEq] at h_req
        replace ⟨p, h_p, a, h_a, r, h_r, h_req⟩ := h_req
        subst req'
        simp only
        split at h_a <;> simp at h_a <;> subst a <;> rename_i h_subs
        <;> simp only [Partial.Value.subst, Partial.ResidualExpr.subst, h_subs]
        · simp only [EvaluateValue.eval_spec_value]
        · simp only [Partial.evaluateValue, Partial.evaluateResidual]
        · simp only [Partial.evaluateValue, Partial.evaluateResidual]
    case resource =>
      subst pval
      cases h₁ : req.resource <;> simp
      case known uid =>
        simp only [Subst.subst_concrete_value, EvaluateValue.eval_spec_value, Except.ok.injEq]
        rw [Subst.req_subst_preserves_known_resource h₁ h_req]
      case unknown u =>
        simp only [Partial.Request.subst, Partial.UidOrUnknown.subst, h₁, Option.bind_eq_bind,
          Option.bind_eq_some, Option.some.injEq] at h_req
        replace ⟨p, h_p, a, h_a, r, h_r, h_req⟩ := h_req
        subst req'
        simp only
        split at h_r <;> simp at h_r <;> subst r <;> rename_i h_subs
        <;> simp only [Partial.Value.subst, Partial.ResidualExpr.subst, h_subs]
        · simp only [EvaluateValue.eval_spec_value]
        · simp only [Partial.evaluateValue, Partial.evaluateResidual]
        · simp only [Partial.evaluateValue, Partial.evaluateResidual]
    case context =>
      simp only [Partial.Request.subst, Option.bind_eq_bind, Option.bind_eq_some,
        Option.some.injEq] at h_req
      replace ⟨p, h_p, a, h_a, r, h_r, h_req⟩ := h_req ; subst req' ; simp only
      simp only [Map.mapMOnValues_mapOnValues]
      split <;> try { trivial }
      rename_i hₑ h₁
      simp only [Prod.mk.injEq] at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
      cases h₁ : Partial.evaluateValue (pval.subst subsmap) (entities.subst subsmap)
      <;> simp only [h₁, imp_false, false_implies, implies_true] at hₑ
      case error e' =>
        exfalso
        specialize hₑ e' ; simp only [true_implies] at hₑ
        cases h₂ : req.context.mapMOnValues (Partial.evaluateValue · entities)
        <;> simp only [h₂, Except.bind_ok, Except.bind_err] at h_var
        case ok apvs =>
          split at h_var <;> simp only [Except.ok.injEq] at h_var <;> subst pval <;> rename_i hapvs
          · simp only [Subst.subst_concrete_value, EvaluateValue.eval_spec_value] at h₁
          · simp only [Partial.Value.subst, Partial.ResidualExpr.subst, List.map_attach₂_snd,
              Partial.evaluateValue, Partial.evaluateResidual,
              Evaluate.Record.mapM₂_eq_mapM_partial_bindAttr (Partial.evaluateValue · (entities.subst subsmap)),
              List.mapM_map] at h₁
            suffices ∃ e, (req.context.mapMOnValues λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)) = .error e by
              replace ⟨e, this⟩ := this
              simp only [this, Except.bind_err, Except.error.injEq, forall_eq'] at hₑ
            clear hₑ
            have h₃ : (apvs.kvs.mapM λ apv => Partial.bindAttr apv.fst (Partial.evaluateValue (apv.snd.subst subsmap) (entities.subst subsmap))) = .error e' := by
              cases h₃ : apvs.kvs.mapM λ apv => Partial.bindAttr apv.fst (Partial.evaluateValue (apv.snd.subst subsmap) (entities.subst subsmap))
              <;> simp only [h₃, Except.bind_ok, Except.bind_err, Except.error.injEq] at h₁
              case error => subst e' ; rfl
              case ok => split at h₁ <;> simp only at h₁
            clear h₁ -- h₃ is a more concise statement of h₁
            replace ⟨(a, pv'), hpv', h₃⟩ := List.mapM_error_implies_exists_error h₃
            simp only [Partial.bindAttr] at h₃
            replace h₃ := do_error h₃
            replace ⟨pv, hpv, h₂⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₂ (a, pv') hpv'
            simp only at *
            apply Map.element_error_implies_mapMOnValues_error (Map.in_list_in_values hpv) (e := e')
            have wf_pv : pv.WellFormed := wf_r.right pv (Map.in_list_in_values hpv)
            simp only [ReevaluateValue.reeval_eqv_substituting_first wf_pv wf_e wf_s h₂] at h₃
            exact h₃
      case ok pval' =>
        cases h₂ : req.context.mapMOnValues (Partial.evaluateValue · entities)
        <;> simp only [h₂, Except.bind_ok, Except.bind_err] at h_var
        case ok apvs =>
          split at h_var <;> simp only [Except.ok.injEq] at h_var <;> subst pval <;> rename_i hapvs
          · rename_i avs
            -- in this branch, `apvs` is all-concrete (`avs` is its pure-concrete representation)
            simp only [Subst.subst_concrete_value, EvaluateValue.eval_spec_value,
              Except.ok.injEq] at h₁ ; subst pval'
            cases h₃ : req.context.mapMOnValues λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)
            case error e =>
              exfalso
              replace ⟨pv, hpv, h₃⟩ := Map.mapMOnValues_error_implies_exists_error h₃
              replace ⟨a, hpv⟩ := Map.in_values_exists_key hpv
              replace ⟨pv', hpv', h₂⟩ := Map.mapMOnValues_ok_implies_all_ok h₂ (a, pv) hpv
              replace ⟨v', hv', hapvs⟩ := Map.mapMOnValues_some_implies_all_some hapvs (a, pv') hpv'
              simp only at *
              split at hapvs <;> simp only [Option.some.injEq] at hapvs ; subst v' ; rename_i v
              have wf_pv : pv.WellFormed := wf_r.right pv (Map.in_list_in_values hpv)
              simp only [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_pv wf_e h₂] at h₃
            case ok apvs' =>
              simp only [Except.bind_ok]
              split <;> rename_i hapvs'
              <;> simp only [Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.record.injEq]
              · rename_i avs'
                apply (Map.eq_iff_kvs_equiv _ _).mp
                · simp only [List.Equiv, List.subset_def]
                  and_intros <;> intro (a, v) hv
                  · replace ⟨pv', hpv', hapvs⟩ := Map.mapMOnValues_some_implies_all_from_some hapvs (a, v) hv
                    split at hapvs <;> simp only [Option.some.injEq] at hapvs ; subst v ; rename_i v
                    replace ⟨pv, hpv, h₂⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₂ (a, v) hpv'
                    have hv' := hpv' ; clear hpv'
                    replace ⟨pv', hpv', h₃⟩ := Map.mapMOnValues_ok_implies_all_ok h₃ (a, pv) hpv
                    replace ⟨v', hv'', hapvs'⟩ := Map.mapMOnValues_some_implies_all_some hapvs' (a, pv') hpv'
                    split at hapvs' <;> simp only [Option.some.injEq] at hapvs' ; subst v' ; rename_i v' hpv''
                    simp only at *
                    subst pv'
                    have wf_pv : pv.WellFormed := wf_r.right pv (Map.in_list_in_values hpv)
                    simp only [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_pv wf_e h₂,
                      Except.ok.injEq, Partial.Value.value.injEq] at h₃
                    subst v'
                    exact hv''
                  · replace ⟨pv', hpv', hapvs'⟩ := Map.mapMOnValues_some_implies_all_from_some hapvs' (a, v) hv
                    split at hapvs' <;> simp only [Option.some.injEq] at hapvs' ; subst v ; rename_i v
                    replace ⟨pv, hpv, h₃⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₃ (a, v) hpv'
                    replace ⟨pv', hpv'', h₂⟩ := Map.mapMOnValues_ok_implies_all_ok h₂ (a, pv) hpv
                    replace ⟨v', hv', hapvs⟩ := Map.mapMOnValues_some_implies_all_some hapvs (a, pv') hpv''
                    split at hapvs <;> simp only [Option.some.injEq] at hapvs ; subst v' ; rename_i v' hv''
                    simp only at *
                    subst pv'
                    have wf_pv : pv.WellFormed := wf_r.right pv (Map.in_list_in_values hpv)
                    simp only [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_pv wf_e h₂,
                      Except.ok.injEq, Partial.Value.value.injEq] at h₃
                    subst v'
                    exact hv'
                · apply Map.mapMOnValues_some_wf _ hapvs
                  apply Map.mapMOnValues_ok_wf _ h₂
                  exact wf_r.left
                · apply Map.mapMOnValues_some_wf _ hapvs'
                  apply Map.mapMOnValues_ok_wf _ h₃
                  exact wf_r.left
              · replace ⟨pv', hpv', hapvs'⟩ := Map.mapMOnValues_none_iff_exists_none.mp hapvs'
                split at hapvs' <;> simp only at hapvs' ; rename_i r
                replace ⟨a, hpv'⟩ := Map.in_values_exists_key hpv'
                replace ⟨pv, hpv, h₃⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₃ (a, .residual r) hpv'
                replace ⟨pv', hpv'', h₂⟩ := Map.mapMOnValues_ok_implies_all_ok h₂ (a, pv) hpv
                replace ⟨v', hv', hapvs⟩ := Map.mapMOnValues_some_implies_all_some hapvs (a, pv') hpv''
                split at hapvs <;> simp only [Option.some.injEq] at hapvs ; subst v' ; rename_i v' hv
                simp only at *
                subst pv'
                have wf_pv : pv.WellFormed := wf_r.right pv (Map.in_list_in_values hpv)
                simp only [EvaluateValue.subst_preserves_evaluation_to_value subsmap wf_pv wf_e h₂,
                  Except.ok.injEq] at h₃
          · -- in this branch, `apvs` contains at least one residual
            -- re-evaluated produced `pval'`; the first evaluation produced `.residual (.record apvs.kvs)`,
            -- which is why `h₁` looks how it does
            replace ⟨pv', hpv', hapvs⟩ := Map.mapMOnValues_none_iff_exists_none.mp hapvs
            split at hapvs <;> simp only at hapvs ; rename_i r
            replace ⟨a, hpv'⟩ := Map.in_values_exists_key hpv'
            have ⟨pv, hpv, h₄⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₂ (a, .residual r) hpv'
            simp only at *
            simp only [Partial.Value.subst, Partial.ResidualExpr.subst, List.map_attach₂_snd,
              Partial.evaluateValue, Partial.evaluateResidual,
              Evaluate.Record.mapM₂_eq_mapM_partial_bindAttr (Partial.evaluateValue · (entities.subst subsmap)),
              List.mapM_map] at h₁
            cases h₃ : apvs.kvs.mapM λ apv => Partial.bindAttr apv.fst (Partial.evaluateValue (apv.snd.subst subsmap) (entities.subst subsmap))
            <;> simp only [h₃, Except.bind_ok, Except.bind_err] at h₁
            case ok apvs' =>
              split at h₁ <;> rename_i hapvs' <;> simp only [Except.ok.injEq] at h₁ <;> subst pval'
              · rename_i avs'
                -- re-evaluated produced a concrete value, `.value (.record (Map.make avs'))`
                cases h₅ : req.context.mapMOnValues λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)
                <;> simp
                case error e =>
                  replace ⟨pv', hpv'', h₅⟩ := Map.mapMOnValues_error_implies_exists_error h₅
                  replace ⟨a, hpv''⟩ := Map.in_values_exists_key hpv''
                  replace ⟨pv'', hpv''', h₂⟩ := Map.mapMOnValues_ok_implies_all_ok h₂ (a, pv') hpv''
                  simp only at *
                  replace ⟨(a', pv'''), hpv'''', h₃⟩ := List.mapM_ok_implies_all_ok h₃ (a, pv'') hpv'''
                  simp [Partial.bindAttr, do_ok] at h₃
                  replace ⟨h₃, h₃'⟩ := h₃ ; subst a'
                  sorry
                case ok apvs'' =>
                  split <;> rename_i h₆ <;> simp
                  · rename_i avs''
                    sorry
                  · replace ⟨pv', hpv'', h₆⟩ := Map.mapMOnValues_none_iff_exists_none.mp h₆
                    split at h₆ <;> simp at h₆ ; rename_i r'
                    -- I think the contradiction requires h₂ / h₃ / hapvs' / h₅ / hpv''
                    sorry
              · -- re-evaluated produced a residual, `.residual (.record apvs')`
                replace ⟨(a', pv'), hpv', hapvs'⟩ := List.mapM_none_iff_exists_none.mp hapvs'
                split at hapvs' <;> simp only at hapvs' ; rename_i r' _
                simp only at * ; subst pv'
                have ⟨(a'', pv''), hpv'', h₃'⟩ := List.mapM_ok_implies_all_from_ok h₃ (a', .residual r') hpv'
                simp only [Partial.bindAttr, do_ok, Prod.mk.injEq, exists_eq_right_right] at h₃'
                replace ⟨h₃', h₃''⟩ := h₃' ; subst a''
                cases h₅ : req.context.mapMOnValues λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)
                <;> simp only [Except.bind_ok, Except.bind_err]
                case error e =>
                  -- subst_first produced an error because one of its `evaluateValue` calls did
                  replace ⟨pvₑ, hpvₑ, h₅⟩ := Map.mapMOnValues_error_implies_exists_error h₅
                  have wf_pvₑ : pvₑ.WellFormed := wf_r.right pvₑ hpvₑ
                  replace ⟨a'', hpvₑ⟩ := Map.in_values_exists_key hpvₑ
                  replace ⟨pv''', hpv''', h₂⟩ := Map.mapMOnValues_ok_implies_all_ok h₂ (a'', pvₑ) hpvₑ
                  simp only at *
                  replace ⟨(a''', pv''''), hpv'''', h₃⟩ := List.mapM_ok_implies_all_ok h₃ (a'', pv''') hpv'''
                  simp only [Partial.bindAttr] at h₃
                  replace ⟨pv'''', h₃, h_tmp⟩ := do_ok.mp h₃
                  simp only [Prod.mk.injEq] at h_tmp ; replace ⟨h_tmp, h_tmp'⟩ := h_tmp; subst h_tmp h_tmp'
                  simp [ReevaluateValue.reeval_eqv_substituting_first wf_pvₑ wf_e wf_s h₂] at h₃
                  simp [h₃] at h₅
                case ok apvs'' =>
                  split <;> rename_i h₆
                  <;> simp only [Except.ok.injEq, Partial.Value.residual.injEq, Partial.ResidualExpr.record.injEq]
                  · rename_i avs''
                    -- subst_first produced a concrete value, `.value (.record avs'')`
                    replace ⟨pv', hpv''', h₂⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₂ (a', pv'') hpv''
                    simp only at *
                    have wf_pv' : pv'.WellFormed := wf_r.right pv' (Map.in_list_in_values hpv''')
                    simp only [ReevaluateValue.reeval_eqv_substituting_first wf_pv' wf_e wf_s h₂] at h₃'
                    replace ⟨pv'''', hpv'''', h₅⟩ := Map.mapMOnValues_ok_implies_all_ok h₅ (a', pv') hpv'''
                    simp [h₃'] at h₅ ; subst pv''''
                    simp only at *
                    replace h₆ := Map.mapMOnValues_some_implies_all_some h₆ (a', .residual r') hpv''''
                    simp at h₆
                  · -- subst_first produced a residual, `.residual (.record apvs''.kvs)`
                    -- Need to show it's equal to the residual re-evaluated produced
                    sorry

/--
  Re-evaluation with a substitution on the residual expression, is equivalent to
  substituting first and then evaluating on the original expression.
-/
theorem reeval_eqv_substituting_first (var : Var) (req req' : Partial.Request) (entities : Partial.Entities) (subsmap : Subsmap)
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  ReevalEquivSubstFirst (Spec.Expr.var var) req req' entities subsmap
:= by
  unfold ReevalEquivSubstFirst
  simp only [Partial.evaluate]
  intro h_req
  have h₁ := reeval_eqv_substituting_first_evaluateVar var entities wf_r wf_e wf_s h_req
  simp only at h₁ ; exact h₁


end Cedar.Thm.Partial.Evaluation.Reevaluation.Var
