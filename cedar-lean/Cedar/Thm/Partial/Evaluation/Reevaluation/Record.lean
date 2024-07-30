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
import Cedar.Thm.Partial.Evaluation.Evaluate.Lemmas
import Cedar.Thm.Partial.Evaluation.Evaluate.Record
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Reevaluation.Record

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr Error Prim Result)

/--
  If evaluating any value in a `Partial.Value.record` produces an error, then
  evaluating the whole `Partial.Value.record` must also produce an error (not
  necessarily the same error)
-/
theorem element_error_implies_record_error {k : Attr} {pv : Partial.Value} {attrs : List (Attr × Partial.Value)} {entities : Partial.Entities} {e : Error} :
  (k, pv) ∈ attrs →
  Partial.evaluateValue pv entities = .error e →
  ∃ e', Partial.evaluateValue (.residual (.record attrs)) entities = .error e'
:= by
  intro h₁ h₂
  simp only [Partial.evaluateValue, Partial.evaluateResidual,
    Evaluate.Record.mapM₂_eq_mapM_partial_bindAttr (Partial.evaluateValue · entities)]
  cases h₃ : attrs.mapM (λ kv => Partial.bindAttr kv.fst (Partial.evaluateValue kv.snd entities))
  <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq']
  case ok pvals =>
    replace ⟨pval, _, h₃⟩ := List.mapM_ok_implies_all_ok h₃ (k, pv) h₁
    simp [h₂, Partial.bindAttr] at h₃

/--
  small lemma that we want to prove by induction, which is easier if we factor
  it out and name it like this
-/
theorem commute_prod_snd {kvs : List (α × Partial.Value)} {kvs' : List (α × Spec.Value)}:
  kvs.mapM (λ kv => match kv.snd with
      | .value v => some (kv.fst, v)
      | .residual _ => none)
    = some kvs' →
  kvs.mapM (λ kv => match kv.snd with
      | .value v => some v
      | .residual _ => none)
    = some (List.map Prod.snd kvs')
:= match kvs with
  | [] => by simp ; intro h ; subst h ; simp
  | (khd, vhd) :: tl => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
      Option.some.injEq, forall_exists_index, and_imp]
    split
    · simp only [Option.some.injEq, exists_eq_left', forall_eq']
      intro tl' htl' _ ; subst kvs'
      exists (tl'.map Prod.snd)
      simp only [commute_prod_snd htl', List.map_cons, and_self]
    · simp only [false_and, exists_const, imp_false, false_implies, implies_true]

/--
  Basically a statement of `ReevalEquivSubstFirst`, but for
  `mapM Partial.bindAttr . (Partial.evaluate .)` instead of raw `Partial.evaluate`
-/
-- Shares a lot of code and structure with the theorem of the same name in Partial/Reevaluation/Set.lean
theorem mapM_reeval_eqv_substituting_first {attrs : List (Attr × Spec.Expr)} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih : ∀ kv ∈ attrs, ReevalEquivSubstFirst kv.snd req req' entities subsmap) :
  req.subst subsmap = some req' →
  let re_evaluated := attrs.mapM (λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req entities)) >>= λ residuals => residuals.mapM (λ kv => Partial.bindAttr kv.fst (Partial.evaluateValue (kv.snd.subst subsmap) (entities.subst subsmap)))
  let subst_first := attrs.mapM (λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req' (entities.subst subsmap)))
  match (re_evaluated, subst_first) with
  | (Except.error _, Except.error _) => true -- don't require that the errors are equal
  | (_, _) => re_evaluated = subst_first
:= by
  simp only
  split
  · simp only [implies_true]
  · rename_i hₑ h₁
    simp at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
    cases hattrs : attrs.mapM λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req entities)
    <;> simp [hattrs] at hₑ <;> simp [hattrs]
    <;> cases hattrs' : attrs.mapM λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req' (entities.subst subsmap))
    <;> simp [hattrs'] at hₑ
    case error.ok e pvals =>
      intro h_req
      exfalso
      replace ⟨(k, x), hx, hattrs⟩ := List.mapM_error_implies_exists_error hattrs
      simp only [Partial.bindAttr] at hattrs
      rw [do_error] at hattrs
      replace ⟨pval, _, hattrs'⟩ := List.mapM_ok_implies_all_ok hattrs' (k, x) hx
      have ⟨e', hattrs''⟩ := Evaluate.subst_preserves_errors wf_r wf_e wf_s h_req hattrs
      simp [Partial.bindAttr, hattrs''] at hattrs'
    case ok.error pvals e =>
      -- evaluating `attrs` before substitution produced residuals, but after
      -- substitution, one of them produced the error `e`
      replace ⟨(k, x), hx, hattrs'⟩ := List.mapM_error_implies_exists_error hattrs'
      simp only [Partial.bindAttr] at hattrs'
      rw [do_error] at hattrs'
      -- `x` is the input expression that produced error `e` after substitution
      exact match h₁ : Partial.evaluate x req entities with
      | .error e' => by
        replace ⟨(k', pval), _, hattrs⟩ := List.mapM_ok_implies_all_ok hattrs (k, x) hx
        simp [Partial.bindAttr, h₁] at hattrs
      | .ok pv => by
        intro h_req
        cases pv
        case value v =>
          simp [Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req h₁] at hattrs'
        case residual r =>
          specialize ih (k, x) hx h_req
          simp [h₁] at ih
          split at ih <;> rename_i ih'
          <;> simp at ih' <;> replace ⟨ih', ih''⟩ := ih'
          · rename_i e' e''
            simp [hattrs'] at ih'' ; subst e''
            suffices ∃ e, pvals.mapM (λ kv => Partial.bindAttr kv.fst (Partial.evaluateValue (kv.snd.subst subsmap) (entities.subst subsmap))) = .error e by
              replace ⟨e, this⟩ := this
              exfalso ; exact hₑ e this
            clear hₑ
            apply List.element_error_implies_mapM_error (x := (k, .residual r)) (e := e')
            · replace ⟨(k', pval), h₃, hattrs⟩ := List.mapM_ok_implies_all_ok hattrs (k, x) hx
              simp only [Partial.bindAttr] at hattrs
              replace ⟨pval', hattrs, hattrs'⟩ := do_ok.mp hattrs
              simp only [Prod.mk.injEq] at hattrs' ; replace ⟨hattrs', hattrs''⟩ := hattrs' ; subst k' pval'
              simp [hattrs] at h₁ ; subst h₁
              exact h₃
            · simp [Partial.bindAttr, ih']
          · rename_i hₑ'
            subst ih' ih''
            simp [hattrs', ih] at ih hₑ'
    case ok.ok pvals pvals' =>
      -- evaluating `attrs` before substitution produced `pvals`, and after
      -- substitution, produced `pvals'`
      intro h_req
      -- we proceed by induction on `attrs`
      cases attrs <;> simp [pure, Except.pure] at *
      case nil => subst pvals pvals' ; simp [pure, Except.pure]
      case cons hd tl =>
        have (khd, vhd) := hd ; clear hd
        have ⟨ih_hd, ih_tl⟩ := ih ; clear ih
        have ih := mapM_reeval_eqv_substituting_first wf_r wf_e wf_s ih_tl h_req
        -- the plan is to use `ih_hd` to dispatch the `hd`-related obligations,
        -- and `ih` (not `ih_tl`) to dispatch the `tl`-related obligations
        specialize ih_hd h_req
        simp at ih_hd ; split at ih_hd <;> rename_i ih_hd'
        · rename_i e e'
          cases hhd : Partial.evaluate vhd req entities
          <;> simp [hhd] at ih_hd' hattrs
          case ok hd_pval =>
            cases htl : tl.mapM λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req entities)
            <;> simp only [htl, Except.bind_ok, Except.bind_err] at hattrs
            <;> simp only [Partial.bindAttr, Except.bind_ok, Except.ok.injEq] at hattrs
            case ok tl_pvals =>
              subst pvals
              simp [Partial.bindAttr, ih_hd'] at hattrs'
          case error e'' =>
            cases htl : tl.mapM λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req entities)
            <;> simp only [htl, Except.bind_ok, Except.bind_err] at hattrs
            <;> simp only [Partial.bindAttr, Except.bind_err] at hattrs
        · rename_i hₑ'
          simp at ih_hd' ; replace ⟨ih_hd', ih_hd''⟩ := ih_hd' ; subst ih_hd' ih_hd''
          cases hhd : Partial.evaluate vhd req entities
          <;> simp [hhd] at ih ih_hd hattrs hₑ'
          case error e => simp only [Partial.bindAttr, Except.bind_err] at hattrs
          case ok hd_pval =>
            simp [ih_hd] at hₑ'
            cases htl : tl.mapM λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req entities)
            <;> simp only [htl, Except.bind_err, Except.bind_ok] at hattrs ih
            <;> simp only [Partial.bindAttr, Except.bind_ok, Except.ok.injEq] at hattrs
            case ok tl_pvals =>
              subst pvals
              simp [ih_hd, pure, Except.pure]
              cases hhd' : Partial.evaluate vhd req' (entities.subst subsmap)
              <;> simp only [hhd'] at hattrs'
              case error e => simp only [Partial.bindAttr, Except.bind_err] at hattrs'
              case ok hd_pval' =>
                clear hₑ'
                split at ih <;> rename_i ih'
                <;> simp at ih' <;> replace ⟨ih', ih''⟩ := ih'
                · simp only [ih'', Except.bind_err] at hattrs'
                  simp only [Partial.bindAttr, Except.bind_ok] at hattrs'
                · rename_i hₑ'
                  subst ih' ih''
                  simp [ih]
                  exact hattrs'

/--
  Inductive argument that re-evaluation of a `Spec.Expr.record` with a
  substitution on the residual expression, is equivalent to substituting first
  and then evaluating on the original `Spec.Expr.record`.
-/
-- TODO: there is significant duplication of the proof between this theorem and
-- `mapM_reeval_eqv_substituting_first` above. This theorem uses the one above
-- as a lemma in only one case. It could probably use it as a lemma in more
-- cases, to reduce duplication.
theorem reeval_eqv_substituting_first {attrs : List (Attr × Spec.Expr)} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih : ∀ kv ∈ attrs, ReevalEquivSubstFirst kv.snd req req' entities subsmap) :
  ReevalEquivSubstFirst (Spec.Expr.record attrs) req req' entities subsmap
:= by
  have h := mapM_reeval_eqv_substituting_first wf_r wf_e wf_s ih
  have hsorted_attrs : attrs.SortedBy Prod.fst := sorry
  unfold ReevalEquivSubstFirst at *
  simp only [Partial.evaluate]
  simp only at ih
  rw [
    Evaluate.Record.mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · req entities),
    Evaluate.Record.mapM₂_eq_mapM_partial_bindAttr (Partial.evaluate · req' (entities.subst subsmap)),
  ]
  split
  · simp only [implies_true]
  · rename_i hₑ h₁
    intro h_req ; simp [h_req] at ih ; specialize h h_req
    simp at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
    cases hattrs : attrs.mapM λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req entities)
    <;> simp [hattrs] at hₑ <;> simp [hattrs]
    <;> cases hattrs' : attrs.mapM λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req' (entities.subst subsmap))
    <;> simp [hattrs'] at hₑ <;> simp [hattrs']
    case error.ok e pvals =>
      replace ⟨x, hx, hattrs⟩ := List.mapM_error_implies_exists_error hattrs
      replace ⟨pval, _, hattrs'⟩ := List.mapM_ok_implies_all_ok hattrs' x hx
      simp only [Partial.bindAttr] at hattrs hattrs'
      rw [do_error] at hattrs
      have ⟨e', hattrs''⟩ := Evaluate.subst_preserves_errors wf_r wf_e wf_s h_req hattrs
      simp [hattrs''] at hattrs'
    case ok.error pvals e =>
      -- evaluating `attrs` before substitution produced residuals, but after
      -- substitution, one of them produced the error `e`
      replace ⟨(k, x), hx, hattrs'⟩ := List.mapM_error_implies_exists_error hattrs'
      -- `x` is the input expression that produced error `e` after substitution
      exact match h₁ : Partial.evaluate x req entities with
      | .error e' => by
        replace ⟨pval, _, hxs⟩ := List.mapM_ok_implies_all_ok hattrs (k, x) hx
        simp [h₁, Partial.bindAttr] at hxs
      | .ok pv => by
        cases pv
        case value v =>
          simp [Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req h₁, Partial.bindAttr] at hattrs'
        case residual r =>
          have h₂ : (k, .residual r) ∈ pvals := by
            replace ⟨(k', pval), h₄, hattrs⟩ := List.mapM_ok_implies_all_ok hattrs (k, x) hx
            simp only [Partial.bindAttr] at hattrs
            replace ⟨pval', hattrs, hattrs'⟩ := do_ok.mp hattrs
            simp only [Prod.mk.injEq] at hattrs' ; replace ⟨hattrs', hattrs''⟩ := hattrs' ; subst k' pval'
            simp [hattrs] at h₁ ; subst h₁
            exact h₄
          have h₃ : pvals.mapM (λ kv => match kv.snd with | .value v => some v | .residual _ => none) = none := by
            by_contra h₃
            simp [Option.ne_none_iff_exists'] at h₃
            replace ⟨vs, h₃⟩ := h₃
            replace ⟨v, _, h₃⟩ := List.mapM_some_implies_all_some h₃ (k, .residual r) h₂
            simp at h₃
          split at hₑ <;> rename_i h₄
          · rename_i avs
            replace ⟨(k', pval), h_pval, h₃⟩ := List.mapM_none_iff_exists_none.mp h₃
            replace ⟨(k'', v), hv, h₄⟩ := List.mapM_some_implies_all_some h₄ (k', pval) h_pval
            cases pval <;> simp at h₃ h₄
          · simp at *
            specialize ih (k, x) hx
            simp [h₁] at ih
            split at ih <;> rename_i ih'
            <;> simp at ih' <;> replace ⟨ih', ih''⟩ := ih'
            · exfalso
              rename_i e' e''
              simp only [Partial.Value.subst] at hₑ
              suffices ∃ e, Partial.evaluateValue ((Partial.ResidualExpr.record pvals).subst subsmap) (entities.subst subsmap) = .error e by
                replace ⟨e, this⟩ := this
                exact hₑ e this
              clear hₑ
              simp only [Partial.ResidualExpr.subst, List.map_attach₂_snd]
              apply element_error_implies_record_error (k := k) (pv := (Partial.Value.residual r).subst subsmap) _ ih'
              simp only [List.mem_map, Prod.mk.injEq]
              exists (k, .residual r)
            · rename_i hₑ'
              subst ih' ih''
              simp only [Partial.bindAttr] at hattrs'
              rw [do_error] at hattrs'
              simp only [hattrs', Except.error.injEq, imp_false, forall_apply_eq_imp_iff] at ih hₑ'
              simp [ih] at hₑ'
    case ok.ok pvals pvals' =>
      -- evaluating `attrs` before substitution produced `pvals`, and after
      -- substitution, produced `pvals'`
      split <;> rename_i h₁ <;> simp
      · -- `pvals` is actually fully concrete
        rename_i avs
        clear hₑ
        have h_pvals : pvals = pvals' := by
          suffices Except.ok (ε := Error) pvals = Except.ok pvals' by simpa using this
          suffices attrs.mapM (λ kv => Partial.bindAttr kv.fst (Partial.evaluate kv.snd req' (entities.subst subsmap))) = .ok pvals by
            rw [← this, ← hattrs']
          apply Evaluate.Record.mapM_subst_snd_preserves_evaluation_to_values _ h_req pvals hattrs _
          · unfold SubstPreservesEvaluationToConcrete
            intro x _ h_req v hx
            exact Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req hx
          · unfold IsAllConcrete
            exists (avs.map Prod.snd)
            simp [List.mapM_map]
            exact commute_prod_snd h₁
        subst pvals'
        simp [h₁, Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
      · -- `pvals` is not fully concrete; that is, it contains at least one `.residual`
        clear hₑ
        simp only [Partial.Value.subst, Partial.ResidualExpr.subst, List.map_attach₂_snd]
        simp only [Partial.evaluateValue, Partial.evaluateResidual, Evaluate.Record.mapM₂_eq_mapM_partial_bindAttr (Partial.evaluateValue · (entities.subst subsmap))]
        simp only [List.mapM_map]
        cases h₂ : pvals.mapM λ kv => Partial.bindAttr kv.fst (Partial.evaluateValue (kv.snd.subst subsmap) (entities.subst subsmap))
        case error e =>
          exfalso
          replace ⟨(k, pval), h_pval, h₂⟩ := List.mapM_error_implies_exists_error h₂
          simp only [Partial.bindAttr, do_error] at h₂
          have wf₁ : pval.WellFormed := by
            apply Evaluate.partial_eval_wf_mapM_snd wf_r wf_e _ hattrs pval
            simp only [List.mem_map]
            exists (k, pval)
          -- re-evaluating `pvals` with substitution produced an error, and
          -- `pval` is the member of `pvals` which caused it
          replace ⟨(k', x), hx, h₃⟩ := List.mapM_ok_implies_all_from_ok hattrs (k, pval) h_pval
          simp only [Partial.bindAttr] at h₃
          replace ⟨pval', h₃, h₃'⟩ := do_ok.mp h₃
          simp only [Prod.mk.injEq] at h₃' ; replace ⟨h₃', h₃''⟩ := h₃' ; subst k' pval'
          -- `x` is the value in `attrs` which produced `pval` (`h₃`)
          replace ⟨(k', pval'), h_pval', hattrs'⟩ := List.mapM_ok_implies_all_ok hattrs' (k, x) hx
          simp only [Partial.bindAttr] at hattrs'
          replace ⟨pval'', hattrs', hattrs''⟩ := do_ok.mp hattrs'
          simp only [Prod.mk.injEq] at hattrs'' ; replace ⟨hattrs'', hattrs'''⟩ := hattrs'' ; subst k' pval''
          specialize ih (k, x) hx
          simp [h₃] at ih
          cases pval
          case value v =>
            simp [Partial.bindAttr, Subst.subst_concrete_value, EvaluateValue.eval_spec_value v] at h₂
          case residual r => simp only [h₂, hattrs'] at ih
        case ok pvals_re =>
          split <;> rename_i h₃
          · -- `pvals'` (substituting first then evaluating) is fully concrete `avs'`
            rename_i avs'
            have hsorted_avs' : avs'.SortedBy Prod.fst := by
              apply Evaluate.mapM_Option_on_snd_preserves_sortedBy_fst' _ h₃
              simp [Partial.bindAttr] at hattrs'
              exact Evaluate.mapM_Except_on_snd_preserves_sortedBy_fst hsorted_attrs hattrs' (f := (Partial.evaluate · req' (entities.subst subsmap)))
            simp only [Except.bind_ok]
            split <;> rename_i h₄
            · -- and re-evaluating `pvals` with substitution produced fully concrete `avs`
              rename_i avs
              have hsorted_avs : avs.SortedBy Prod.fst := by
                apply Evaluate.mapM_Option_on_snd_preserves_sortedBy_fst' _ h₄
                simp [Partial.bindAttr] at h₂ hattrs
                apply Evaluate.mapM_Except_on_snd_preserves_sortedBy_fst _ h₂ (f := λ (pv : Partial.Value) => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap))
                exact Evaluate.mapM_Except_on_snd_preserves_sortedBy_fst hsorted_attrs hattrs (f := (Partial.evaluate · req entities))
              simp only [Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.record.injEq]
              apply (Map.eq_iff_kvs_equiv (Map.make_wf _) (Map.make_wf _)).mp
              simp only [List.Equiv, List.subset_def]
              constructor <;> intro (k, v) hkv
              · replace hkv := Map.make_mem_list_mem hkv
                replace ⟨(k', pval_re), h_pval_re, h₄⟩ := List.mapM_some_implies_all_from_some h₄ (k, v) hkv
                split at h₄ <;> simp only [Option.some.injEq, Prod.mk.injEq] at h₄
                replace ⟨h₄, h₄'⟩ := h₄ ; subst k' h₄' ; rename_i v hv
                simp only at hv ; subst pval_re
                replace ⟨(k', pval), h_pval, h₂⟩ := List.mapM_ok_implies_all_from_ok h₂ (k, .value v) h_pval_re
                simp only [Partial.bindAttr] at h₂
                replace ⟨pv', h₂, h₂'⟩ := do_ok.mp h₂
                simp only [Prod.mk.injEq] at h₂' ; replace ⟨h₂', h₂''⟩ := h₂' ; subst k' pv'
                replace ⟨(k', x), hx, hxs⟩ := List.mapM_ok_implies_all_from_ok hattrs (k, pval) h_pval
                simp only [Partial.bindAttr] at hxs
                replace ⟨pval', hxs, hxs'⟩ := do_ok.mp hxs
                simp only [Prod.mk.injEq] at hxs' ; replace ⟨hxs', hxs''⟩ := hxs' ; subst k' pval'
                replace ⟨(k', pval'), h_pval', hattrs'⟩ := List.mapM_ok_implies_all_ok hattrs' (k, x) hx
                simp only [Partial.bindAttr] at hattrs'
                replace ⟨pval', hattrs', hattrs''⟩ := do_ok.mp hattrs'
                simp only [Prod.mk.injEq] at hattrs'' ; replace ⟨hattrs'', hattrs'''⟩ := hattrs'' ; subst k' pval'
                replace ⟨(k', v'), hv', h₃⟩ := List.mapM_some_implies_all_some h₃ (k, pval') h_pval'
                split at h₃ <;> simp only [Option.some.injEq, Prod.mk.injEq] at h₃
                replace ⟨h₃, h₃'⟩ := h₃ ; subst k' v' ; rename_i v' hv''
                suffices v = v' by subst this ; exact Map.mem_list_mem_make hsorted_avs' hv'
                specialize ih (k, x) hx
                simp [hxs, h₂, hattrs'] at ih ; subst pval'
                simpa using hv''
              · replace hkv := Map.make_mem_list_mem hkv
                replace ⟨(k', pval'), h_pval', h₃⟩ := List.mapM_some_implies_all_from_some h₃ (k, v) hkv
                split at h₃ <;> simp at h₃
                replace ⟨h₃, h₃'⟩ := h₃ ; subst k' v ; rename_i v' h_pval''
                simp only at h_pval'' ; subst pval'
                replace ⟨(k', x), hx, hxs'⟩ := List.mapM_ok_implies_all_from_ok hattrs' (k, .value v') h_pval'
                simp only [Partial.bindAttr] at hxs'
                replace ⟨v'', hxs', hxs''⟩ := do_ok.mp hxs'
                simp only [Prod.mk.injEq] at hxs'' ; replace ⟨hxs'', hxs'''⟩ := hxs'' ; subst k' v''
                replace ⟨(k', pval), h_pval, hxs⟩ := List.mapM_ok_implies_all_ok hattrs (k, x) hx
                simp only [Partial.bindAttr] at hxs
                replace ⟨pval', hxs, hxs''⟩ := do_ok.mp hxs
                simp only [Prod.mk.injEq] at hxs'' ; replace ⟨hxs'', hxs'''⟩ := hxs'' ; subst k' pval'
                replace ⟨(k', pval_re), h_pval_re, h₂⟩ := List.mapM_ok_implies_all_ok h₂ (k, pval) h_pval
                simp only [Partial.bindAttr] at h₂
                replace ⟨pval', h₂, h₂'⟩ := do_ok.mp h₂
                simp only [Prod.mk.injEq] at h₂' ; replace ⟨h₂', h₂''⟩ := h₂' ; subst k' pval'
                replace ⟨v, hv, h₄⟩ := List.mapM_some_implies_all_some h₄ (k, pval_re) h_pval_re
                split at h₄ <;> simp at h₄
                subst h₄ ; rename_i v hv'
                simp only at hv'
                suffices v = v' by subst this ; exact Map.mem_list_mem_make hsorted_avs hv
                specialize ih (k, x) hx
                simp [hxs, h₂, hxs'] at ih ; subst ih
                simpa using hv'.symm
            · -- but re-evaluating `pvals` with substitution produced `pvals_re` which is not fully concrete
              exfalso
              replace ⟨(k, pval), h_pval, h₄⟩ := List.mapM_none_iff_exists_none.mp h₄
              split at h₄ <;> simp at h₄ ; rename_i pval' h_pval'
              simp only at h_pval'
              replace ⟨(k', pval''), h_pval'', h₂⟩ := List.mapM_ok_implies_all_from_ok h₂ (k, pval) h_pval
              simp only [Partial.bindAttr] at h₂
              replace ⟨v', h₂, h₂'⟩ := do_ok.mp h₂
              simp only [Prod.mk.injEq] at h₂' ; replace ⟨h₂', h₂''⟩ := h₂' ; subst k' v'
              replace ⟨(k', x), hx, hattrs⟩ := List.mapM_ok_implies_all_from_ok hattrs (k, pval'') h_pval''
              simp only [Partial.bindAttr] at hattrs
              replace ⟨pval', hattrs, hattrs''⟩ := do_ok.mp hattrs
              simp only [Prod.mk.injEq] at hattrs'' ; replace ⟨hattrs'', hattrs'''⟩ := hattrs'' ; subst k' pval'
              replace ⟨(k', pval'''), h_pval''', hattrs'⟩ := List.mapM_ok_implies_all_ok hattrs' (k, x) hx
              simp only [Partial.bindAttr] at hattrs'
              replace ⟨pval', hattrs', hattrs''⟩ := do_ok.mp hattrs'
              simp only [Prod.mk.injEq] at hattrs'' ; replace ⟨hattrs'', hattrs'''⟩ := hattrs'' ; subst k' pval'
              replace ⟨(k', v), hv, h₃⟩ := List.mapM_some_implies_all_some h₃ (k, pval''') h_pval'''
              split at h₃ <;> simp at h₃ ; rename_i v' hv'
              simp only at hv' ; subst pval'''
              replace ⟨h₃, h₃'⟩ := h₃ ; subst k' v'
              specialize ih (k, x) hx
              simp [hattrs, h₂, hattrs'] at ih
              subst ih
              simp only at h_pval'
          · -- `pvals'` (substituting first then evaluating) is not fully concrete
            simp only [Except.bind_ok]
            split <;> rename_i h₄
            · -- but re-evaluating `pvals` with substitution produced fully concrete `avs`
              exfalso
              rename_i vs'
              replace ⟨(k, pval'), h_pval', h₃⟩ := List.mapM_none_iff_exists_none.mp h₃
              split at h₃ <;> simp at h₃ ; rename_i pval'' h_pval''
              simp only at h_pval''
              replace ⟨(k', x), hx, hattrs'⟩ := List.mapM_ok_implies_all_from_ok hattrs' (k, pval') h_pval'
              simp only [Partial.bindAttr] at hattrs'
              replace ⟨v', hattrs', hattrs''⟩ := do_ok.mp hattrs'
              simp only [Prod.mk.injEq] at hattrs'' ; replace ⟨hattrs'', hattrs'''⟩ := hattrs'' ; subst k' v'
              replace ⟨(k', pval), h_pval, hattrs⟩ := List.mapM_ok_implies_all_ok hattrs (k, x) hx
              simp only [Partial.bindAttr] at hattrs
              replace ⟨v, hattrs, hattrs''⟩ := do_ok.mp hattrs
              simp only [Prod.mk.injEq] at hattrs'' ; replace ⟨hattrs'', hattrs'''⟩ := hattrs'' ; subst k' v
              replace ⟨(k', pval_re), h_pval_re, h₂⟩ := List.mapM_ok_implies_all_ok h₂ (k, pval) h_pval
              simp only [Partial.bindAttr] at h₂
              replace ⟨pval_re', h₂, h₂'⟩ := do_ok.mp h₂
              simp only [Prod.mk.injEq] at h₂' ; replace ⟨h₂', h₂''⟩ := h₂' ; subst k' pval_re'
              replace ⟨v', hv', h₄⟩ := List.mapM_some_implies_all_some h₄ (k, pval_re) h_pval_re
              split at h₄ <;> simp at h₄
              subst h₄ ; rename_i v' hv''
              specialize ih (k, x) hx
              simp [hattrs, h₂, hattrs'] at ih ; subst pval_re
              simp only at hv'' ; subst hv''
              simp only at h_pval''
            · -- and re-evaluating `pvals` with substitution produced `pvals_re` which is not fully concrete either
              simp only [Except.ok.injEq, Partial.Value.residual.injEq,
                Partial.ResidualExpr.record.injEq]
              simp [hattrs, h₂, hattrs'] at h
              subst h ; rfl

end Cedar.Thm.Partial.Evaluation.Reevaluation.Record
