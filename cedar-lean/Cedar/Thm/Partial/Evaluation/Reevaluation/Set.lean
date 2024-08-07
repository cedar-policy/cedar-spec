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
import Cedar.Thm.Partial.Evaluation.Evaluate.Set
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Reevaluation.Set

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Error Prim Result)

/--
  If evaluating any element of a `Partial.ResidualExpr.set` produces an error,
  then evaluating the whole `Partial.ResidualExpr.set` must also produce an
  error (not necessarily the same error)
-/
theorem element_error_implies_set_error {pv : Partial.Value} {pvs : List Partial.Value} {entities : Partial.Entities} {e : Error} :
  pv ∈ pvs →
  Partial.evaluateValue pv entities = .error e →
  ∃ e', Partial.evaluateValue (.residual (Partial.ResidualExpr.set pvs)) entities = .error e'
:= by
  intro h₁ h₂
  simp [Partial.evaluateValue, Partial.evaluateResidual, List.mapM₁_eq_mapM (Partial.evaluateValue · entities)]
  cases h₃ : pvs.mapM (Partial.evaluateValue · entities) <;> simp
  case ok pvals =>
    replace ⟨pval, _, h₃⟩ := List.mapM_ok_implies_all_ok h₃ pv h₁
    simp [h₂] at h₃

/--
  Basically a statement of `ReevalEquivSubstFirst`, but for
  `mapM Partial.evaluate` instead of raw `Partial.evaluate`. Used by both Set
  and Call.
-/
theorem mapM_reeval_eqv_substituting_first {xs : List Spec.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih : ∀ x ∈ xs, ReevalEquivSubstFirst x req req' entities subsmap) :
  req.subst subsmap = some req' →
  let re_evaluated := xs.mapM (Partial.evaluate · req entities) >>= λ residuals => residuals.mapM (λ residual => Partial.evaluateValue (residual.subst subsmap) (entities.subst subsmap))
  let subst_first := xs.mapM (λ x => Partial.evaluate x req' (entities.subst subsmap))
  match (re_evaluated, subst_first) with
  | (Except.error _, Except.error _) => true -- don't require that the errors are equal
  | (_, _) => re_evaluated = subst_first
:= by
  simp only
  split <;> try simp only [implies_true]
  rename_i hₑ h₁
  simp at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
  cases hxs : xs.mapM (Partial.evaluate · req entities)
  <;> simp only [Except.bind_ok, Except.bind_err]
  <;> cases hxs' : xs.mapM (λ x => Partial.evaluate x req' (entities.subst subsmap))
  <;> simp [hxs, hxs'] at hₑ
  case error.ok e pvals =>
    intro h_req
    exfalso
    replace ⟨x, hx, hxs⟩ := List.mapM_error_implies_exists_error hxs
    replace ⟨pval, _, hxs'⟩ := List.mapM_ok_implies_all_ok hxs' x hx
    have ⟨e, hxs''⟩ := Evaluate.subst_preserves_errors wf_r wf_e wf_s h_req hxs
    simp only [hxs''] at hxs'
  case ok.error pvals e =>
    -- evaluating `xs` before substitution produced residuals, but after
    -- substitution, one of them produced the error `e`
    replace ⟨x, hx, hxs'⟩ := List.mapM_error_implies_exists_error hxs'
    -- `x` is the input expression that produced error `e` after substitution
    exact match h₁ : Partial.evaluate x req entities with
    | .error e' => by
      replace ⟨pval, _, hxs⟩ := List.mapM_ok_implies_all_ok hxs x hx
      simp [h₁] at hxs
    | .ok (.value v) => by
      intro h_req
      simp [Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req h₁] at hxs'
    | .ok (.residual r) => by
      intro h_req
      specialize ih x hx h_req
      simp [h₁] at ih
      split at ih <;> rename_i ih'
      <;> simp at ih' <;> replace ⟨ih', ih''⟩ := ih'
      · rename_i e' e''
        simp [hxs'] at ih'' ; subst e''
        suffices ∃ e, pvals.mapM (λ pval => Partial.evaluateValue (pval.subst subsmap) (entities.subst subsmap)) = .error e by
          replace ⟨e, this⟩ := this
          exfalso ; exact hₑ e this
        clear hₑ
        apply List.element_error_implies_mapM_error (x := Partial.Value.residual r) _ ih'
        replace ⟨pval, h₃, hxs⟩ := List.mapM_ok_implies_all_ok hxs x hx
        simp [hxs] at h₁ ; subst h₁
        exact h₃
      · rename_i hₑ'
        subst ih' ih''
        simp [hxs', ih] at ih hₑ'
  case ok.ok pvals pvals' =>
    -- evaluating `xs` before substitution produced `pvals`, and after
    -- substitution, produced `pvals'`
    intro h_req
    -- we proceed by induction on `xs`
    cases xs <;> simp [pure, Except.pure] at *
    case nil => subst pvals pvals' ; simp [pure, Except.pure]
    case cons hd tl =>
      have ⟨ih_hd, ih_tl⟩ := ih ; clear ih
      have ih := mapM_reeval_eqv_substituting_first wf_r wf_e wf_s ih_tl h_req
      -- the plan is to use `ih_hd` to dispatch the `hd`-related obligations,
      -- and `ih` (not `ih_tl`) to dispatch the `tl`-related obligations
      specialize ih_hd h_req
      simp at ih_hd ; split at ih_hd <;> rename_i ih_hd'
      · rename_i e e'
        cases hhd : Partial.evaluate hd req entities
        <;> simp [hhd] at ih_hd' hxs
        case ok hd_pval =>
          cases htl : tl.mapM (Partial.evaluate · req entities)
          <;> simp [htl] at hxs
          case ok tl_pvals => subst pvals ; simp [ih_hd'] at hxs'
      · rename_i hₑ'
        simp at ih_hd' ; replace ⟨ih_hd', ih_hd''⟩ := ih_hd' ; subst ih_hd' ih_hd''
        cases hhd : Partial.evaluate hd req entities
        <;> simp [hhd] at ih ih_hd hxs hₑ'
        case ok hd_pval =>
          simp [ih_hd] at hₑ'
          cases htl : tl.mapM (Partial.evaluate · req entities)
          <;> simp [htl] at hxs ih
          case ok tl_pvals =>
            subst pvals
            simp [ih_hd, pure, Except.pure]
            cases hhd' : Partial.evaluate hd req' (entities.subst subsmap)
            <;> simp [hhd'] at hxs'
            case ok hd_pval' =>
              clear hₑ'
              split at ih <;> rename_i ih'
              <;> simp at ih' <;> replace ⟨ih', ih''⟩ := ih'
              · simp [ih''] at hxs'
              · rename_i hₑ'
                subst ih' ih''
                simp [ih]
                exact hxs'

/--
  Inductive argument that re-evaluation of a `Spec.Expr.set` with a
  substitution on the residual expression, is equivalent to substituting first
  and then evaluating on the original `Spec.Expr.set`.
-/
-- TODO: there is significant duplication of the proof between this theorem and
-- `mapM_reeval_eqv_substituting_first` above. This theorem uses the one above
-- as a lemma in only one case. It could probably use it as a lemma in more
-- cases, to reduce duplication.
theorem reeval_eqv_substituting_first {xs : List Spec.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih : ∀ x ∈ xs, ReevalEquivSubstFirst x req req' entities subsmap) :
  ReevalEquivSubstFirst (Spec.Expr.set xs) req req' entities subsmap
:= by
  have h := mapM_reeval_eqv_substituting_first wf_r wf_e wf_s ih
  unfold ReevalEquivSubstFirst at *
  simp only [Partial.evaluate]
  simp only at ih
  rw [
    List.mapM₁_eq_mapM (Partial.evaluate · req entities),
    List.mapM₁_eq_mapM (Partial.evaluate · req' (entities.subst subsmap)),
  ]
  split
  · simp only [implies_true]
  · rename_i hₑ h₁
    intro h_req ; simp [h_req] at ih ; specialize h h_req
    simp at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
    cases hxs : xs.mapM (Partial.evaluate · req entities)
    <;> simp [hxs] at hₑ <;> simp [hxs]
    <;> cases hxs' : xs.mapM (λ x => Partial.evaluate x req' (entities.subst subsmap))
    <;> simp [hxs'] at hₑ <;> simp [hxs']
    case error.ok e pvals =>
      replace ⟨x, hx, hxs⟩ := List.mapM_error_implies_exists_error hxs
      replace ⟨pval, _, hxs'⟩ := List.mapM_ok_implies_all_ok hxs' x hx
      have ⟨e', hxs''⟩ := Evaluate.subst_preserves_errors wf_r wf_e wf_s h_req hxs
      simp only [hxs''] at hxs'
    case ok.error pvals e =>
      -- evaluating `xs` before substitution produced residuals, but after
      -- substitution, one of them produced the error `e`
      replace ⟨x, hx, hxs'⟩ := List.mapM_error_implies_exists_error hxs'
      -- `x` is the input expression that produced error `e` after substitution
      exact match h₁ : Partial.evaluate x req entities with
      | .error e' => by
        replace ⟨pval, _, hxs⟩ := List.mapM_ok_implies_all_ok hxs x hx
        simp [h₁] at hxs
      | .ok (.value v) => by
        simp [Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req h₁] at hxs'
      | .ok (.residual r) => by
        have h₂ : (Partial.Value.residual r) ∈ pvals := by
          replace ⟨pval, h₄, hxs⟩ := List.mapM_ok_implies_all_ok hxs x hx
          simp [hxs] at h₁ ; subst h₁
          exact h₄
        have h₃ : pvals.mapM (λ pval => match pval with | .value v => some v | .residual _ => none) = none := by
          by_contra h₃
          simp [Option.ne_none_iff_exists'] at h₃
          replace ⟨vs, h₃⟩ := h₃
          replace ⟨v, _, h₃⟩ := List.mapM_some_implies_all_some h₃ (.residual r) h₂
          simp at h₃
        split at hₑ <;> rename_i h₄
        · -- for some reason, Lean doesn't accept `rw [h₄] at h₃`,
          -- so we have this convoluted way to get Lean to see the contradiction here
          rename_i vs
          suffices some vs = none by simp at this
          rw [← h₄, ← h₃]
          rfl
        · simp only [Except.bind_ok]
          simp only [hxs, Except.bind_ok] at h
          specialize ih x hx
          simp only [h₁, Except.bind_ok] at ih
          split at ih <;> rename_i ih'
          <;> simp at ih' <;> replace ⟨ih', ih''⟩ := ih'
          · exfalso
            rename_i e' e''
            simp [Partial.Value.subst, Partial.ResidualExpr.subst, List.map₁_eq_map] at hₑ
            suffices ∃ e, Partial.evaluateValue (.residual (.set (pvals.map (Partial.Value.subst subsmap)))) (entities.subst subsmap) = .error e by
              replace ⟨e, this⟩ := this
              exact hₑ e this
            clear hₑ
            apply element_error_implies_set_error (pv := (Partial.Value.residual r).subst subsmap) _ ih'
            simp only [List.mem_map]
            exists (.residual r)
          · rename_i hₑ'
            subst ih' ih''
            simp [hxs'] at ih hₑ'
            simp [ih] at hₑ'
    case ok.ok pvals pvals' =>
      -- evaluating `xs` before substitution produced `pvals`, and after
      -- substitution, produced `pvals'`
      split <;> rename_i h₁ <;> simp
      · -- `pvals` is actually fully concrete
        rename_i vs
        clear hₑ
        have h_pvals : pvals = pvals' := by
          suffices Except.ok (ε := Error) pvals = Except.ok pvals' by simpa using this
          suffices xs.mapM (λ x => Partial.evaluate x req' (entities.subst subsmap)) = .ok pvals by
            rw [← this, ← hxs']
          apply Evaluate.Set.mapM_subst_preserves_evaluation_to_values _ h_req pvals hxs _
          · unfold SubstPreservesEvaluationToConcrete
            intro x _ h_req v hx
            exact Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req hx
          · unfold IsAllConcrete
            exists vs
        subst pvals'
        simp [h₁, Subst.subst_concrete_value, EvaluateValue.eval_spec_value]
      · -- `pvals` is not fully concrete; that is, it contains at least one `.residual`
        clear hₑ
        simp only [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual, List.map₁_eq_map]
        rw [List.mapM₁_eq_mapM (Partial.evaluateValue · (entities.subst subsmap))]
        rw [List.mapM_map]
        cases h₂ : pvals.mapM λ pval => Partial.evaluateValue (pval.subst subsmap) (entities.subst subsmap)
        <;> simp only [Except.bind_ok, Except.bind_err]
        case error e =>
          exfalso
          replace ⟨pval, h_pval, h₂⟩ := List.mapM_error_implies_exists_error h₂
          -- re-evaluating `pvals` with substitution produced an error, and
          -- `pval` is the member of `pvals` which caused it
          replace ⟨x, hx, h₃⟩ := List.mapM_ok_implies_all_from_ok hxs pval h_pval
          -- `x` is the member of `xs` which produced `pval`
          replace ⟨pval', _, hxs'⟩ := List.mapM_ok_implies_all_ok hxs' x hx
          specialize ih x hx
          simp [h₃, hxs'] at ih
          simp [ih] at h₂
        case ok pvals_re =>
          split <;> rename_i h₃
          · -- re-evaluating `pvals` with substitution produced fully concrete `vs`
            rename_i vs
            split <;> rename_i h₄
            · -- and `pvals'` (substituting first then evaluating) is fully concrete `vs'`
              rename_i vs'
              simp only [Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.set.injEq]
              simp only [Set.make_make_eqv, List.Equiv, List.subset_def]
              constructor <;> intro v hv
              · replace ⟨pval_re, h_pval_re, h₃⟩ := List.mapM_some_implies_all_from_some h₃ v hv
                split at h₃ <;> simp at h₃
                subst h₃ ; rename_i v
                replace ⟨pval, h_pval, h₂⟩ := List.mapM_ok_implies_all_from_ok h₂ (.value v) h_pval_re
                replace ⟨x, hx, hxs⟩ := List.mapM_ok_implies_all_from_ok hxs pval h_pval
                replace ⟨pval', h_pval', hxs'⟩ := List.mapM_ok_implies_all_ok hxs' x hx
                replace ⟨v', hv', h₄⟩ := List.mapM_some_implies_all_some h₄ pval' h_pval'
                split at h₄ <;> simp at h₄
                subst h₄ ; rename_i v'
                suffices v = v' by subst this ; exact hv'
                specialize ih x hx
                simp [hxs, h₂, hxs'] at ih
                exact ih
              · replace ⟨pval', h_pval', h₄⟩ := List.mapM_some_implies_all_from_some h₄ v hv
                split at h₄ <;> simp at h₄
                subst h₄ ; rename_i v'
                replace ⟨x, hx, hxs'⟩ := List.mapM_ok_implies_all_from_ok hxs' (.value v') h_pval'
                replace ⟨pval, h_pval, hxs⟩ := List.mapM_ok_implies_all_ok hxs x hx
                replace ⟨pval_re, h_pval_re, h₂⟩ := List.mapM_ok_implies_all_ok h₂ pval h_pval
                replace ⟨v, hv, h₃⟩ := List.mapM_some_implies_all_some h₃ pval_re h_pval_re
                split at h₃ <;> simp at h₃
                subst h₃ ; rename_i v
                suffices v = v' by subst this ; exact hv
                specialize ih x hx
                simp [hxs, h₂, hxs'] at ih
                exact ih
            · -- but `pvals'` (substituting first then evaluating) is not fully concrete
              exfalso
              replace ⟨pval', h_pval', h₄⟩ := List.mapM_none_iff_exists_none.mp h₄
              split at h₄ <;> simp at h₄ ; rename_i r
              replace ⟨x, hx, hxs'⟩ := List.mapM_ok_implies_all_from_ok hxs' (.residual r) h_pval'
              replace ⟨pval, h_pval, hxs⟩ := List.mapM_ok_implies_all_ok hxs x hx
              replace ⟨pval_re, h_pval_re, h₂⟩ := List.mapM_ok_implies_all_ok h₂ pval h_pval
              replace ⟨v, hv, h₃⟩ := List.mapM_some_implies_all_some h₃ pval_re h_pval_re
              split at h₃ <;> simp at h₃
              subst h₃ ; rename_i v
              specialize ih x hx
              simp [hxs, h₂, hxs'] at ih
          · -- re-evaluating `pvals` with substitution produced `pvals_re` which is not fully concrete
            split <;> rename_i h₄
            · -- but `pvals'` (substituting first then evaluating) is fully concrete `vs'`
              exfalso
              rename_i vs'
              replace ⟨pval_re, h_pval_re, h₃⟩ := List.mapM_none_iff_exists_none.mp h₃
              split at h₃ <;> simp at h₃ ; rename_i r
              replace ⟨pval, h_pval, h₂⟩ := List.mapM_ok_implies_all_from_ok h₂ (.residual r) h_pval_re
              replace ⟨x, hx, hxs⟩ := List.mapM_ok_implies_all_from_ok hxs pval h_pval
              replace ⟨pval', h_pval', hxs'⟩ := List.mapM_ok_implies_all_ok hxs' x hx
              replace ⟨v', hv', h₄⟩ := List.mapM_some_implies_all_some h₄ pval' h_pval'
              split at h₄ <;> simp at h₄
              subst h₄ ; rename_i v'
              specialize ih x hx
              simp [hxs, h₂, hxs'] at ih
            · -- and `pvals'` (substituting first then evaluating) is not fully concrete either
              simp only [Except.ok.injEq, Partial.Value.residual.injEq, Spec.Expr.set.injEq]
              simp [hxs, h₂, hxs'] at h
              subst h ; rfl

end Cedar.Thm.Partial.Evaluation.Reevaluation.Set
