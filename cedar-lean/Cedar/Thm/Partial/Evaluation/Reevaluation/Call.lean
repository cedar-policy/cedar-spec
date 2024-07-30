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
import Cedar.Thm.Partial.Evaluation.EvaluateCall
import Cedar.Thm.Partial.Evaluation.EvaluateValue
import Cedar.Thm.Partial.Evaluation.ReevaluateValue
import Cedar.Thm.Partial.Evaluation.Reevaluation.Set
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Reevaluation.Call

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Error ExtFun Prim Result)

/--
  something akin to `EvaluateValue.subst_preserves_errors`, lifted to
  lists of `Partial.Value`

  NOTE: As of this writing, not used
-/
theorem mapM_subst_preserves_errors {pvals : List Partial.Value} {req req' : Partial.Request} {entities : Partial.Entities} {e : Error}
  (wf_v : ∀ pval ∈ pvals, pval.WellFormed)
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  (pvals.mapM λ pval => Partial.evaluateValue pval entities) = .error e →
  ∃ e', (pvals.mapM λ pval => Partial.evaluateValue (pval.subst subsmap) (entities.subst subsmap)) = .error e'
:= by
  intro h_req h₁
  replace ⟨pval, h_pval, h₁⟩ := List.mapM_error_implies_exists_error h₁
  have ⟨e', h₁'⟩ := EvaluateValue.subst_preserves_errors (wf_v pval h_pval) wf_e wf_s h₁
  exact List.element_error_implies_mapM_error
    (f := λ pval => Partial.evaluateValue (pval.subst subsmap) (entities.subst subsmap))
    h_pval
    h₁'

/--
  Inductive argument that re-evaluation of a `Spec.Expr.call` with a
  substitution on the residual expression, is equivalent to substituting first
  and then evaluating on the original `Spec.Expr.call`.
-/
theorem reeval_eqv_substituting_first {xs : List Spec.Expr} {xfn : ExtFun} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih : ∀ x ∈ xs, ReevalEquivSubstFirst x req req' entities subsmap) :
  ReevalEquivSubstFirst (Spec.Expr.call xfn xs) req req' entities subsmap
:= by
  have h := Set.mapM_reeval_eqv_substituting_first wf_r wf_e wf_s ih
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
    <;> simp [hxs] at hₑ h <;> simp [hxs]
    <;> cases hxs' : xs.mapM (λ x => Partial.evaluate x req' (entities.subst subsmap))
    <;> simp [hxs'] at hₑ h <;> simp [hxs']
    case ok.error pvals e =>
      -- evaluating `xs` before substitution produced residuals, but after
      -- substitution, one of them produced the error `e`
      replace ⟨x, hx, hxs'⟩ := List.mapM_error_implies_exists_error hxs'
      -- `x` is the input expression that produced error `e` after substitution
      have hc := EvaluateCall.reeval_eqv_substituting_first pvals xfn entities h_req
      simp only at hc
      exact match h₁ : Partial.evaluate x req entities with
      | .error e' => by
        replace ⟨pval, _, hxs⟩ := List.mapM_ok_implies_all_ok hxs x hx
        simp [h₁] at hxs
      | .ok (.value v) => by
        simp [Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req h₁] at hxs'
      | .ok (.residual r) => by
        -- evaluating the argument `x` before substitution produced (`.residual r`),
        -- but evaluating `x` after substitution produced the error `e`,
        -- so we need to show that re-evaluating the call residual with that
        -- substitution also produces an error (not necessarily the same error)
        suffices ∃ e, (do let residual ← Partial.evaluateCall xfn pvals ; Partial.evaluateValue (residual.subst subsmap) (entities.subst subsmap)) = .error e by
          replace ⟨e, this⟩ := this
          exfalso ; exact hₑ e this
        clear hₑ
        have h₂ : (Partial.Value.residual r) ∈ pvals := by
          replace ⟨pval, h₄, hxs⟩ := List.mapM_ok_implies_all_ok hxs x hx
          simp [hxs] at h₁ ; subst h₁
          exact h₄
        split at hc <;> rename_i hc'
        <;> simp only [Prod.mk.injEq] at hc' <;> replace ⟨hc', hc''⟩ := hc'
        · rename_i e' e''
          exists e'
        · rename_i hₑ'
          subst hc' hc''
          simp only [hc, List.map_map, List.mapM_map, Function.comp_apply] ; clear hc
          -- using `hc` has reduced our proof obligation to showing that the
          -- subst-first evaluation produces (any) error.
          -- Our strategy for doing this will revolve around the fact that we know
          -- that evaluating one of the arguments itself (`x`) produced an error
          -- in the subst-first evaluation (`hxs'`).
          suffices ∃ e, (pvals.mapM λ pval => Partial.evaluateValue (pval.subst subsmap) (entities.subst subsmap)) = .error e by
            replace ⟨e, this⟩ := this
            exists e
            simp [this]
          suffices ∃ e, Partial.evaluateValue ((Partial.Value.residual r).subst subsmap) (entities.subst subsmap) = .error e by
            replace ⟨e, this⟩ := this
            exact List.element_error_implies_mapM_error h₂ this
          simp [Partial.Value.subst]
          specialize ih x hx
          simp only [h₁, Partial.Value.subst, Except.bind_ok] at ih
          cases hr' : r.subst subsmap
          case value v =>
            simp only [hr', EvaluateValue.eval_spec_value v] at ih
            simp only [← ih] at hxs'
          all_goals {
            simp only [hr'] at ih
            split at ih <;> rename_i ih'
            <;> simp only [Prod.mk.injEq] at ih' <;> replace ⟨ih', ih''⟩ := ih'
            · rename_i e' e''
              exists e'
            · subst ih' ih''
              simp [ih]
              exists e
          }
    case ok.ok pvals pvals' =>
      -- evaluating `xs` before substitution produced `pvals`, and after
      -- substitution, produced `pvals'`
      have hc := EvaluateCall.reeval_eqv_substituting_first pvals xfn entities h_req
      simp only at hc
      split at hc <;> rename_i hc'
      <;> simp only [Prod.mk.injEq] at hc' <;> replace ⟨hc', hc''⟩ := hc'
      · -- `evaluateCall` produced an error, both re-evaluated (`hc'`) and subst-first (`hc''`)
        -- (when substituting on `pvals`, that is, after evaluating `xs` (`hxs`).)
        -- Need to show that it also produces an error subst-first on `xs` (`hxs'`).
        rename_i e e'
        simp only [hc', Except.error.injEq] at *
        suffices ∃ e, Partial.evaluateCall xfn pvals' = .error e by
          replace ⟨e'', this⟩ := this
          exfalso ; exact hₑ e e'' rfl this
        clear hₑ
        simp [List.mapM_map, h] at hc''
        exists e'
      · subst hc' hc''
        simp [h, hc, List.mapM_map]

end Cedar.Thm.Partial.Evaluation.Reevaluation.Call
