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
import Cedar.Spec.Evaluator
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.LT
import Cedar.Thm.Data.Map
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Evaluation.WellFormed
import Cedar.Thm.Partial.Subst

namespace Cedar.Thm.Partial.Evaluation.Var

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (Var)

/--
  `Partial.evaluateVar` on concrete arguments gives the same output as
  `Spec.evaluate` on those arguments
-/
theorem partialEvaluateVar_on_concrete_eqv_concrete_eval (v : Var) (request : Spec.Request) (entities : Spec.Entities)
  (wf : request.WellFormed) :
  Partial.evaluateVar v request = (Spec.evaluate (Spec.Expr.var v) request entities).map Partial.Value.value
:= by
  unfold Partial.evaluateVar Spec.evaluate
  unfold Spec.Request.WellFormed at wf
  cases v <;> simp only [Spec.Request.asPartialRequest, Except.map]
  case context =>
    split
    case h_1 m h₁ =>
      simp only [Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.record.injEq]
      rw [← Map.eq_iff_kvs_equiv (wf₁ := Map.mapMOnValues_wf (Map.mapOnValues_wf.mp wf) h₁) (wf₂ := wf)]
      simp only [List.Equiv, List.subset_def]
      constructor
      case left =>
        intro (k, v) h₂
        rw [Map.mapOnValues_eq_make_map _ wf] at h₁
        unfold Map.toList at h₁
        replace ⟨pv, h₁, h₃⟩ := Map.mapMOnValues_some_implies_all_from_some h₁ (k, v) h₂
        replace h₁ := Map.make_mem_list_mem h₁
        cases pv <;> simp only [Option.some.injEq] at h₃
        case value v =>
          subst v
          rw [List.mem_map] at h₁
          replace ⟨(k', v'), h₁, h₃⟩ := h₁
          simp only [Prod.mk.injEq, Partial.Value.value.injEq] at h₃
          replace ⟨h₃, h₃'⟩ := h₃
          subst k' v'
          exact h₁
      case right =>
        intro (k, v) h₂
        have ⟨v', h₃, h₄⟩ := Map.mapMOnValues_some_implies_all_some h₁ (k, v) (Map.in_kvs_in_mapOnValues h₂)
        simp only [Option.some.injEq] at h₄
        subst h₄
        simp [h₃]
    case h_2 h₁ =>
      exfalso
      replace ⟨v, h₁, h₂⟩ := Map.mapMOnValues_none_iff_exists_none.mp h₁
      cases v <;> simp only at h₂
      case residual r =>
        rw [Map.mapOnValues_eq_make_map _ wf] at h₁
        replace h₁ := Map.mem_values_make h₁
        simp [List.mem_map] at h₁

/--
  Partial-evaluating a concrete `Var` expression gives the same output as
  concrete-evaluating the `Var`
-/
theorem on_concrete_eqv_concrete_eval (v : Var) (request : Spec.Request) (entities : Spec.Entities)
  (wf : request.WellFormed) :
  PartialEvalEquivConcreteEval (Spec.Expr.var v) request entities
:= by
  unfold PartialEvalEquivConcreteEval Spec.Expr.asPartialExpr Partial.evaluate
  exact partialEvaluateVar_on_concrete_eqv_concrete_eval v request entities wf

/--
  Lemma: If `context` has only concrete values before substitution, then it has
  only concrete values after substitution
-/
theorem subst_preserves_all_concrete {req req' : Partial.Request} {subsmap : Map Unknown Partial.Value}
  (wf : req.AllWellFormed) :
  req.subst subsmap = some req' →
  req.context.mapMOnValues (λ v => match v with | .value v => some v | .residual _ => none) = some m →
  (k, pval') ∈ req'.context.kvs →
  ∃ v, pval' = .value v ∧ (k, .value v) ∈ req.context.kvs
:= by
  intro h_req h₁ h₂
  have wf_req' : req'.AllWellFormed := Partial.Subst.req_subst_preserves_wf wf h_req
  unfold Partial.Request.AllWellFormed at wf wf_req'
  have h_keys := Partial.Subst.req_subst_preserves_keys_of_context h_req
  have wf_keys := Map.keys_wf req.context wf.left
  have ⟨keys, h₃⟩ := Set.if_wellformed_then_exists_make req.context.keys wf_keys
  rw [h₃] at h_keys
  unfold Map.keys at h_keys h₃
  replace h_keys := Set.make_mk_eqv h_keys
  replace h₃ := Set.make_mk_eqv h₃.symm
  simp only [List.Equiv, List.subset_def, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at h_keys h₃
  replace ⟨_, h_keys⟩ := h_keys
  replace ⟨h₃, _⟩ := h₃
  specialize h_keys (k, pval') h₂
  simp only at h_keys
  replace ⟨(k', pval), h₃, h₃'⟩ := h₃ h_keys
  simp only at h₃' ; subst k'
  cases pval
  case value v =>
    have h₄ := Partial.Subst.req_subst_preserves_concrete_context_vals h₃ h_req
    have h₅ := Map.key_maps_to_one_value k _ _ _ wf_req'.left h₂ h₄
    exists v
  case residual r =>
    replace h₁ := Map.mapMOnValues_some_implies_all_some h₁ (k, .residual r) h₃
    simp only [and_false, exists_const] at h₁

/--
  If evaluating a request context returns a concrete value, then it returns the
  same value after any substitution of unknowns
-/
theorem subst_preserves_evaluate_req_context_to_value {req req' : Partial.Request} {subsmap : Map Unknown Partial.Value}
  (wf : req.AllWellFormed) :
  req.subst subsmap = some req' →
  req.context.mapMOnValues (λ v => match v with | .value v => some v | .residual _ => none) = some m →
  req'.context.mapMOnValues (λ v => match v with | .value v => some v | .residual _ => none) = some m
:= by
  intro h_req h₁
  suffices req.context = req'.context by rw [← this] ; exact h₁
  have wf_req' : req'.AllWellFormed := Partial.Subst.req_subst_preserves_wf wf h_req
  unfold Partial.Request.AllWellFormed at wf_req'
  apply (Map.eq_iff_kvs_equiv wf.left wf_req'.left).mp
  simp only [List.Equiv, List.subset_def]
  constructor <;> intro (k, pval') h₄
  · cases pval'
    case value v =>
      exact Partial.Subst.req_subst_preserves_concrete_context_vals h₄ h_req
    case residual r =>
      exfalso
      replace h₁ := Map.mapMOnValues_some_implies_all_some h₁ (k, .residual r) h₄
      simp only [and_false, exists_const] at h₁
  · have ⟨v, h₃, h₅⟩ := subst_preserves_all_concrete wf h_req h₁ h₄
    subst pval'
    exact h₅

/--
  If `Partial.evaluateVar` returns a concrete value, then it returns the same
  value after any substitution of unknowns
-/
theorem subst_preserves_evaluateVar_to_value {var : Var} {req req' : Partial.Request} {v : Spec.Value} {subsmap : Map Unknown Partial.Value}
  (wf : req.AllWellFormed) :
  req.subst subsmap = some req' →
  Partial.evaluateVar var req = .ok (.value v) →
  Partial.evaluateVar var req' = .ok (.value v)
:= by
  unfold Partial.evaluateVar
  intro h_req h₁
  cases var <;> simp only at h₁
  case principal =>
    cases h₂ : req.principal <;> simp only [h₂, Except.ok.injEq, Partial.Value.value.injEq] at h₁
    case known uid =>
      subst h₁
      simp [Partial.Subst.req_subst_preserves_known_principal h₂ h_req]
  case action =>
    cases h₂ : req.action <;> simp only [h₂, Except.ok.injEq, Partial.Value.value.injEq] at h₁
    case known uid =>
      subst h₁
      simp [Partial.Subst.req_subst_preserves_known_action h₂ h_req]
  case resource =>
    cases h₂ : req.resource <;> simp only [h₂, Except.ok.injEq, Partial.Value.value.injEq] at h₁
    case known uid =>
      subst h₁
      simp [Partial.Subst.req_subst_preserves_known_resource h₂ h_req]
  case context =>
    simp only
    split at h₁ <;> simp only [Except.ok.injEq, Partial.Value.value.injEq] at h₁ ; subst h₁
    rename_i m h₁
    -- `m` is the `Spec.Value`-valued version of `req.context` (which we know has only concrete values from h₁)
    split <;> simp only [Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.record.injEq]
    · rename_i m' h₂
      -- `m'` is the `Spec.Value`-valued version of `req'.context` (which we know has only concrete values from h₂)
      replace h₁ := subst_preserves_evaluate_req_context_to_value wf h_req h₁
      suffices some m = some m' by simpa using this.symm
      rw [← h₁, ← h₂]
      rfl
    · rename_i h₂
      replace ⟨pval, h₂, h₃⟩ := Map.mapMOnValues_none_iff_exists_none.mp h₂
      cases pval <;> simp only at h₃
      case residual r =>
        replace ⟨k, h₂⟩ := Map.in_values_exists_key h₂
        have ⟨v, h₄⟩ := subst_preserves_all_concrete wf h_req h₁ h₂
        simp at h₄

/--
  If partial-evaluation of a `Var` returns a concrete value, then it returns the
  same value after any substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value (var : Var) (req req' : Partial.Request) (entities : Partial.Entities) (subsmap : Map Unknown Partial.Value)
  (wf : req.AllWellFormed) :
  SubstPreservesEvaluationToConcrete (Partial.Expr.var var) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete Partial.Expr.subst Partial.evaluate
  intro h_req v
  exact subst_preserves_evaluateVar_to_value wf h_req

end Cedar.Thm.Partial.Evaluation.Var
