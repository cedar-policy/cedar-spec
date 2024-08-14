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
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map
import Cedar.Thm.Partial.Evaluation.EvaluateValue
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Evaluate.Var

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr Error Expr Prim Var)

/--
  `Partial.evaluateVar` on concrete arguments gives the same output as
  `Spec.evaluate` on those arguments
-/
theorem evaluateVar_on_concrete_eqv_concrete_eval (v : Var) (request : Spec.Request) (entities : Spec.Entities) :
  Partial.evaluateVar v request entities = (Spec.evaluate (Expr.var v) request entities).map Partial.Value.value
:= by
  unfold Partial.evaluateVar Spec.evaluate
  cases v <;> simp only [Spec.Request.asPartialRequest, Except.map]
  case context =>
    simp only [Map.mapMOnValues_mapOnValues, EvaluateValue.eval_spec_value]
    rw [Map.mapMOnValues_ok (f := Partial.Value.value)]
    simp only [Except.bind_ok, Map.mapMOnValues_mapOnValues]
    rw [Map.mapMOnValues_some]
    simp only [Except.ok.injEq, Partial.Value.value.injEq, Spec.Value.record.injEq]
    exact Map.mapOnValues_id

/--
  Inductive argument that, for an `Expr.var` with concrete request/entities,
  partial evaluation and concrete evaluation give the same output
-/
theorem on_concrete_eqv_concrete_eval (v : Var) (request : Spec.Request) (entities : Spec.Entities) :
  PartialEvalEquivConcreteEval (Expr.var v) request entities
:= by
  unfold PartialEvalEquivConcreteEval Partial.evaluate
  exact evaluateVar_on_concrete_eqv_concrete_eval v request entities

/--
  if `Partial.evaluateVar` returns `ok` with some value, it is a well-formed value

  This takes the proof of `EvaluateValue.evalValue_wf` as an argument,
  because this file can't import `Thm/Partial/Evaluation/EvaluateValue` to get
  it (that would be a circular import). See #372.
-/
theorem evaluateVar_wf {v : Var} {request : Partial.Request} {entities : Partial.Entities}
  (wf_r : request.WellFormed)
  (wf_e : entities.WellFormed)
  (h_evwf : ∀ {pv pv'}, pv.WellFormed → entities.WellFormed → Partial.evaluateValue pv entities = .ok pv' → pv'.WellFormed) :
  ∀ pval, Partial.evaluateVar v request entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.evaluateVar
  cases v <;> simp
  case principal =>
    cases request.principal
    <;> simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  case action =>
    cases request.action
    <;> simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  case resource =>
    cases request.resource
    <;> simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  case context =>
    cases h₁ : request.context.mapMOnValues (Partial.evaluateValue · entities)
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies, implies_true]
    case ok context' =>
      split <;> simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed, Spec.Value.WellFormed]
      · rename_i m h₂
        apply And.intro (Map.mapMOnValues_some_wf (Map.mapMOnValues_ok_wf wf_r.left h₁) h₂)
        intro (k, v) h₃
        have ⟨pval, h₄, h₅⟩ := Map.mapMOnValues_some_implies_all_from_some h₂ (k, v) h₃
        have ⟨pval', h₆, h₇⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₁ (k, pval) h₄
        split at h₅ <;> simp only [Option.some.injEq] at h₅ ; subst v ; rename_i v
        simp only at *
        cases pval'
        case value v' =>
          simp [Partial.evaluateValue] at h₇ ; subst v'
          replace wf_r := wf_r.right (.value v)
          simp only [Partial.Value.WellFormed] at wf_r
          exact wf_r (Map.in_list_in_values h₆)
        case residual r' =>
          suffices (Partial.Value.value v).WellFormed by simpa [Partial.Value.WellFormed] using this
          apply h_evwf (pv := .residual r') (pv' := .value v) _ wf_e h₇
          · exact wf_r.right (.residual r') (Map.in_list_in_values h₆)
      · intro (k, pv') hpv'
        unfold Partial.Request.WellFormed at wf_r
        split at wf_r ; rename_i context ; simp only at *
        replace ⟨pv, hpv, h₁⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₁ (k, pv') hpv'
        apply h_evwf _ wf_e h₁
        exact wf_r.right pv (Map.in_list_in_values hpv)

/--
  If partial-evaluating a `Var` expression returns `ok` with some value, it is a
  well-formed value

  `h_evwf`: see notes on `evaluateVar_wf`
-/
theorem partial_eval_wf {v : Var} {request : Partial.Request} {entities : Partial.Entities}
  (wf_r : request.WellFormed)
  (wf_e : entities.WellFormed)
  (h_evwf : ∀ {pv pv'}, pv.WellFormed → entities.WellFormed → Partial.evaluateValue pv entities = .ok pv' → pv'.WellFormed) :
  EvaluatesToWellFormed (Expr.var v) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  exact evaluateVar_wf wf_r wf_e h_evwf

/--
  Lemma: If `context` has only concrete values before substitution, then it has
  only concrete values after substitution
-/
theorem subst_preserves_all_concrete {req req' : Partial.Request} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  req.context.mapMOnValues (λ v => match v with | .value v => some v | .residual _ => none) = some m →
  (k, pval') ∈ req'.context.kvs →
  ∃ v, pval' = .value v ∧ (k, .value v) ∈ req.context.kvs
:= by
  intro h_req h₁ h₂
  have wf_req' : req'.WellFormed := Subst.req_subst_preserves_wf wf_r wf_s h_req
  unfold Partial.Request.WellFormed at wf_r wf_req'
  have h_keys := Subst.req_subst_preserves_keys_of_context h_req
  have wf_keys := Map.keys_wf req.context wf_r.left
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
  replace h₁ := Map.mapMOnValues_some_implies_all_some h₁ (k, pval) h₃
  cases pval
  case residual r => simp only [and_false, exists_const] at h₁
  case value v =>
    have h₄ := Subst.req_subst_preserves_concrete_context_vals h₃ h_req
    have h₅ := Map.key_maps_to_one_value k _ _ _ wf_req'.left h₂ h₄
    exists v

/--
  If evaluating a request context returns a concrete value, then it returns the
  same value after any substitution of unknowns
-/
theorem subst_preserves_evaluate_req_context_to_value {req req' : Partial.Request} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  req.context.mapMOnValues (λ v => match v with | .value v => some v | .residual _ => none) = some m →
  req'.context.mapMOnValues (λ v => match v with | .value v => some v | .residual _ => none) = some m
:= by
  intro h_req h₁
  suffices req.context = req'.context by rw [← this] ; exact h₁
  have wf_req' : req'.WellFormed := Subst.req_subst_preserves_wf wf_r wf_s h_req
  unfold Partial.Request.WellFormed at wf_req'
  apply (Map.eq_iff_kvs_equiv wf_r.left wf_req'.left).mp
  simp only [List.Equiv, List.subset_def]
  constructor <;> intro (k, pval') h₄
  · replace h₁ := Map.mapMOnValues_some_implies_all_some h₁ (k, pval') h₄
    cases pval'
    case value v => exact Subst.req_subst_preserves_concrete_context_vals h₄ h_req
    case residual r => simp only [and_false, exists_const] at h₁
  · have ⟨v, h₃, h₅⟩ := subst_preserves_all_concrete wf_r wf_s h_req h₁ h₄
    subst pval'
    exact h₅

/--
  If `Partial.evaluateVar` returns a concrete value, then it returns the same
  value after any substitution of unknowns
-/
theorem subst_preserves_evaluateVar_to_value {var : Var} {req req' : Partial.Request} {entities : Partial.Entities} {v : Spec.Value} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed) :
  req.subst subsmap = some req' →
  Partial.evaluateVar var req entities = .ok (.value v) →
  Partial.evaluateVar var req' (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.evaluateVar
  intro h_req h₁
  cases var <;> simp only at h₁
  case principal =>
    cases h₂ : req.principal <;> simp only [h₂, Except.ok.injEq, Partial.Value.value.injEq] at h₁
    case known uid =>
      subst h₁
      simp [Subst.req_subst_preserves_known_principal h₂ h_req]
  case action =>
    cases h₂ : req.action <;> simp only [h₂, Except.ok.injEq, Partial.Value.value.injEq] at h₁
    case known uid =>
      subst h₁
      simp [Subst.req_subst_preserves_known_action h₂ h_req]
  case resource =>
    cases h₂ : req.resource <;> simp only [h₂, Except.ok.injEq, Partial.Value.value.injEq] at h₁
    case known uid =>
      subst h₁
      simp [Subst.req_subst_preserves_known_resource h₂ h_req]
  case context =>
    simp only
    cases h₂ : req.context.mapMOnValues (Partial.evaluateValue · entities)
    <;> simp only [h₂, Except.bind_ok, Except.bind_err] at h₁
    case ok context_ev =>
      -- `context_ev` is the "evaluated" context (i.e., `evaluateValue` applied to all the values)
      split at h₁ <;> simp only [Except.ok.injEq, Partial.Value.value.injEq] at h₁ ; subst h₁
      rename_i m h₁
      -- `m` is the `Spec.Value`-valued version of `context_ev` (which we know has only concrete values from h₁)
      simp [Partial.Request.subst] at h_req
      replace ⟨p, _, a, _, r, _, h_req⟩ := h_req
      subst req' ; simp [Map.mapMOnValues_mapOnValues]
      cases h₃ : req.context.mapMOnValues λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_err, Except.bind_ok]
      case error e =>
        replace ⟨pv, hpv, h₃⟩ := Map.mapMOnValues_error_implies_exists_error h₃
        replace ⟨k, hpv⟩ := Map.in_values_exists_key hpv
        replace ⟨pv', hpv', h₂⟩ := Map.mapMOnValues_ok_implies_all_ok h₂ (k, pv) hpv
        simp only at *
        replace ⟨pv'', hpv'', h₁⟩ := Map.mapMOnValues_some_implies_all_some h₁ (k, pv') hpv'
        split at h₁ <;> simp at h₁ ; subst pv'' ; simp only at * ; subst pv' ; rename_i v
        simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap (wf_r.right pv (Map.in_list_in_values hpv)) wf_e h₂] at h₃
      case ok context_ev' =>
        split <;> simp <;> rename_i h₄
        · rename_i m'
          suffices context_ev = context_ev' by subst context_ev' ; simpa [h₄] using h₁
          have wf₁ : context_ev.WellFormed := Map.mapMOnValues_ok_wf wf_r.left h₂
          have wf₂ : context_ev'.WellFormed := Map.mapMOnValues_ok_wf wf_r.left h₃
          rw [← Map.eq_iff_kvs_equiv wf₁ wf₂] ; simp [List.Equiv, List.subset_def]
          and_intros
          · intro (k, pv') hpv'
            replace ⟨pv, hpv, h₂⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₂ (k, pv') hpv'
            simp only at *
            replace ⟨pv'', hpv'', h₃⟩ := Map.mapMOnValues_ok_implies_all_ok h₃ (k, pv) hpv
            simp only at *
            replace ⟨v, hv, h₄⟩ := Map.mapMOnValues_some_implies_all_some h₄ (k, pv'') hpv''
            split at h₄ <;> simp at h₄ ; subst v ; simp only at * ; subst pv'' ; rename_i v
            replace ⟨v', hv', h₁⟩ := Map.mapMOnValues_some_implies_all_some h₁ (k, pv') hpv'
            split at h₁ <;> simp at h₁ ; subst v' ; simp only at * ; subst pv' ; rename_i v'
            simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap (wf_r.right pv (Map.in_list_in_values hpv)) wf_e h₂] at h₃
            subst v'
            exact hpv''
          · intro (k, pv) hpv
            replace ⟨pv', hpv', h₄⟩ := Map.mapMOnValues_some_implies_all_some h₄ (k, pv) hpv
            split at h₄ <;> simp at h₄ ; subst pv' ; simp only at * ; subst pv ; rename_i v
            replace ⟨pv'', hpv'', h₃⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₃ (k, .value v) hpv
            simp only at *
            replace ⟨pv''', hpv''', h₂⟩ := Map.mapMOnValues_ok_implies_all_ok h₂ (k, pv'') hpv''
            simp only at *
            replace ⟨v', hv', h₁⟩ := Map.mapMOnValues_some_implies_all_some h₁ (k, pv''') hpv'''
            split at h₁ <;> simp at h₁ ; subst v' ; simp only at * ; subst pv''' ; rename_i v'
            simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap (wf_r.right pv'' (Map.in_list_in_values hpv'')) wf_e h₂] at h₃
            subst v'
            exact hpv'''
        · replace ⟨pv, hpv, h₄⟩ := Map.mapMOnValues_none_iff_exists_none.mp h₄
          split at h₄ <;> simp at h₄ ; rename_i r
          replace ⟨k, hpv⟩ := Map.in_values_exists_key hpv
          replace ⟨pv', hpv', h₃⟩ := Map.mapMOnValues_ok_implies_all_from_ok h₃ (k, .residual r) hpv
          simp only at *
          replace ⟨pv'', hpv'', h₂⟩ := Map.mapMOnValues_ok_implies_all_ok h₂ (k, pv') hpv'
          simp only at *
          replace ⟨v, hv, h₁⟩ := Map.mapMOnValues_some_implies_all_some h₁ (k, pv'') hpv''
          simp only at *
          split at h₁ <;> simp at h₁ ; subst v ; rename_i v
          simp [EvaluateValue.subst_preserves_evaluation_to_value subsmap (wf_r.right pv' (Map.in_list_in_values hpv')) wf_e h₂] at h₃

/--
  If partial-evaluation of a `Var` returns a concrete value, then it returns the
  same value after any substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value (var : Var) (req req' : Partial.Request) (entities : Partial.Entities) (subsmap : Subsmap)
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed) :
  SubstPreservesEvaluationToConcrete (Expr.var var) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete Partial.evaluate
  intro h_req v
  exact subst_preserves_evaluateVar_to_value wf_r wf_e h_req

/--
  If `Partial.evaluateVar` returns an error, then it also returns an error (not
  necessarily the same error) after any substitution of unknowns
-/
theorem subst_preserves_evaluateVar_to_error {var : Var} {req req' : Partial.Request} {entities : Partial.Entities} {e : Error} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  Partial.evaluateVar var req entities = .error e →
  ∃ e', Partial.evaluateVar var req' (entities.subst subsmap) = .error e'
:= by
  cases var <;> simp only [Partial.evaluateVar, exists_false, imp_self, implies_true]
  case context =>
    intro h_req
    cases h₁ : req.context.mapMOnValues (Partial.evaluateValue · entities) <;> simp
    case ok => split <;> simp
    case error e₂ =>
      intro _ ; subst e₂
      replace ⟨pv, hpv, h₁⟩ := Map.mapMOnValues_error_implies_exists_error h₁
      have ⟨e₂, h₂⟩ := EvaluateValue.subst_preserves_errors (wf_r.right pv hpv) wf_e wf_s h₁
      have hpv' : (pv.subst subsmap) ∈ req'.context.values := by
        simp [Partial.Request.subst] at h_req
        replace ⟨p, _, a, _, r, _, hc⟩ := h_req ; clear h_req ; subst req'
        simp [Map.values_mapOnValues]
        exists pv
      have ⟨e₃, h₃⟩ := Map.element_error_implies_mapMOnValues_error hpv' h₂ (f := (Partial.evaluateValue · (entities.subst subsmap)))
      simp [h₃]

/--
  If partial-evaluation of a `Var` returns an error, then it also returns an
  error (not necessarily the same error) after any sustitution of unknowns
-/
theorem subst_preserves_errors {var : Var} {req req' : Partial.Request} {e : Error} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  Partial.evaluate (Expr.var var) req entities = .error e →
  ∃ e', Partial.evaluate (Expr.var var) req' (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.evaluate]
  exact subst_preserves_evaluateVar_to_error wf_r wf_e wf_s

end Cedar.Thm.Partial.Evaluation.Evaluate.Var
