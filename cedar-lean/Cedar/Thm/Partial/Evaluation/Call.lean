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
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Evaluation.Set
import Cedar.Thm.Partial.Evaluation.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Call

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Error Expr Ext ExtFun Prim Result)

/--
  `Partial.evaluateCall` on concrete arguments gives the same output as
  `Spec.call` on those same arguments
-/
theorem evaluateCall_on_concrete_eqv_concrete {vs : List Spec.Value} {xfn : ExtFun} :
  Partial.evaluateCall xfn (vs.map Partial.Value.value) = (Spec.call xfn vs).map Partial.Value.value
:= by
  unfold Partial.evaluateCall
  simp only [List.mapM_map, List.mapM_some, Except.map]
  cases Spec.call xfn vs <;> simp

/--
  Inductive argument that, for an `Expr.call` with concrete request/entities,
  partial evaluation and concrete evaluation give the same output
-/
theorem on_concrete_eqv_concrete_eval {xs : List Expr} {request : Spec.Request} {entities : Spec.Entities} {xfn : ExtFun} :
  (∀ x ∈ xs, PartialEvalEquivConcreteEval x request entities) →
  PartialEvalEquivConcreteEval (Expr.call xfn xs) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate
  simp only
  rw [List.mapM₁_eq_mapM (Partial.evaluate · request entities)]
  rw [List.mapM₁_eq_mapM (Spec.evaluate · request entities)]
  rw [Set.mapM_partial_eval_eqv_concrete_eval ih₁]
  cases xs.mapM (Spec.evaluate · request entities) <;> simp only [Except.bind_ok, Except.bind_err]
  case error e => simp only [Except.map, Except.bind_err]
  case ok vs => exact evaluateCall_on_concrete_eqv_concrete

/--
  if `Spec.call` returns `ok` with some value, that is a well-formed value
-/
theorem specCall_wf {vs : List Spec.Value} {xfn : ExtFun}
  (wf : ∀ v ∈ vs, v.WellFormed) :
  ∀ v, Spec.call xfn vs = .ok v → v.WellFormed
:= by
  unfold Spec.Value.WellFormed
  intro v
  cases v <;> simp
  case prim p => simp [Prim.WellFormed]
  case set | record =>
    unfold Spec.call Spec.res
    split <;> simp at * <;> split <;> simp
  case ext x => cases x <;> simp [Ext.WellFormed]

/--
  if `Partial.evaluateCall` on well-formed arguments returns `ok` with some
  value, that is a well-formed value as well
-/
theorem partialEvaluateCall_wf {pvals : List Partial.Value} {xfn : ExtFun}
  (wf : ∀ pval ∈ pvals, pval.WellFormed) :
  ∀ pval, Partial.evaluateCall xfn pvals = .ok pval → pval.WellFormed
:= by
  unfold Partial.evaluateCall Partial.Value.WellFormed Partial.ResidualExpr.WellFormed
  intro pval h₁
  split at h₁
  · rename_i vs h₂
    cases h₃ : Spec.call xfn vs <;> simp [h₃] at h₁
    subst pval
    rename_i v'
    apply specCall_wf _ v' h₃
    intro v h₅
    replace ⟨pval, h₄, h₂⟩ := List.mapM_some_implies_all_from_some h₂ v h₅
    specialize wf pval h₄
    unfold Partial.Value.WellFormed at wf
    cases pval <;> simp at wf h₂
    case value v' => subst v' ; exact wf
  · simp at h₁ ; subst h₁ ; simp

/--
  Inductive argument that if partial-evaluating an `Expr.Call` returns
  `ok` with some value, that value is well-formed
-/
theorem partial_eval_wf {xs : List Expr} {request : Partial.Request} {entities : Partial.Entities} {xfn : ExtFun}
  (ih : ∀ x ∈ xs, EvaluatesToWellFormed x request entities) :
  EvaluatesToWellFormed (Expr.call xfn xs) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  rw [List.mapM₁_eq_mapM (Partial.evaluate · request entities)]
  cases hx : xs.mapM (Partial.evaluate · request entities) <;> simp [hx]
  case ok pvals =>
    replace hx := List.mapM_ok_implies_all_from_ok hx
    apply partialEvaluateCall_wf _
    intro pval h₂
    replace ⟨x, h₃, hx⟩ := hx pval h₂
    exact ih x h₃ pval hx

/--
  If `Partial.evaluateCall` produces `ok` with a concrete value, then all of the
  arguments are concrete
-/
theorem partialEvaluateCall_concrete_then_args_concrete {args : List Partial.Value} {xfn : ExtFun} :
  Partial.evaluateCall xfn args = .ok (.value v) →
  ∀ arg ∈ args, ∃ v, arg = .value v
:= by
  unfold Partial.evaluateCall
  split <;> intro h₁ arg h₂
  · rename_i vs h₃
    replace ⟨v, h₃, h₄⟩ := List.mapM_some_implies_all_some h₃ arg h₂
    cases arg <;> simp only [Option.some.injEq] at h₄
    subst v ; rename_i v
    exists v
  · rename_i h₃
    replace ⟨arg', h₃, h₄⟩ := List.mapM_none_iff_exists_none.mp h₃
    cases arg' <;> simp only [Except.ok.injEq] at h₁ h₄

/--
  If partial-evaluating an `Expr.call` produces `ok` with a concrete
  value, then so would partial-evaluating any of the arguments
-/
theorem evals_to_concrete_then_args_eval_to_concrete {xs : List Expr} {request : Partial.Request} {entities : Partial.Entities} {xfn : ExtFun} :
  EvaluatesToConcrete (Expr.call xfn xs) request entities →
  ∀ x ∈ xs, EvaluatesToConcrete x request entities
:= by
  unfold EvaluatesToConcrete
  intro h₁ x h₂
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  rw [List.mapM₁_eq_mapM (Partial.evaluate · request entities)] at h₁
  cases h₃ : xs.mapM (Partial.evaluate · request entities)
  <;> simp only [h₃, Except.bind_ok, Except.bind_err] at h₁
  case ok pvals =>
    replace ⟨pval, h₃, h₄⟩ := List.mapM_ok_implies_all_ok h₃ x h₂
    replace ⟨v, h₁⟩ := partialEvaluateCall_concrete_then_args_concrete h₁ pval h₃
    subst pval
    exists v

/--
  Inductive argument that if partial-evaluation of an `Expr.call` returns
  a concrete value, then it returns the same value after any substitution of
  unknowns
-/
theorem subst_preserves_evaluation_to_value {args : List Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap} {xfn : ExtFun}
  (ih : ∀ arg ∈ args, SubstPreservesEvaluationToConcrete arg req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Expr.call xfn args) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete
  unfold Partial.evaluate Partial.evaluateCall
  intro h_req v
  rw [List.mapM₁_eq_mapM (Partial.evaluate · req entities)]
  cases h₁ : args.mapM (Partial.evaluate · req entities)
  <;> simp only [Except.bind_ok, Except.bind_err, Bool.not_eq_true', false_implies]
  case ok pvals =>
    split
    · rename_i vs h₂
      -- vs are the concrete values produced by evaluating the args pre-subst
      rw [List.mapM₁_eq_mapM (Partial.evaluate · req' (entities.subst subsmap))]
      rw [Set.mapM_subst_preserves_evaluation_to_values ih h_req pvals h₁ (by unfold IsAllConcrete ; exists vs)]
      cases h₃ : Spec.call xfn vs
      <;> simp only [Except.bind_err, Except.bind_ok, false_implies, Except.ok.injEq, Partial.Value.value.injEq]
      case ok v' =>
        intro h ; subst v'
        simp only [h₂, h₃, Except.bind_ok]
    · rename_i h₂
      replace ⟨pval, h₂, h₃⟩ := List.mapM_none_iff_exists_none.mp h₂
      cases pval <;> simp only at h₃
      case residual r => simp only [Except.ok.injEq, false_implies]

/--
  Inductive argument that if partial-evaluation of an `Expr.call`
  returns an error, then it also returns an error (not necessarily the same
  error) after any substitution of unknowns

  The proof of `subst_preserves_evaluation_to_value` for this
  request/entities/subsmap is passed in as an argument, because this file can't
  import `Thm/Partial/Evaluation.lean` to access it.
  See #372.
-/
theorem subst_preserves_errors {xs : List Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap} {xfn : ExtFun}
  (h_spetv : ∀ x, SubstPreservesEvaluationToConcrete x req req' entities subsmap)
  (ih : ∀ x ∈ xs, SubstPreservesEvaluationToError x req req' entities subsmap) :
  SubstPreservesEvaluationToError (Expr.call xfn xs) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToError at *
  simp only [Partial.evaluate, Partial.evaluateCall]
  intro h_req e
  rw [List.mapM₁_eq_mapM (Partial.evaluate · req entities)]
  rw [List.mapM₁_eq_mapM (Partial.evaluate · req' (entities.subst subsmap))]
  cases hxs : xs.mapM (Partial.evaluate · req entities)
  case error e' =>
    simp only [Except.bind_err, Except.error.injEq, List.mapM_map]
    intro _ ; subst e'
    replace ⟨x, hx, hxs⟩ := List.mapM_error_implies_exists_error hxs
    replace ⟨e', ih⟩ := ih x hx h_req e hxs
    have ⟨e'', h₁⟩ := List.element_error_implies_mapM_error hx (f := λ x => Partial.evaluate x req' (entities.subst subsmap)) ih
    simp only [h₁, Except.bind_err, Except.error.injEq, exists_eq']
  case ok pvals =>
    simp only [Except.bind_ok]
    intro h₁
    split at h₁ <;> rename_i h₁'
    · rename_i vs
      rw [do_error] at h₁
      have h₂ := Set.mapM_subst_preserves_evaluation_to_values (by intro x _ ; exact h_spetv x) h_req pvals hxs (by unfold IsAllConcrete ; exists vs)
      simp only [h₂, h₁', h₁, Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq']
    · simp only at h₁

end Cedar.Thm.Partial.Evaluation.Call
