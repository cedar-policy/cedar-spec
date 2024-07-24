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
import Cedar.Thm.Partial.Evaluation.Evaluate.Set
import Cedar.Thm.Partial.WellFormed
import Cedar.Thm.Partial.Subst

/-! Theorems about `Partial.evaluateCall` -/

namespace Cedar.Thm.Partial.Evaluation.EvaluateCall

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Error Expr Ext ExtFun Prim Result)

/--
  `Partial.evaluateCall` on concrete arguments gives the same output as
  `Spec.call` on those same arguments
-/
theorem on_concrete_eqv_concrete {vs : List Spec.Value} {xfn : ExtFun} :
  Partial.evaluateCall xfn (vs.map Partial.Value.value) = (Spec.call xfn vs).map Partial.Value.value
:= by
  unfold Partial.evaluateCall
  simp only [List.mapM_map, List.mapM_some, Except.map]
  cases Spec.call xfn vs <;> simp

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
theorem evaluateCall_wf {pvals : List Partial.Value} {xfn : ExtFun}
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
  · simp only [Except.ok.injEq] at h₁ ; subst h₁ ; simp only

/--
  If `Partial.evaluateCall` produces `ok` with a concrete value, then all of the
  arguments are concrete
-/
theorem returns_concrete_then_args_concrete {args : List Partial.Value} {xfn : ExtFun} :
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
  something akin to `Partial.Evaluation.EvaluateValue.eval_spec_value`, lifted to lists of `Partial.Value`
-/
theorem mapM_eval_spec_value {pvals : List Partial.Value} (entities : Partial.Entities) :
  (pvals.mapM λ pval => match pval with | .value v => some v | .residual _ => none) = some vs →
  (pvals.mapM (Partial.evaluateValue · entities)) = .ok (vs.map Partial.Value.value)
:= match pvals with
  | [] => by intro h₁ ; simp at h₁ ; subst vs ; simp [pure, Except.pure]
  | hd :: tl => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
      Option.some.injEq, forall_exists_index, and_imp, pure, Except.pure]
    intro vhd hvhd vtl hvtl _ ; subst vs
    cases hd <;> simp only [Option.some.injEq] at hvhd ; subst hvhd
    case value vhd =>
      simp only [Partial.evaluateValue, Except.bind_ok, List.map_cons]
      simp only [mapM_eval_spec_value (pvals := tl) entities hvtl, Except.bind_ok]

/--
  If `Partial.evaluateCall` returns a residual, re-evaluating that residual with
  a substitution is equivalent to substituting first, evaluating the arguments,
  and then calling `Partial.evaluateCall` on the substituted/evaluated arguments
-/
theorem reeval_eqv_substituting_first (pvals : List Partial.Value) (xfn : ExtFun) {req req' : Partial.Request} (entities : Partial.Entities) {subsmap : Subsmap} :
  req.subst subsmap = some req' →
  let re_evaluated := Partial.evaluateCall xfn pvals >>= λ residual => Partial.evaluateValue (residual.subst subsmap) (entities.subst subsmap)
  let subst_first := (pvals.map (Partial.Value.subst subsmap)).mapM (Partial.evaluateValue · (entities.subst subsmap)) >>= λ args => Partial.evaluateCall xfn args
  match (re_evaluated, subst_first) with
  | (Except.error _, Except.error _) => true -- don't require that the errors are equal
  | (_, _) => re_evaluated = subst_first
:= by
  unfold Partial.evaluateCall
  simp only ; split <;> rename_i h₁
  · simp only [implies_true]
  · -- re-evaluation and subst-first don't _both_ return errors
    rename_i hₑ
    simp at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
    split <;> rename_i h₂ <;> simp only [h₂, bind_assoc, Except.bind_ok, List.mapM_map, Function.comp_apply] at hₑ
    · -- pvals are all concrete
      rename_i vs
      rw [← Subst.subst_concrete_values (pvals := pvals) (by unfold IsAllConcrete ; exists vs)]
      cases h_call : Spec.call xfn vs
      <;> simp only [h_call, Except.bind_err, Except.bind_ok, Except.error.injEq] at hₑ
      case error e =>
        simp only [Except.bind_err]
        cases h₃ : (pvals.map (Partial.Value.subst subsmap)).mapM λ pval => Partial.evaluateValue pval (entities.subst subsmap)
        case error e' => simp only [List.mapM_map] at h₃ ; simp [h₃] at hₑ
        case ok pvals' =>
          rw [← Subst.subst_concrete_values (pvals := pvals) (by unfold IsAllConcrete ; exists vs)] at h₃
          rw [mapM_eval_spec_value _ h₂, Except.ok.injEq] at h₃ ; subst pvals'
          rw [mapM_eval_spec_value _ h₂, Except.bind_ok, List.mapM_map]
          simp only [h_call, List.mapM_some, Except.bind_err, implies_true]
      case ok v =>
        simp only [Subst.subst_concrete_value, Partial.evaluateValue, Except.bind_ok]
        cases h₃ : pvals.mapM λ pval => Partial.evaluateValue pval (entities.subst subsmap)
        case error e' =>
          -- pvals are all concrete, but evaluating them produces an error
          exfalso
          replace ⟨pval, h_pval, h₃⟩ := List.mapM_error_implies_exists_error h₃
          replace ⟨v', _, h₂⟩ := List.mapM_some_implies_all_some h₂ pval h_pval
          cases pval <;> simp at h₂
          case value v'' =>
            subst v''
            simp [Partial.evaluateValue] at h₃
        case ok pvals' =>
          -- pvals are all concrete, and evaluating them produces pvals' ; we'll show pvals = pvals'
          simp only [mapM_eval_spec_value _ h₂, Except.ok.injEq] at h₃ ; subst pvals'
          simp only [mapM_eval_spec_value _ h₂, Except.bind_ok, List.mapM_map]
          simp only [h_call, List.mapM_some, Except.bind_ok, implies_true]
    · -- pvals are not all concrete
      simp only [Except.bind_ok, Partial.Value.subst, Partial.ResidualExpr.subst, List.map₁_eq_map,
        List.mapM_map]
      simp only [Partial.evaluateValue, Partial.evaluateResidual, Partial.evaluateCall]
      rw [List.mapM₁_eq_mapM (Partial.evaluateValue · (entities.subst subsmap)), List.mapM_map]
      intro _ ; rfl
