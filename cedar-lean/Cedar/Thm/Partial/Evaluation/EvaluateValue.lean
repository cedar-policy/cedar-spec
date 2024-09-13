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
import Cedar.Partial.Value
import Cedar.Spec.Evaluator
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.EvaluateBinaryApp
import Cedar.Thm.Partial.Evaluation.EvaluateCall
import Cedar.Thm.Partial.Evaluation.EvaluateGetAttr
import Cedar.Thm.Partial.Evaluation.EvaluateHasAttr
import Cedar.Thm.Partial.Evaluation.EvaluateUnaryApp
import Cedar.Thm.Partial.Evaluation.Evaluate.Record
import Cedar.Thm.Partial.Evaluation.ReevaluateHasAttr
import Cedar.Thm.Partial.Evaluation.ReevaluateUnaryApp
import Cedar.Thm.Partial.WellFormed

/-! This file contains theorems about `Partial.evaluateValue` (and `Partial.evaluateResidual`). -/

namespace Cedar.Thm.Partial.Evaluation.EvaluateValue

open Cedar.Data
open Cedar.Partial (Subsmap)
open Cedar.Spec (Attr BinaryOp Error ExtFun Prim UnaryOp)

/--
  `Partial.evaluateValue` of a Spec.Value always succeeds and returns the value
-/
theorem eval_spec_value (v : Spec.Value) (entities : Partial.Entities) :
  Partial.evaluateValue v entities = .ok (.value v)
:= by
  simp [Partial.evaluateValue]

theorem sizeOf_lt_ite (pv₁ pv₂ pv₃ : Partial.Value) :
  sizeOf pv₁ < sizeOf (Partial.ResidualExpr.ite pv₁ pv₂ pv₃) ∧
  sizeOf pv₂ < sizeOf (Partial.ResidualExpr.ite pv₁ pv₂ pv₃) ∧
  sizeOf pv₃ < sizeOf (Partial.ResidualExpr.ite pv₁ pv₂ pv₃)
:= by simp_wf ; omega

theorem sizeOf_lt_and (pv₁ pv₂ : Partial.Value) :
  sizeOf pv₁ < sizeOf (Partial.ResidualExpr.and pv₁ pv₂) ∧
  sizeOf pv₂ < sizeOf (Partial.ResidualExpr.and pv₁ pv₂)
:= by simp_wf ; omega

theorem sizeOf_lt_or (pv₁ pv₂ : Partial.Value) :
  sizeOf pv₁ < sizeOf (Partial.ResidualExpr.or pv₁ pv₂) ∧
  sizeOf pv₂ < sizeOf (Partial.ResidualExpr.or pv₁ pv₂)
:= by simp_wf ; omega

theorem sizeOf_lt_unaryApp (op : UnaryOp) (pv₁ : Partial.Value) :
  sizeOf pv₁ < sizeOf (Partial.ResidualExpr.unaryApp op pv₁)
:= by simp_wf ; omega

theorem sizeOf_lt_binaryApp (op : BinaryOp) (pv₁ pv₂ : Partial.Value) :
  sizeOf pv₁ < sizeOf (Partial.ResidualExpr.binaryApp op pv₁ pv₂) ∧
  sizeOf pv₂ < sizeOf (Partial.ResidualExpr.binaryApp op pv₁ pv₂)
:= by simp_wf ; omega

theorem sizeOf_lt_getAttr (pv₁ : Partial.Value) (attr : Attr) :
  sizeOf pv₁ < sizeOf (Partial.ResidualExpr.getAttr pv₁ attr)
:= by simp_wf ; omega

theorem sizeOf_lt_hasAttr (pv₁ : Partial.Value) (attr : Attr) :
  sizeOf pv₁ < sizeOf (Partial.ResidualExpr.hasAttr pv₁ attr)
:= by simp_wf ; omega

theorem sizeOf_lt_set (pvs : List Partial.Value) :
  sizeOf pvs < sizeOf (Partial.ResidualExpr.set pvs)
:= by simp_wf ; omega

theorem sizeOf_lt_record (pvs : List (Attr × Partial.Value)) :
  sizeOf pvs < sizeOf (Partial.ResidualExpr.record pvs)
:= by simp_wf ; omega

theorem sizeOf_lt_call (xfn : ExtFun) (pvs : List Partial.Value) :
  sizeOf pvs < sizeOf (Partial.ResidualExpr.call xfn pvs)
:= by simp_wf ; omega

mutual

/--
  `Partial.evaluateResidual` always returns well-formed results
-/
theorem evalResidual_wf {r : Partial.ResidualExpr} {entities : Partial.Entities}
  (wf_r : r.WellFormed)
  (wf_e : entities.WellFormed) :
  Partial.evaluateResidual r entities = .ok pv → pv.WellFormed
:= by
  cases r <;> simp only [Partial.evaluateResidual, Except.ok.injEq, Bool.not_eq_true']
  <;> simp only [Partial.ResidualExpr.WellFormed] at wf_r
  case unknown u => intro _ ; subst pv ; simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
  case and pv₁ pv₂ | or pv₁ pv₂ =>
    have := sizeOf_lt_and pv₁ pv₂
    have := sizeOf_lt_or pv₁ pv₂
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      cases pv₁' <;> simp only [Except.ok.injEq]
      case residual r₁' =>
        intro _ ; subst pv ; simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
        apply And.intro _ wf_r.right
        have h₁ := evalValue_wf wf_r.left wf_e hpv₁
        simpa [Partial.Value.WellFormed] using h₁
      case value v₁' =>
        cases v₁'.asBool <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
        case ok b₁' =>
          cases b₁' <;> simp only [reduceIte, Except.ok.injEq, Bool.true_eq_false]
          all_goals try {
            -- this resolves the `false` case for `and`, and the `true` case for `or`
            intro _ ; subst pv ; simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
          }
          cases hpv₂ : Partial.evaluateValue pv₂ entities
          <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
          case ok pv₂' =>
            cases pv₂' <;> simp only [Except.ok.injEq]
            case residual r₂' =>
              intro _ ; subst pv ; simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
              have h₁ := evalValue_wf wf_r.right wf_e hpv₂
              simpa [Partial.Value.WellFormed] using h₁
            case value v₂' =>
              cases v₂'.asBool
              case error e => simp only [Except.bind_err, false_implies]
              case ok b₂' =>
                simp only [Except.bind_ok, Except.ok.injEq]
                intro _ ; subst pv ; simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  case ite pv₁ pv₂ pv₃ =>
    have := sizeOf_lt_ite pv₁ pv₂ pv₃
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      cases pv₁' <;> simp only [Except.ok.injEq]
      case residual r₁' =>
        intro _ ; subst pv ; simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
        simp only [wf_r, and_self, and_true]
        have h₁ := evalValue_wf wf_r.left wf_e hpv₁
        simpa [Partial.Value.WellFormed] using h₁
      case value v₁' =>
        cases v₁'.asBool <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
        case ok b₁' =>
          cases b₁' <;> simp only [Bool.false_eq_true, reduceIte]
          case true => exact evalValue_wf wf_r.right.left wf_e
          case false => exact evalValue_wf wf_r.right.right wf_e
  case unaryApp op pv₁ =>
    have := sizeOf_lt_unaryApp op pv₁
    cases hpv₁' : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      apply EvaluateUnaryApp.evaluateUnaryApp_wf
      exact evalValue_wf wf_r wf_e hpv₁'
  case binaryApp op pv₁ pv₂ =>
    have := sizeOf_lt_binaryApp op pv₁ pv₂
    cases hpv₁' : Partial.evaluateValue pv₁ entities
    <;> cases hpv₂' : Partial.evaluateValue pv₂ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok.ok =>
      apply EvaluateBinaryApp.evaluateBinaryApp_wf
      · exact evalValue_wf wf_r.left wf_e hpv₁'
      · exact evalValue_wf wf_r.right wf_e hpv₂'
  case getAttr pv₁ attr =>
    have := sizeOf_lt_getAttr pv₁ attr
    cases hpv₁' : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      have wf₁' : pv₁'.WellFormed := evalValue_wf wf_r wf_e hpv₁'
      apply EvaluateGetAttr.evaluateGetAttr_wf wf₁' wf_e _ pv
      · intro pv pv' ; exact evalValue_wf (pv := pv) (pv' := pv') (wf_e := wf_e)
  case hasAttr pv₁ attr =>
    have := sizeOf_lt_hasAttr pv₁ attr
    cases hpv₁' : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      have wf₁' : pv₁'.WellFormed := evalValue_wf wf_r wf_e hpv₁'
      exact EvaluateHasAttr.evaluateHasAttr_wf wf₁' pv
  case set pvs =>
    have := sizeOf_lt_set pvs
    rw [List.mapM₁_eq_mapM (Partial.evaluateValue · entities)]
    cases hpvs' : pvs.mapM (Partial.evaluateValue · entities)
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pvs' =>
      split <;> rename_i h₁ <;> simp only [Except.ok.injEq] <;> intro _ <;> subst pv
      · rename_i vs'
        simp only [Partial.Value.WellFormed, Spec.Value.WellFormed]
        apply And.intro (Set.make_wf vs')
        intro v hv
        replace hv := (Set.make_mem _ _).mpr hv
        replace ⟨pv', hpv', h₁⟩ := List.mapM_some_implies_all_from_some h₁ v hv
        split at h₁ <;> simp only [Option.some.injEq] at h₁ ; subst h₁ ; rename_i v'
        replace ⟨pv, hpv, h₂⟩ := List.mapM_ok_implies_all_from_ok hpvs' v' hpv'
        have := List.sizeOf_lt_of_mem hpv
        have := evalValue_wf (wf_r pv hpv) wf_e h₂
        simpa [Partial.Value.WellFormed] using this
      · simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
        intro pv' hpv'
        replace ⟨pv, hpv, hpvs'⟩ := List.mapM_ok_implies_all_from_ok hpvs' pv' hpv'
        have := List.sizeOf_lt_of_mem hpv
        exact evalValue_wf (wf_r pv hpv) wf_e hpvs'
  case record apvs =>
    have := sizeOf_lt_record apvs
    rw [Evaluate.Record.mapM₂_eq_mapM_partial_bindAttr (Partial.evaluateValue · entities)]
    cases hapvs : apvs.mapM λ kv => match kv with | (k, v) => Partial.bindAttr k (Partial.evaluateValue v entities)
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok apvs' =>
      split <;> simp only [Except.ok.injEq] <;> intro _ <;> subst pv
      · rename_i avs havs
        simp only [Partial.Value.WellFormed, Spec.Value.WellFormed]
        apply And.intro (Map.make_wf avs)
        intro (k, v) hkv
        replace hkv := Map.make_mem_list_mem hkv
        replace ⟨(k', pv'), hpv', havs⟩ := List.mapM_some_implies_all_from_some havs (k, v) hkv
        split at havs <;> simp only [Option.some.injEq, Prod.mk.injEq] at havs
        replace ⟨havs, havs'⟩ := havs ; subst k' v ; rename_i v' hpv'
        simp only at hpv' ; subst hpv'
        replace ⟨pv, hpv, hapvs⟩ := List.mapM_ok_implies_all_from_ok hapvs (k, v') hpv'
        split at hapvs ; rename_i k' pv'
        simp only [Partial.bindAttr, do_ok, Prod.mk.injEq, exists_eq_right_right] at hapvs
        have := List.sizeOf_snd_lt_sizeOf_list hpv
        have := evalValue_wf (wf_r (k', pv') hpv) wf_e hapvs.left
        simpa [Partial.Value.WellFormed] using this
      · simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
        intro (k', pv') hpv'
        replace ⟨(k, pv), hpv, hapvs⟩ := List.mapM_ok_implies_all_from_ok hapvs (k', pv') hpv'
        split at hapvs ; rename_i hapvs'
        simp only [Prod.mk.injEq] at hapvs' ; replace ⟨hapvs', hapvs''⟩ := hapvs' ; subst hapvs' hapvs''
        simp only [Partial.bindAttr, do_ok, Prod.mk.injEq, exists_eq_right_right] at hapvs
        have := List.sizeOf_snd_lt_sizeOf_list hpv
        exact evalValue_wf (wf_r (k, pv) hpv) wf_e hapvs.left
  case call xfn pvs =>
    have := sizeOf_lt_call xfn pvs
    rw [List.mapM₁_eq_mapM (Partial.evaluateValue · entities)]
    cases hpvs : pvs.mapM (Partial.evaluateValue · entities)
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pvs' =>
      apply EvaluateCall.evaluateCall_wf
      intro pv' hpv'
      replace ⟨pv, hpv, hpvs⟩ := List.mapM_ok_implies_all_from_ok hpvs pv' hpv'
      have := List.sizeOf_lt_of_mem hpv
      exact evalValue_wf (wf_r pv hpv) wf_e hpvs
termination_by sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals simp only at *
  all_goals subst r
  all_goals try omega
  case _ => -- the second inductive call for getAttr
    sorry

/--
  `Partial.evaluateValue` always returns well-formed results
-/
theorem evalValue_wf {pv : Partial.Value} {entities : Partial.Entities}
  (wf_pv : pv.WellFormed)
  (wf_e : entities.WellFormed) :
  Partial.evaluateValue pv entities = .ok pv' → pv'.WellFormed
:= by
  cases pv <;> simp only [Partial.evaluateValue, Except.ok.injEq]
  case value v => intro _ ; subst pv' ; exact wf_pv
  case residual r =>
    simp only [Partial.Value.WellFormed] at wf_pv
    exact evalResidual_wf wf_pv wf_e
termination_by sizeOf pv

end

mutual

/--
  If `Partial.evaluateResidual` returns a concrete value, then
  `Partial.evaluateValue` returns the same value after any substitution of
  unknowns
-/
theorem evalResidual_subst_preserves_evaluation_to_value {r : Partial.ResidualExpr} {entities : Partial.Entities} {v : Spec.Value} {subsmap : Subsmap}
  (wf : r.WellFormed)
  (wf_e : entities.WellFormed) :
  Partial.evaluateResidual r entities = .ok (.value v) →
  Partial.evaluateValue (r.subst subsmap) (entities.subst subsmap) = .ok (.value v)
:= by
  cases r <;> simp only [Partial.evaluateResidual, Partial.evaluateValue, Partial.ResidualExpr.subst,
    Except.ok.injEq, false_implies, Bool.not_eq_true']
    <;> simp only [Partial.ResidualExpr.WellFormed] at wf
  case and pv₁ pv₂ | or pv₁ pv₂ =>
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok pv₁' =>
      cases pv₁' <;> simp only [Except.ok.injEq, false_implies]
      case value v₁' =>
        cases hv₁' : v₁'.asBool <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
        case ok b₁' =>
          cases b₁' <;> simp [subst_preserves_evaluation_to_value subsmap wf.left wf_e hpv₁, hv₁']
          all_goals {
            cases hpv₂ : Partial.evaluateValue pv₂ entities <;> simp
            case ok pv₂' =>
              cases pv₂' <;> simp
              case value v₂' =>
                cases hv₂' : v₂'.asBool <;> simp
                case ok b₂' =>
                  intro _ ; subst v
                  simp [subst_preserves_evaluation_to_value subsmap wf.right wf_e hpv₂, hv₂']
          }
  case ite pv₁ pv₂ pv₃ =>
    cases hpv₁ : Partial.evaluateValue pv₁ entities <;> simp
    case ok pv₁' =>
      cases pv₁' <;> simp
      case value v₁' =>
        cases hv₁' : v₁'.asBool <;> simp
        case ok b₁' =>
          cases b₁' <;> simp [subst_preserves_evaluation_to_value subsmap wf.left wf_e hpv₁, hv₁']
          case true =>
            intro hpv₂ ; simp [subst_preserves_evaluation_to_value subsmap wf.right.left wf_e hpv₂]
          case false =>
            intro hpv₃ ; simp [subst_preserves_evaluation_to_value subsmap wf.right.right wf_e hpv₃]
  case unaryApp op pv₁ =>
    cases hpv₁ : Partial.evaluateValue pv₁ entities <;> simp
    case ok pv₁' =>
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap) <;> simp
      case error e =>
        intro h₁
        have h₂ := ReevaluateUnaryApp.reeval_eqv_substituting_first op pv₁ entities subsmap wf
        simp [hpv₁'] at h₂
        split at h₂ <;> rename_i h₃
        <;> simp only [Prod.mk.injEq] at h₃ <;> replace ⟨h₃, h₃'⟩ := h₃
        · simp at h₃' ; subst h₃' ; rename_i e₁
          cases h₄ : Partial.evaluateUnaryApp op pv₁
          <;> simp [h₄] at h₃
          case error e₂ =>
            subst e₂
            simp [EvaluateUnaryApp.reducing_arg_preserves_errors h₄ hpv₁] at h₁
          case ok pv₁'' =>
            have ⟨pv, h₅⟩ :=
              EvaluateUnaryApp.subst_preserves_reduce_evaluation_to_value subsmap
                (by intro v ; exact subst_preserves_evaluation_to_value subsmap wf wf_e)
                hpv₁ h₁
            simp [h₅] at hpv₁'
        · rename_i hₑ
          subst h₃ h₃'
          simp [h₂] at hₑ
      case ok pv₁'' =>
        intro h₁
        have ⟨pv, h₂⟩ :=
          EvaluateUnaryApp.subst_preserves_reduce_evaluation_to_value subsmap
            (by intro v ; exact subst_preserves_evaluation_to_value subsmap wf wf_e)
            hpv₁ h₁
        simp [hpv₁'] at h₂
        simp [h₂]
  case binaryApp op pv₁ pv₂ =>
    have h₁ := EvaluateBinaryApp.reeval_eqv_substituting_first op pv₁ pv₂ entities subsmap wf.left wf.right
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> cases hpv₂ : Partial.evaluateValue pv₂ entities
    <;> simp
    case ok.ok pv₁' pv₂' =>
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> cases hpv₂' : Partial.evaluateValue (pv₂.subst subsmap) (entities.subst subsmap)
      <;> simp
      <;> simp [hpv₁', hpv₂'] at h₁
      case error.error e₁ e₂ | error.ok e₁ pv₂'' =>
        split at h₁ <;> rename_i h₃
        <;> simp only [Prod.mk.injEq] at h₃ <;> replace ⟨h₃, h₃'⟩ := h₃
        · simp at h₃' ; subst h₃' ; rename_i e₃
          cases h₄ : Partial.evaluateBinaryApp op pv₁ pv₂ entities
          <;> simp [h₄] at h₃
          case error e₄ => simp [EvaluateBinaryApp.reducing_arg_preserves_errors h₄ hpv₁ hpv₂]
          case ok pv₁'' =>
            intro h₂
            have ⟨pv₁''', pv₂''', h₅⟩ :=
              EvaluateBinaryApp.subst_preserves_reduce_evaluation_to_value subsmap
                (by intro v ; exact subst_preserves_evaluation_to_value subsmap wf.left wf_e)
                (by intro v ; exact subst_preserves_evaluation_to_value subsmap wf.right wf_e)
                hpv₁ hpv₂ h₂
            simp [h₅] at hpv₁'
        · rename_i hₑ
          subst h₃ h₃'
          simp [h₁] at hₑ
      case ok.error pv₁'' e₂ =>
        split at h₁ <;> rename_i h₃
        <;> simp only [Prod.mk.injEq] at h₃ <;> replace ⟨h₃, h₃'⟩ := h₃
        · simp at h₃' ; subst h₃' ; rename_i e₃
          cases h₄ : Partial.evaluateBinaryApp op pv₁ pv₂ entities
          <;> simp [h₄] at h₃
          case error e₄ => simp [EvaluateBinaryApp.reducing_arg_preserves_errors h₄ hpv₁ hpv₂]
          case ok pv₁'' =>
            intro h₂
            have ⟨pv₁''', pv₂''', h₅⟩ :=
              EvaluateBinaryApp.subst_preserves_reduce_evaluation_to_value subsmap
                (by intro v ; exact subst_preserves_evaluation_to_value subsmap wf.left wf_e)
                (by intro v ; exact subst_preserves_evaluation_to_value subsmap wf.right wf_e)
                hpv₁ hpv₂ h₂
            simp [h₅] at hpv₂'
        · rename_i hₑ
          subst h₃ h₃'
          simp [h₁] at hₑ
      case ok.ok pv₁'' pv₂'' =>
        intro h₂
        have ⟨pv₁'''', pv₂'''', h₅, h₆, h₇⟩ :=
          EvaluateBinaryApp.subst_preserves_reduce_evaluation_to_value subsmap
            (by intro v ; exact subst_preserves_evaluation_to_value subsmap wf.left wf_e)
            (by intro v ; exact subst_preserves_evaluation_to_value subsmap wf.right wf_e)
            hpv₁ hpv₂ h₂
        simp only [h₅, h₆, Except.ok.injEq] at hpv₁' hpv₂'
        subst pv₁'''' pv₂''''
        exact h₇
  case hasAttr pv₁ attr =>
    cases hpv₁ : Partial.evaluateValue pv₁ entities <;> simp
    case ok pv₁' =>
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap) <;> simp
      case error e =>
        intro h₁
        have h₂ := ReevaluateHasAttr.reeval_eqv_substituting_first pv₁ attr subsmap wf_e wf
        simp [hpv₁'] at h₂
        cases h₃ : Partial.evaluateHasAttr pv₁ attr entities
        <;> simp [h₃] at h₂
        <;> simp [Partial.evaluateHasAttr] at h₃
        case error e =>
          subst e
          split at h₃
          · simp [Subst.subst_concrete_value, eval_spec_value] at hpv₁'
          · simp at h₃
        case ok pv₂ =>
          split at h₃
          · simp [Subst.subst_concrete_value, eval_spec_value] at hpv₁'
          · rename_i r₁
            simp only [Partial.Value.WellFormed] at wf
            simp at h₃
            subst pv₂
            simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual] at *
            simp [hpv₁'] at h₂
            replace ⟨v₁, h₁⟩ := EvaluateHasAttr.returns_concrete_then_operand_evals_to_concrete h₁
            subst pv₁'
            simp [evalResidual_subst_preserves_evaluation_to_value wf wf_e hpv₁] at hpv₁'
      case ok pv₁'' =>
        intro h₁
        have ⟨pv, h₂⟩ :=
          EvaluateHasAttr.subst_preserves_reduce_evaluation_to_value subsmap wf_e
            (by intro v ; exact subst_preserves_evaluation_to_value subsmap wf wf_e)
            hpv₁ h₁
        simp [hpv₁'] at h₂
        simp [h₂]
  case getAttr pv₁ attr => sorry
  case set pvs => sorry
  case record attrs => sorry
  case call xfn pvs => sorry

/--
  If `Partial.evaluateValue` returns a concrete value, then it returns the same
  value after any substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {pv : Partial.Value} {entities : Partial.Entities} {v : Spec.Value} (subsmap : Subsmap)
  (wf : pv.WellFormed)
  (wf_e : entities.WellFormed) :
  Partial.evaluateValue pv entities = .ok (.value v) →
  Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap) = .ok (.value v)
:= by
  cases pv <;> simp only [Partial.evaluateValue, Except.ok.injEq, Partial.Value.value.injEq]
  case value v =>
    intro _ ; subst v
    simp only [Subst.subst_concrete_value, eval_spec_value v]
  case residual r =>
    simp only [Partial.Value.subst]
    simp only [Partial.Value.WellFormed] at wf
    exact evalResidual_subst_preserves_evaluation_to_value wf wf_e

end

mutual

/--
  If `Partial.evaluateResidual` returns an error, then `Partial.evaluateValue`
  returns an error (not necessarily the same error) after any substitution of
  unknowns
-/
theorem evalResidual_subst_preserves_errors {r : Partial.ResidualExpr} {entities : Partial.Entities} {e : Error} {subsmap : Subsmap}
  (wf_r : r.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.evaluateResidual r entities = .error e →
  ∃ e', Partial.evaluateValue (r.subst subsmap) (entities.subst subsmap) = .error e'
:= by
  cases r
  <;> simp only [Partial.evaluateResidual, Partial.ResidualExpr.subst, Partial.evaluateValue,
    false_implies, Bool.not_eq_true']
  <;> simp only [Partial.ResidualExpr.WellFormed] at wf_r
  case and pv₁ pv₂ | or pv₁ pv₂ =>
    have := sizeOf_lt_and pv₁ pv₂
    have := sizeOf_lt_or pv₁ pv₂
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq]
    case error e₁ =>
      intro _ ; subst e₁
      have ⟨e₁', h₁⟩ := subst_preserves_errors wf_r.left wf_e wf_s hpv₁
      simp only [h₁, Except.bind_err, Except.error.injEq, exists_eq']
    case ok pv₁' =>
      cases pv₁' <;> simp only [false_implies]
      case value v₁' =>
        simp only [subst_preserves_evaluation_to_value subsmap wf_r.left wf_e hpv₁, Except.bind_ok]
        cases v₁'.asBool
        <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
        case ok b₁' =>
          cases b₁'
          all_goals try {
            -- this discharges the `false` case for `and`, and the `true` case for `or`
            simp only [reduceIte, exists_false, imp_self]
          }
          all_goals {
            simp only [Bool.true_eq_false, reduceIte]
            cases hpv₂ : Partial.evaluateValue pv₂ entities
            <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq]
            case error e₂ =>
              have ⟨e₂', h₁⟩ := subst_preserves_errors wf_r.right wf_e wf_s hpv₂
              simp only [h₁, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
            case ok pv₂' =>
              cases pv₂' <;> simp only [false_implies]
              case value v₂' =>
                simp only [subst_preserves_evaluation_to_value subsmap wf_r.right wf_e hpv₂, Except.bind_ok]
                cases v₂'.asBool
                case error e₂' => intro _ ; exists e₂'
                case ok b₂' => simp only [Except.bind_ok, exists_false, imp_self]
          }
  case ite pv₁ pv₂ pv₃ =>
    have := sizeOf_lt_ite pv₁ pv₂ pv₃
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq]
    case error e₁ =>
      intro _ ; subst e₁
      have ⟨e₁', h₁⟩ := subst_preserves_errors wf_r.left wf_e wf_s hpv₁
      simp only [h₁, Except.bind_err, Except.error.injEq, exists_eq']
    case ok pv₁' =>
      cases pv₁' <;> simp only [false_implies]
      case value v₁' =>
        simp only [subst_preserves_evaluation_to_value subsmap wf_r.left wf_e hpv₁, Except.bind_ok]
        cases v₁'.asBool
        <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
        case ok b₁' =>
          cases b₁' <;> simp only [Bool.false_eq_true, reduceIte]
          case true => exact subst_preserves_errors wf_r.right.left wf_e wf_s
          case false => exact subst_preserves_errors wf_r.right.right wf_e wf_s
  case binaryApp op pv₁ pv₂ =>
    have := sizeOf_lt_binaryApp op pv₁ pv₂
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> cases hpv₂ : Partial.evaluateValue pv₂ entities
    <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq]
    case error.error e₁ e₂ | error.ok e₁ pv₂' =>
      have ⟨e', h₁⟩ := subst_preserves_errors wf_r.left wf_e wf_s hpv₁
      simp only [h₁, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
    case ok.error pv₁' e₂ =>
      intro _ ; subst e₂
      have ⟨e', h₁⟩ := subst_preserves_errors wf_r.right wf_e wf_s hpv₂
      simp only [h₁, Except.bind_err]
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq']
    case ok.ok pv₁' pv₂' =>
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
      case ok pv₁'' =>
        cases hpv₂' : Partial.evaluateValue (pv₂.subst subsmap) (entities.subst subsmap)
        <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
        case ok pv₂'' =>
          intro h₁
          have ⟨e', h₂⟩ := EvaluateBinaryApp.subst_preserves_errors subsmap h₁
          sorry
  case unaryApp op pv₁ =>
    have := sizeOf_lt_unaryApp op pv₁
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq]
    case error e₁ =>
      intro _ ; subst e₁
      have ⟨e₁', h₁⟩ := subst_preserves_errors wf_r wf_e wf_s hpv₁
      simp only [h₁, Except.bind_err, Except.error.injEq, exists_eq']
    case ok pv₁' =>
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
      case ok pv₁'' =>
        sorry
  case getAttr pv₁ attr =>
    have := sizeOf_lt_getAttr pv₁ attr
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq]
    case error e₁ =>
      intro _ ; subst e₁
      have ⟨e₁', h₁⟩ := subst_preserves_errors wf_r wf_e wf_s hpv₁
      simp only [h₁, Except.bind_err, Except.error.injEq, exists_eq']
    case ok pv₁' =>
      have wf_pv₁' : pv₁'.WellFormed := evalValue_wf wf_r wf_e hpv₁
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
      case ok pv₁'' =>
        intro h₁
        apply EvaluateGetAttr.subst_and_reduce_preserves_errors wf_r wf_e wf_s _ _ _ hpv₁ h₁ hpv₁'
        · intro v pv wf_v h₂
          apply subst_preserves_errors _ wf_e wf_s
          exact EvaluateGetAttr.getAttr_wf wf_v wf_e _ h₂
        · intro _ _ _
          exact evalValue_wf
        · intro _ _ _
          apply evalResidual_subst_preserves_evaluation_to_value
  case hasAttr pv₁ attr =>
    have := sizeOf_lt_hasAttr pv₁ attr
    cases hpv₁ : Partial.evaluateValue pv₁ entities
    <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq]
    case error e₁ =>
      intro _ ; subst e₁
      have ⟨e₁', h₁⟩ := subst_preserves_errors wf_r wf_e wf_s hpv₁
      simp only [h₁, Except.bind_err, Except.error.injEq, exists_eq']
    case ok pv₁' =>
      cases hpv₁' : Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
      case ok pv₁'' =>
        intro h₁
        apply EvaluateHasAttr.subst_and_reduce_preserves_errors wf_r wf_e wf_s _ _ hpv₁ h₁ hpv₁'
        · intro _ _ _
          exact evalValue_wf
        · intro _ _ _
          exact evalResidual_subst_preserves_evaluation_to_value
  case set pvs =>
    have := sizeOf_lt_set pvs
    rw [
      List.mapM₁_eq_mapM (Partial.evaluateValue · entities),
      List.mapM₁_eq_mapM (Partial.evaluateValue · (entities.subst subsmap)),
      List.map₁_eq_map,
      List.mapM_map,
    ]
    cases hpvs : pvs.mapM (Partial.evaluateValue · entities)
    <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq]
    case ok pvs' => split <;> simp only [false_implies]
    case error e' =>
      intro _ ; subst e'
      replace ⟨pv, hpv, hpvs⟩ := List.mapM_error_implies_exists_error hpvs
      have ⟨e', h₁⟩ := subst_preserves_errors (wf_r pv hpv) wf_e wf_s hpvs
      have ⟨e'', h₂⟩ := List.element_error_implies_mapM_error (f := λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)) hpv h₁
      simp only [h₂, Except.bind_err, Except.error.injEq, exists_eq']
  case record apvs =>
    have := sizeOf_lt_record apvs
    rw [
      List.map_attach₂_snd,
      Evaluate.Record.mapM₂_eq_mapM_partial_bindAttr (Partial.evaluateValue · entities),
      Evaluate.Record.mapM₂_eq_mapM_partial_bindAttr (Partial.evaluateValue · (entities.subst subsmap)),
      List.mapM_map,
    ]
    cases hapvs : apvs.mapM λ apv => match apv with | (a, pv) => Partial.bindAttr a (Partial.evaluateValue pv entities)
    <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq]
    case ok apvs' => split <;> simp only [false_implies]
    case error e' =>
      intro _ ; subst e'
      replace ⟨(a, pv), hpv, hapvs⟩ := List.mapM_error_implies_exists_error hapvs
      split at hapvs ; rename_i a' pv' h ; simp only [Prod.mk.injEq] at h ; replace ⟨h, h'⟩ := h ; subst a' pv'
      simp only [Partial.bindAttr, do_error] at hapvs
      have ⟨e', h₁⟩ := subst_preserves_errors (wf_r (a, pv) hpv) wf_e wf_s hapvs
      have ⟨e'', h₂⟩ := List.element_error_implies_mapM_error (f := λ (a, pv) => Partial.bindAttr a (Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap))) (e := e') hpv (by
        simp only [Partial.bindAttr, h₁, Except.bind_err]
      )
      simp only [h₂, Except.bind_err, Except.error.injEq, exists_eq']
  case call xfn pvs =>
    have := sizeOf_lt_call xfn pvs
    rw [
      List.mapM₁_eq_mapM (Partial.evaluateValue · entities),
      List.mapM₁_eq_mapM (Partial.evaluateValue · (entities.subst subsmap)),
      List.map₁_eq_map,
      List.mapM_map,
    ]
    cases hpvs : pvs.mapM (Partial.evaluateValue · entities)
    <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq]
    case ok pvs' =>
      cases hpvs' : pvs.mapM λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)
      <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
      case ok pvs'' =>
        -- unlike in the other cases, we don't currently have the proof of `evaluateCall_subst_preserves_errors` pulled out in Call.lean
        sorry
    case error e' =>
      intro _ ; subst e'
      replace ⟨pv, hpv, hpvs⟩ := List.mapM_error_implies_exists_error hpvs
      have ⟨e', h₁⟩ := subst_preserves_errors (wf_r pv hpv) wf_e wf_s hpvs
      have ⟨e'', h₂⟩ := List.element_error_implies_mapM_error (f := λ pv => Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)) hpv h₁
      simp only [h₂, Except.bind_err, Except.error.injEq, exists_eq']
termination_by sizeOf r
decreasing_by all_goals sorry

/--
  If `Partial.evaluateValue` returns an error, then it also returns an error
  (not necessarily the same error) after any substitution of unknowns
-/
theorem subst_preserves_errors {pv : Partial.Value} {entities : Partial.Entities} {e : Error} {subsmap : Subsmap}
  (wf_pv : pv.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.evaluateValue pv entities = .error e →
  ∃ e', Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap) = .error e'
:= by
  cases pv <;> simp only [Partial.evaluateValue, false_implies]
  case residual r =>
    simp only [Partial.Value.subst]
    simp only [Partial.Value.WellFormed] at wf_pv
    exact evalResidual_subst_preserves_errors wf_pv wf_e wf_s
termination_by sizeOf pv

end

/--
  Reducing a value and then substituting it, produces the same result as
  substituting it then reducing it
-/
theorem reduce_commutes_subst {pv : Partial.Value} {entities : Partial.Entities} (subsmap : Subsmap)
  (wf_v : pv.WellFormed)
  (wf_e : entities.WellFormed) :
  Partial.evaluateValue pv entities = .ok pv' →
  Partial.evaluateValue (pv'.subst subsmap) (entities.subst subsmap) =
  Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)
:= match pv with
  | .value v => by
    simp [eval_spec_value]
    intro _ ; subst pv' ; rfl
  | .residual (.unknown u) => by
    simp [Partial.evaluateValue, Partial.evaluateResidual]
    intro _ ; subst pv' ; rfl
  | .residual (.and pv₁ pv₂) | .residual (.or pv₁ pv₂) => by
    simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
    simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed] at wf_v
    exact match h₁ : Partial.evaluateValue pv₁ entities with
    | .error _ => by simp
    | .ok (.value v₁) => by
      simp only [Except.bind_ok, subst_preserves_evaluation_to_value subsmap wf_v.left wf_e h₁]
      exact match hv₁ : v₁.asBool with
      | .error _ => by simp
      | .ok b₁ => by
        cases b₁
        all_goals try {
          -- this dispatches the false case for `and`, and the true case for `or`
          simp only [Except.bind_ok, Bool.true_eq_false, Bool.false_eq_true, reduceIte, Except.ok.injEq]
          intro _ ; subst pv'
          simp only [Subst.subst_concrete_value, eval_spec_value]
        }
        all_goals {
          exact match h₂ : Partial.evaluateValue pv₂ entities with
          | .error _ => by simp
          | .ok (.value v₂) => by
            simp only [Except.bind_ok, Bool.true_eq_false, Bool.false_eq_true, reduceIte,
              subst_preserves_evaluation_to_value subsmap wf_v.right wf_e h₂]
            simp only [do_ok]
            intro ⟨b₂, h₃, h₄⟩ ; subst pv'
            simp only [Subst.subst_concrete_value, eval_spec_value, h₃, Except.bind_ok]
          | .ok (.residual r₂) => by
            simp only [Except.bind_ok, Bool.true_eq_false, Bool.false_eq_true, reduceIte, Except.ok.injEq]
            intro _ ; subst pv'
            simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual, Spec.Value.asBool]
            have h₃ := reduce_commutes_subst subsmap wf_v.right wf_e h₂
            simp only [Partial.Value.subst] at h₃
            simp [h₃]
        }
    | .ok (.residual r₁) => by
      simp only [Except.bind_ok, Except.ok.injEq]
      intro _ ; subst pv'
      simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
      have h₂ := reduce_commutes_subst subsmap wf_v.left wf_e h₁
      simp only [Partial.Value.subst] at h₂
      simp [h₂]
  | .residual (.ite pv₁ pv₂ pv₃) => by
    simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
    sorry
  | .residual (.binaryApp op pv₁ pv₂) => by
    simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
    sorry
  | .residual (.unaryApp op pv₁) => by
    simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
    sorry
  | .residual (.hasAttr pv₁ attr) => by
    simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
    sorry
  | .residual (.getAttr pv₁ attr) => by
    simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
    sorry
  | .residual (.set pvs) => by
    simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
    sorry
  | .residual (.record attrs) => by
    simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
    sorry
  | .residual (.call xfn pvs) => by
    simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual]
    sorry
