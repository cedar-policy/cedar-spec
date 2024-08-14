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
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.EvaluateHasAttr

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr Error Expr Prim Result)

/--
  `Partial.attrsOf` on concrete arguments is the same as `Spec.attrsOf` on those
  arguments

  Note that the "concrete arguments" provided to `Partial.attrsOf` and
  `Spec.attrsOf` in this theorem are different from the "concrete arguments"
  provided in the theorem of the same name in Partial/Evaluation/EvaluateGetAttr.lean
-/
theorem attrsOf_on_concrete_eqv_concrete {v : Spec.Value} {entities : Spec.Entities} :
  Partial.attrsOf v (λ uid => .ok (entities.asPartialEntities.attrsOrEmpty uid)) =
  (Spec.attrsOf v (λ uid => .ok (entities.attrsOrEmpty uid))).map λ m => m.mapOnValues Partial.Value.value
:= by
  unfold Partial.attrsOf Spec.attrsOf Except.map
  cases v <;> simp only
  case prim p =>
    cases p <;> simp only
    case entityUID uid =>
      unfold Partial.Entities.attrsOrEmpty Spec.Entities.attrsOrEmpty Spec.Entities.asPartialEntities
      cases h₁ : (entities.mapOnValues Spec.EntityData.asPartialEntityData).find? uid
      <;> simp only [Except.ok.injEq]
      <;> cases h₂ : entities.find? uid <;> simp only
      <;> unfold Spec.EntityData.asPartialEntityData at h₁
      <;> simp only [← Map.find?_mapOnValues, Option.map_eq_none', Option.map_eq_some'] at h₁
      case none.none => simp [Map.mapOnValues_empty]
      case none.some => simp [h₁] at h₂
      case some.none => simp [h₂] at h₁
      case some.some edata₁ edata₂ =>
        replace ⟨edata₁, ⟨h₁, h₃⟩⟩ := h₁
        simp only [h₂, Option.some.injEq] at h₁
        subst h₁ h₃
        simp [Map.mapOnValues]

/--
  `Partial.hasAttr` on concrete arguments is the same as `Spec.hasAttr` on those
  arguments
-/
theorem hasAttr_on_concrete_eqv_concrete {v : Spec.Value} {entities : Spec.Entities} {attr : Attr} :
  Partial.hasAttr v attr entities = Spec.hasAttr v attr entities
:= by
  unfold Partial.hasAttr Spec.hasAttr
  simp only [attrsOf_on_concrete_eqv_concrete, Except.map]
  cases Spec.attrsOf v λ uid => .ok (entities.attrsOrEmpty uid)
  <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Spec.Value.prim.injEq, Spec.Prim.bool.injEq]
  case ok m => simp [← Map.mapOnValues_contains]

/--
  `Partial.evaluateHasAttr` on concrete arguments is the same as `Spec.hasAttr`
  on those arguments
-/
theorem on_concrete_eqv_concrete {v : Spec.Value} {a : Attr} {entities : Spec.Entities} :
  Partial.evaluateHasAttr v a entities = Spec.hasAttr v a entities
:= by
  simp [Partial.evaluateHasAttr, hasAttr_on_concrete_eqv_concrete, pure, Except.pure]

/--
  if `Partial.hasAttr` returns `ok` with some value, that is a well-formed value
-/
theorem partialHasAttr_wf {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} :
  ∀ v, Partial.hasAttr v₁ attr entities = .ok v → v.WellFormed
:= by
  unfold Partial.hasAttr
  cases Partial.attrsOf v₁ λ uid => .ok (entities.attrsOrEmpty uid) <;> simp
  case ok m => simp [Spec.Value.WellFormed, Prim.WellFormed]

/--
  if `Partial.evaluateHasAttr` on a well-formed value returns `ok` with some
  value, that is also a well-formed value
-/
theorem evaluateHasAttr_wf {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities}
  (wf : pval₁.WellFormed) :
  ∀ pval, Partial.evaluateHasAttr pval₁ attr entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.evaluateHasAttr
  cases pval₁ <;> simp only [Except.ok.injEq, forall_eq']
  case value v₁ =>
    cases h₁ : Partial.hasAttr v₁ attr entities
    case error e => simp only [Except.bind_err, false_implies, implies_true]
    case ok v =>
      simp only [Partial.Value.WellFormed, Except.bind_ok, Except.ok.injEq, forall_eq']
      exact partialHasAttr_wf v h₁
  case residual r₁ =>
    simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
    simpa [Partial.Value.WellFormed] using wf

/--
  If `Partial.evaluateHasAttr` produces `ok` with a concrete value, then so
  would partial-evaluating its operand
-/
theorem returns_concrete_then_operand_evals_to_concrete {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} :
  Partial.evaluateHasAttr pval₁ attr entities = .ok (.value v) →
  ∃ v₁, pval₁ = .value v₁
:= by
  unfold Partial.evaluateHasAttr
  intro h₁
  cases pval₁
  case value v₁ => exists v₁
  case residual r₁ => simp only [Except.ok.injEq] at h₁

/--
  The return value of `Partial.hasAttr` is not affected by substitution of
  unknowns in `entities`
-/
theorem hasAttr_subst_const {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} (subsmap : Subsmap)
  (wf : entities.WellFormed) :
  Partial.hasAttr v₁ attr entities = Partial.hasAttr v₁ attr (entities.subst subsmap)
:= by
  unfold Partial.hasAttr Partial.attrsOf
  cases v₁ <;> simp only [Except.bind_ok, Except.bind_err]
  case prim p₁ =>
    cases p₁
    <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Spec.Value.prim.injEq, Spec.Prim.bool.injEq]
    case entityUID uid =>
      exact Subst.entities_subst_preserves_contains_on_attrsOrEmpty entities uid attr subsmap wf

/--
  If `Partial.evaluateHasAttr` returns a concrete value, then it returns the
  same value after any substitution of unknowns in `entities`
-/
theorem subst_preserves_evaluation_to_value {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} (subsmap : Subsmap)
  (wf : entities.WellFormed) :
  Partial.evaluateHasAttr pval₁ attr entities = .ok (.value v) →
  Partial.evaluateHasAttr pval₁ attr (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.evaluateHasAttr
  cases pval₁ <;> simp only [Except.ok.injEq, imp_self]
  case value v₁ => simp only [← hasAttr_subst_const subsmap wf, imp_self]

/--
  If `Partial.hasAttr` returns an error, then it also returns an error (not
  necessarily the same error) after any substitution of unknowns in `entities`
-/
theorem hasAttr_subst_preserves_errors {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} (subsmap : Subsmap) :
  Partial.hasAttr v₁ attr entities = .error e →
  ∃ e', Partial.hasAttr v₁ attr (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.hasAttr, Partial.attrsOf]
  exact match v₁ with
  | .prim (.entityUID uid) => by simp only [Except.bind_ok, exists_false, imp_self]
  | .record attrs => by simp only [Except.bind_ok, exists_false, imp_self]
  | .prim (.bool _) | .prim (.int _) | .prim (.string _) => by simp
  | .set _ | .ext _ => by simp

/--
  If `Partial.evaluateHasAttr` returns an error, then it also returns an error
  (not necessarily the same error) after any substitution of unknowns in
  `entities`
-/
theorem subst_preserves_errors {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} (subsmap : Subsmap) :
  Partial.evaluateHasAttr pval₁ attr entities = .error e →
  ∃ e', Partial.evaluateHasAttr pval₁ attr (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.evaluateHasAttr]
  cases pval₁ <;> simp only [exists_false, imp_self]
  case value v₁ =>
    intro h₁
    rw [do_error] at h₁
    have ⟨e', h₂⟩ := hasAttr_subst_preserves_errors subsmap h₁
    exists e'
    simp only [h₂, Except.bind_err]

/--
  Variant of `subst_preserves_errors` where `Partial.evaluateValue` is applied
  to the argument first

  This takes the proof of `EvaluateValue.evalValue_wf` as an argument, because this
  file can't directly import `Thm/Partial/Evaluation/EvaluateValue.lean` to get it.
  See #372.

  This takes the proof of
  `EvaluateValue.evalResidual_subst_preserves_evaluation_to_value` as an
  argument, because this file can't directly import
  `Thm/Partial/Evaluation/EvaluateValue.lean` to get it.
  See #372.
-/
theorem subst_and_reduce_preserves_errors {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_v : pval₁.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (h_pevwf : ∀ pv es pv', pv.WellFormed → es.WellFormed → Partial.evaluateValue pv es = .ok pv' → pv'.WellFormed)
  (h_erspetv : ∀ r es v, r.WellFormed → es.WellFormed →
    Partial.evaluateResidual r es = .ok (.value v) →
    Partial.evaluateValue (r.subst subsmap) (es.subst subsmap) = .ok (.value v) ) :
  Partial.evaluateValue pval₁ entities = .ok pval₂ →
  Partial.evaluateHasAttr pval₂ attr entities = .error e →
  Partial.evaluateValue (pval₁.subst subsmap) (entities.subst subsmap) = .ok pval₃ →
  ∃ e', Partial.evaluateHasAttr pval₃ attr (entities.subst subsmap) = .error e'
:= by
  cases pval₁ <;> simp [Partial.evaluateValue]
  case value v₁ =>
    intro _ ; subst pval₂
    simp [Subst.subst_concrete_value, Partial.evaluateValue]
    intro h₁ h₂ ; subst pval₃
    exact subst_preserves_errors subsmap h₁
  case residual r₁ =>
    simp only [Partial.Value.WellFormed] at wf_v
    specialize h_erspetv r₁ entities ; simp only [wf_v, wf_e] at h_erspetv
    intro h₁ h₂ h₃
    have wf₃ : pval₃.WellFormed := by
      apply h_pevwf ((Partial.Value.residual r₁).subst subsmap) (entities.subst subsmap) pval₃ _ _ h₃
      · apply Subst.val_subst_preserves_wf _ wf_s
        simp [Partial.Value.WellFormed, wf_v]
      · exact Subst.entities_subst_preserves_wf wf_e wf_s
    apply subst_preserves_errors
    cases pval₂ <;> simp [Partial.Value.subst] at *
    case a.value v₂ =>
      simp [h_erspetv v₂ h₁] at h₃ ; subst pval₃
      exact h₂
    case a.residual r₂ => simp [Partial.evaluateHasAttr] at h₂

/--
  If reducing the arg then `Partial.evaluateHasAttr` returns a concrete value,
  then any subst before that process shouldn't make a difference.

  This is like `subst_preserves_evaluation_to_value` but with a reduce operation
  in front of the `Partial.evaluateHasAttr` in both cases

  Takes an inductive hypothesis `ih` which says that
  `subst_preserves_evaluation_to_value` holds for `pv₁`
-/
theorem subst_preserves_reduce_evaluation_to_value {pv₁ pv₂ : Partial.Value} {attr : Attr} {entities : Partial.Entities} (subsmap : Subsmap)
  (wf_e : entities.WellFormed)
  (ih : ∀ v, Partial.evaluateValue pv₁ entities = .ok (.value v) → Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap) = .ok (.value v)) :
  Partial.evaluateValue pv₁ entities = .ok pv₂ →
  Partial.evaluateHasAttr pv₂ attr entities = .ok (.value v) →
  ∃ pv₃,
    Partial.evaluateValue (pv₁.subst subsmap) (entities.subst subsmap) = .ok pv₃ ∧
    Partial.evaluateHasAttr pv₃ attr (entities.subst subsmap) = .ok (.value v)
:= by
  cases pv₁ <;> simp [Partial.evaluateHasAttr]
  case value v₁ =>
    simp [Subst.subst_concrete_value, Partial.evaluateValue]
    intro _ ; subst pv₂
    simp only [do_ok, Partial.Value.value.injEq, exists_eq_right]
    simp only [hasAttr_subst_const subsmap wf_e, imp_self]
  case residual r₁ =>
    cases pv₂ <;> simp only [Except.ok.injEq, false_implies, implies_true]
    case value v₂ =>
      intro h₁ h₂
      rw [hasAttr_subst_const subsmap wf_e] at h₂
      specialize ih v₂ h₁
      exists (.value v₂)
