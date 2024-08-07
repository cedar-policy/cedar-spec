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
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.EvaluatePartialGetAttr
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Evaluation.ReevaluatePartialGetAttr
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.EvaluateGetAttr

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr EntityUID Error Expr Prim Result)

/--
  `Partial.evaluateGetAttr` on concrete arguments is the same as `Spec.getAttr`
  on those arguments
-/
theorem on_concrete_eqv_concrete {v : Spec.Value} {a : Attr} {entities : Spec.Entities} :
  Partial.evaluateGetAttr v a entities = Spec.getAttr v a entities
:= by
  simp only [Partial.evaluateGetAttr, getAttr_on_concrete_eqv_concrete, pure, Except.pure, Except.map]
  cases Spec.getAttr v a entities <;> simp only [Except.bind_ok, Except.bind_err]
  case ok v' => simp only [Partial.evaluateValue]

/--
  if `Partial.evaluateGetAttr` on a well-formed value and well-formed entities
  returns `ok` with some value, that is a well-formed value as well
-/
theorem evaluateGetAttr_wf {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities}
  (wf₁ : pval₁.WellFormed)
  (wf_e : entities.WellFormed)
  (ih₂ : ∀ {pval pval' : Partial.Value}, pval.WellFormed → Partial.evaluateValue pval entities = .ok pval' → pval'.WellFormed) :
  ∀ pval, Partial.evaluateGetAttr pval₁ attr entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.evaluateGetAttr
  cases pval₁ <;> simp only [Except.bind_ok]
  <;> simp only [Partial.Value.WellFormed] at wf₁
  case residual r₁ =>
    simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed, wf₁]
  case value v₁ =>
    intro pval
    cases h₁ : Partial.getAttr v₁ attr entities <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
    case ok v₁' => exact ih₂ (pval := v₁') (pval' := pval) (getAttr_wf wf₁ wf_e _ h₁)

/--
  If `Partial.evaluateGetAttr` returns a concrete value, then it returns the
  same value after any substitution of unknowns in `entities`

  The inductive hypothesis `ih` says that the theorem holds for `evaluateValue`
  on all values in `entities`
-/
theorem subst_preserves_evaluation_to_value {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_pv : pval₁.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih : ∀ v v' pv,
    v.WellFormed →
    Partial.getAttr v attr entities = .ok pv →
    Partial.evaluateValue pv entities = .ok (.value v') →
    Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap) = .ok (.value v')) :
  Partial.evaluateGetAttr pval₁ attr entities = .ok (.value v) →
  Partial.evaluateGetAttr pval₁ attr (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.evaluateGetAttr
  cases pval₁ <;> simp only [Except.ok.injEq, imp_self]
  case value v₁ => exact match h₁ : Partial.getAttr v₁ attr entities with
    | .error _ => by simp only [Except.bind_err, false_implies]
    | .ok (.residual r₁) => by
      simp only [Partial.Value.WellFormed] at wf_pv
      simp only [Except.bind_ok]
      intro h₂
      specialize ih v₁ v (.residual r₁) wf_pv h₁ h₂
      have h₄ := ReevaluateGetAttr.reeval_eqv_substituting_first_partialGetAttr v₁ attr wf_pv wf_e wf_s
      simp [ih, h₁] at h₄
      exact h₄.symm
    | .ok (.value v₁') => by
      simp only [Partial.Value.WellFormed] at wf_pv
      simp only [Except.bind_ok, getAttr_subst_preserves_evaluation_to_value wf_pv wf_e wf_s h₁]
      simp only [Partial.evaluateValue, Except.ok.injEq, Partial.Value.value.injEq, imp_self]

/--
  If `Partial.evaluateGetAttr` returns an error, then it also returns an error
  (not necessarily the same error) after any substitution of unknowns in
  `entities`

  The inductive hypothesis `ih` says that the theorem holds for `evaluateValue`
  on all values in `entities`
-/
theorem subst_preserves_errors {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_v : pval₁.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih : ∀ v pv,
    v.WellFormed →
    Partial.getAttr v attr entities = .ok pv →
    Partial.evaluateValue pv entities = .error e →
    ∃ e', Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap) = .error e') :
  Partial.evaluateGetAttr pval₁ attr entities = .error e →
  ∃ e', Partial.evaluateGetAttr pval₁ attr (entities.subst subsmap) = .error e'
:= by
  cases pval₁ <;> simp [Partial.evaluateGetAttr]
  case value v₁ =>
    simp only [Partial.Value.WellFormed] at wf_v
    cases h₁ : Partial.getAttr v₁ attr entities <;> simp
    case error e' =>
      intro _ ; subst e'
      have ⟨e', h₂⟩ := getAttr_subst_preserves_errors wf_v wf_e wf_s h₁
      simp [h₂]
    case ok pv₁ =>
      intro h₂
      replace ⟨e', ih⟩ := ih v₁ pv₁ wf_v h₁ h₂
      cases pv₁ <;> simp [Partial.evaluateValue] at *
      case residual r₁ =>
        cases h₃ : Partial.getAttr v₁ attr (entities.subst subsmap) <;> simp
        case ok pv₁ =>
          apply getAttr_subst_preserves_twostep_errors wf_v wf_e wf_s _ h₁ h₂ h₃
          intro _ ; simp [Partial.Value.subst] at ih ; simp [ih]

/--
  Variant of `subst_preserves_errors` where `Partial.evaluateValue` is applied
  to the argument first

  The inductive hypothesis `ih` says that `subst_preserves_errors` holds for
  `evaluateValue` on all values in `entities`

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
  (ih : ∀ v pv,
    v.WellFormed →
    Partial.getAttr v attr entities = .ok pv →
    Partial.evaluateValue pv entities = .error e →
    ∃ e', Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap) = .error e')
  (h_pevwf : ∀ pv es pv', pv.WellFormed → es.WellFormed → Partial.evaluateValue pv es = .ok pv' → pv'.WellFormed)
  (h_erspetv : ∀ r es v, r.WellFormed →
    Partial.evaluateResidual r es = .ok (.value v) →
    Partial.evaluateValue (r.subst subsmap) (es.subst subsmap) = .ok (.value v) ) :
  Partial.evaluateValue pval₁ entities = .ok pval₂ →
  Partial.evaluateGetAttr pval₂ attr entities = .error e →
  Partial.evaluateValue (pval₁.subst subsmap) (entities.subst subsmap) = .ok pval₃ →
  ∃ e', Partial.evaluateGetAttr pval₃ attr (entities.subst subsmap) = .error e'
:= by
  cases pval₁ <;> simp [Partial.evaluateValue]
  case value v₁ =>
    intro _ ; subst pval₂
    simp [Subst.subst_concrete_value, Partial.evaluateValue]
    intro h₁ h₂ ; subst pval₃
    exact subst_preserves_errors wf_v wf_e wf_s ih h₁
  case residual r₁ =>
    simp only [Partial.Value.WellFormed] at wf_v
    specialize h_erspetv r₁ entities ; simp only [wf_v] at h_erspetv
    intro h₁ h₂ h₃
    have wf₃ : pval₃.WellFormed := by
      apply h_pevwf ((Partial.Value.residual r₁).subst subsmap) (entities.subst subsmap) pval₃ _ _ h₃
      · apply Subst.val_subst_preserves_wf _ wf_s
        simp [Partial.Value.WellFormed, wf_v]
      · exact Subst.entities_subst_preserves_wf wf_e wf_s
    apply subst_preserves_errors wf₃ wf_e wf_s ih
    cases pval₂ <;> simp [Partial.Value.subst] at *
    case value v₂ =>
      simp [h_erspetv v₂ h₁] at h₃ ; subst pval₃
      exact h₂
    case residual r₂ => simp [Partial.evaluateGetAttr] at h₂
