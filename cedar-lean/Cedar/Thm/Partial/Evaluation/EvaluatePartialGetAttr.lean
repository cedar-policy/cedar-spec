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
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

/-! Theorems about `Partial.getAttr` and `Partial.attrsOf` -/

namespace Cedar.Thm.Partial.Evaluation.EvaluateGetAttr

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Attr EntityUID Error Expr Prim Result)

/--
  `Partial.attrsOf` on concrete arguments is the same as `Spec.attrsOf` on those
  arguments
-/
theorem attrsOf_on_concrete_eqv_concrete {v : Spec.Value} {entities : Spec.Entities} :
  Partial.attrsOf v (Partial.Entities.attrs entities) = (Spec.attrsOf v (Spec.Entities.attrs entities)).map λ m => m.mapOnValues Partial.Value.value
:= by
  unfold Partial.attrsOf Spec.attrsOf Except.map
  cases v <;> simp only
  case prim p =>
    cases p <;> simp only
    case entityUID uid =>
      unfold Partial.Entities.attrs Spec.Entities.attrs Spec.Entities.asPartialEntities
      cases h₁ : entities.findOrErr uid Error.entityDoesNotExist
      <;> simp only [h₁, Map.findOrErr_mapOnValues, Except.map, Spec.EntityData.asPartialEntityData,
        Except.bind_ok, Except.bind_err]

/--
  `Partial.getAttr` on concrete arguments is the same as `Spec.getAttr` on those
  arguments
-/
theorem getAttr_on_concrete_eqv_concrete {v : Spec.Value} {entities : Spec.Entities} {attr : Attr} :
  Partial.getAttr v attr entities = (Spec.getAttr v attr entities).map Partial.Value.value
:= by
  unfold Partial.getAttr Spec.getAttr
  simp only [attrsOf_on_concrete_eqv_concrete, Except.map]
  cases Spec.attrsOf v entities.attrs <;> simp only [Except.bind_err, Except.bind_ok]
  case ok m => simp only [Map.findOrErr_mapOnValues, Except.map]

/--
  if `entities.attrs uid` is `ok` with some attrs, those attrs are a
  well-formed `Map`, and all the values in those attrs are well-formed
-/
theorem partialEntities_attrs_wf {entities : Partial.Entities} {uid : EntityUID} {attrs: Map String Partial.Value}
  (wf_e : entities.WellFormed) :
  entities.attrs uid = .ok attrs →
  attrs.WellFormed ∧ ∀ v ∈ attrs.values, v.WellFormed
:= by
  unfold Partial.Entities.attrs
  intro h₁
  cases h₂ : entities.es.findOrErr uid Error.entityDoesNotExist
  <;> simp only [h₂, Except.bind_err, Except.bind_ok, Except.ok.injEq] at h₁
  case ok attrs =>
    subst h₁
    unfold Partial.Entities.WellFormed Partial.EntityData.WellFormed at wf_e
    have ⟨wf_m, wf_edata⟩ := wf_e ; clear wf_e
    constructor
    · apply (wf_edata _ _).left
      simp only [← Map.findOrErr_ok_iff_in_values (v := attrs) (e := Error.entityDoesNotExist) wf_m]
      exists uid
    · intro pval h₃
      replace h₂ := Map.findOrErr_ok_implies_in_values h₂
      exact (wf_edata attrs h₂).right.right pval h₃

/--
  if `Partial.attrsOf` returns `ok` with some attrs, those attrs are a
  well-formed `Map`, and all the values in those attrs are well-formed
-/
theorem attrsOf_wf {entities : Partial.Entities} {v : Spec.Value} {attrs : Map String Partial.Value}
  (wf₁ : v.WellFormed)
  (wf_e : entities.WellFormed) :
  Partial.attrsOf v entities.attrs = .ok attrs →
  attrs.WellFormed ∧ ∀ v ∈ attrs.values, v.WellFormed
:= by
  unfold Partial.attrsOf
  cases v <;> try simp only [false_implies, Except.ok.injEq]
  case prim p =>
    cases p <;> simp only [false_implies]
    case entityUID uid => exact partialEntities_attrs_wf wf_e
  case record m =>
    intro h₁ ; subst h₁
    unfold Spec.Value.WellFormed at wf₁
    replace ⟨wf₁, wf_vs⟩ := wf₁
    apply And.intro (Map.mapOnValues_wf.mp wf₁)
    intro pval h₁
    have ⟨k, h₁'⟩ := Map.in_values_exists_key h₁
    rw [Map.values_mapOnValues] at h₁
    replace ⟨v, _, h₃⟩ := List.mem_map.mp h₁
    subst h₃
    simp [Partial.Value.WellFormed]
    apply wf_vs (k, v)
    exact Map.in_mapOnValues_in_kvs wf₁ h₁' (by simp)

/--
  if `Partial.getAttr` on a well-formed value and well-formed entities returns
  `ok` with some value, that is a well-formed value as well
-/
theorem getAttr_wf {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities}
  (wf₁ : v₁.WellFormed)
  (wf_e : entities.WellFormed) :
  ∀ v, Partial.getAttr v₁ attr entities = .ok v → v.WellFormed
:= by
  unfold Partial.getAttr
  cases h₁ : Partial.attrsOf v₁ entities.attrs <;> simp
  case ok attrs =>
    have ⟨_, wf_vs⟩ := attrsOf_wf wf₁ wf_e h₁
    intro pval h₂
    exact wf_vs pval (Map.findOrErr_ok_implies_in_values h₂)

/--
  If `Partial.getAttr` returns any partial value, then after any substitution of
  unknowns in `entities`, it returns the same value with that substitution
  applied
-/
theorem getAttr_subst_preserves_attrs {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_v : v₁.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.getAttr v₁ attr entities = .ok pv →
  Partial.getAttr v₁ attr (entities.subst subsmap) = .ok (pv.subst subsmap)
:= by
  cases v₁ <;> simp [Partial.getAttr, Partial.attrsOf]
  case prim p₁ =>
    cases p₁ <;> simp
    case entityUID uid₁ =>
      cases h₁ : entities.attrs uid₁ <;> simp
      case ok attrs =>
        intro h₂
        replace h₂ := Map.findOrErr_ok_implies_in_kvs h₂
        unfold Map.toList at h₂
        have ⟨attrs', h₃, h₄⟩ := Subst.entities_subst_preserves_attrs subsmap h₁ h₂
        simp only [h₃, Except.bind_ok]
        apply (Map.findOrErr_ok_iff_in_kvs _).mpr h₄
        have wf' := Subst.entities_subst_preserves_wf wf_e wf_s
        exact (partialEntities_attrs_wf wf' h₃).left
  case record attrs =>
    simp only [Spec.Value.WellFormed] at wf_v
    simp [Map.findOrErr_ok_iff_in_kvs (Map.mapOnValues_wf.mp wf_v.left)]
    cases pv
    case value v => simp [Subst.subst_concrete_value]
    case residual r =>
      intro h₁
      replace h₁ := Map.in_mapOnValues_in_kvs' wf_v.left h₁
      simp at h₁

/--
  If `Partial.getAttr` returns a concrete value, then it returns the same value
  after any substitution of unknowns in `entities`
-/
theorem getAttr_subst_preserves_evaluation_to_value {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_v : v₁.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.getAttr v₁ attr entities = .ok (.value v) →
  Partial.getAttr v₁ attr (entities.subst subsmap) = .ok (.value v)
:= by
  intro h₁
  have h₂ := getAttr_subst_preserves_attrs wf_v wf_e wf_s h₁
  simpa [Subst.subst_concrete_value] using h₂

/--
  If `Partial.attrsOf` returns an error, then it also returns the same error
  after any substitution of unknowns in `entities`
-/
theorem attrsOf_subst_preserves_errors {v₁ : Spec.Value} {entities : Partial.Entities} {subsmap : Subsmap} :
  Partial.attrsOf v₁ entities.attrs = .error e →
  Partial.attrsOf v₁ (entities.subst subsmap).attrs = .error e
:= by
  simp only [Partial.attrsOf]
  exact match v₁ with
  | .prim (.entityUID uid) => match ha : entities.attrs uid with
    | .ok attrs => match ha' : (entities.subst subsmap).attrs uid with
      | .ok attrs' => by simp only [ha, ha', imp_self]
      | .error e' => by simp only [ha, ha', Except.error.injEq, false_implies]
    | .error e' => by
      simp only [ha, Except.error.injEq]
      intro h ; subst e'
      simp only [(Subst.entities_subst_preserves_error_attrs subsmap).mp ha]
  | .record attrs => by simp only [imp_self]
  | .prim (.bool _) | .prim (.int _) | .prim (.string _) | .set _ | .ext _ => by
    simp only [Except.error.injEq, imp_self]

/--
  If `Partial.getAttr` returns an error, then it also returns an error (not
  necessarily the same error) after any substitution of unknowns in `entities`
-/
theorem getAttr_subst_preserves_errors {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_v : v₁.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.getAttr v₁ attr entities = .error e →
  ∃ e', Partial.getAttr v₁ attr (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.getAttr]
  /- progress on refactoring this to use `attrsOf_subst_preserves_errors`
      instead of unfolding `Partial.attrsOf` directly and essentially repeating that
      proof
  cases h₁ : Partial.attrsOf v₁ entities.attrs <;> simp
  case error e' => intro _ ; subst e' ; simp [attrsOf_subst_preserves_errors h₁]
  case ok attrs =>
    cases h₂ : Partial.attrsOf v₁ (entities.subst subsmap).attrs <;> simp
    case ok attrs' =>
      exact match e with
      | .attrDoesNotExist => by
        have wf_attrs := attrsOf_wf wf_v wf_e h₁
        have wf_attrs' := attrsOf_wf wf_v (Subst.entities_subst_preserves_wf wf_e wf_s) h₂
        intro h₃ ; exists .attrDoesNotExist
        simp only [Map.findOrErr_err_iff_not_in_keys (wf_attrs.left)] at h₃
        simp only [Map.findOrErr_err_iff_not_in_keys (wf_attrs'.left)]
      | .entityDoesNotExist | .typeError | .arithBoundsError | .extensionError => by
        intro h₃ ; rcases Map.findOrErr_returns attrs attr Error.attrDoesNotExist with h₄ | h₄
        · simp only [h₃, exists_const] at h₄
        · simp only [h₃, Except.error.injEq] at h₄
  -/
  simp only [Partial.attrsOf]
  exact match v₁ with
  | .prim (.entityUID uid) => match ha : entities.attrs uid with
    | .ok attrs => match ha' : (entities.subst subsmap).attrs uid with
      | .ok attrs' => match e with
        | .attrDoesNotExist => by
          simp only [ha, ha', Except.bind_ok]
          have wf_attrs := EvaluateGetAttr.partialEntities_attrs_wf wf_e ha
          have wf_attrs' := EvaluateGetAttr.partialEntities_attrs_wf (Subst.entities_subst_preserves_wf wf_e wf_s) ha'
          intro h₁
          exists .attrDoesNotExist
          simp only [Map.findOrErr_err_iff_not_in_keys (wf_attrs.left)] at h₁
          simp only [Map.findOrErr_err_iff_not_in_keys (wf_attrs'.left)]
          replace ⟨attrs'', ha'', h₁⟩ := Subst.entities_subst_preserves_absent_attrs subsmap ha h₁
          simp [ha'] at ha'' ; subst attrs''
          exact h₁
        | .entityDoesNotExist | .typeError | .arithBoundsError | .extensionError => by
          simp only [ha, ha', Except.bind_ok]
          intro h₁ ; rcases Map.findOrErr_returns attrs attr Error.attrDoesNotExist with h₂ | h₂
          · simp only [h₁, exists_const] at h₂
          · simp only [h₁, Except.error.injEq] at h₂
      | .error e' => by
        simp only [ha, ha', Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq',
          implies_true]
    | .error e' => by
      simp only [ha, Except.bind_err, Except.error.injEq]
      intro h ; subst e'
      simp [(Subst.entities_subst_preserves_error_attrs subsmap).mp ha]
  | .record attrs => by
    simp only [Except.bind_ok]
    intro _ ; exists e
  | .prim (.bool _) | .prim (.int _) | .prim (.string _) => by simp
  | .set _ | .ext _ => by simp

/--
  If `Partial.getAttr` returns a residual that evaluates to an error, and after
  any substitution of unknowns in `entities` it still returns any `.ok`, then
  `Partial.evaluateValue` on the returned value produces an error (not
  necessarily the same error)

  The inductive hypothesis `ih` says that `subst_preserves_errors` holds for `r`
-/
theorem getAttr_subst_preserves_twostep_errors {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap} {r : Partial.ResidualExpr} {e : Error}
  (wf_v : v₁.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (ih :
    Partial.evaluateResidual r entities = .error e →
    ∃ e', Partial.evaluateValue (r.subst subsmap) (entities.subst subsmap) = .error e') :
  Partial.getAttr v₁ attr entities = .ok (.residual r) →
  Partial.evaluateResidual r entities = .error e →
  Partial.getAttr v₁ attr (entities.subst subsmap) = .ok pv' →
  ∃ e', Partial.evaluateValue pv' (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.getAttr]
  cases h₁ : Partial.attrsOf v₁ entities.attrs <;> simp
  case ok attrs =>
    have wf_attrs : attrs.WellFormed := (attrsOf_wf wf_v wf_e h₁).left
    rw [Map.findOrErr_ok_iff_in_kvs wf_attrs]
    cases h₂ : Partial.attrsOf v₁ (entities.subst subsmap).attrs <;> simp
    case ok attrs' =>
      have wf_attrs' : attrs'.WellFormed := (attrsOf_wf wf_v (Subst.entities_subst_preserves_wf wf_e wf_s) h₂).left
      rw [Map.findOrErr_ok_iff_in_kvs wf_attrs']
      intro h₃
      have ⟨attrs'', hattrs'', h₄⟩ := Subst.attrsOf_subst_preserves_attrs subsmap wf_v h₁ h₃
      simp only [h₂, Except.ok.injEq] at hattrs'' ; subst attrs''
      intro h₅ h₆
      have h₇ := Map.key_maps_to_one_value attr _ _ attrs' wf_attrs' h₄ h₆ ; subst pv' ; clear h₆
      simp only [Partial.Value.subst, ih h₅]
