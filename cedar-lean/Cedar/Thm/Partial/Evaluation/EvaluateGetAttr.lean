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
import Cedar.Thm.Partial.WellFormed
import Cedar.Thm.Partial.Subst

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
  `Partial.evaluateGetAttr` on concrete arguments is the same as `Spec.getAttr`
  on those arguments
-/
theorem on_concrete_eqv_concrete {v : Spec.Value} {a : Attr} {entities : Spec.Entities} :
  Partial.evaluateGetAttr v a entities = Spec.getAttr v a entities
:= by
  simp only [Partial.evaluateGetAttr, getAttr_on_concrete_eqv_concrete, pure, Except.pure, Except.map]
  cases Spec.getAttr v a entities <;> simp only [Except.bind_ok, Except.bind_err]

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
  if `Partial.evaluateGetAttr` on a well-formed value and well-formed entities
  returns `ok` with some value, that is a well-formed value as well
-/
theorem evaluateGetAttr_wf {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities}
  (wf₁ : pval₁.WellFormed)
  (wf_e : entities.WellFormed) :
  ∀ pval, Partial.evaluateGetAttr pval₁ attr entities = .ok pval → pval.WellFormed
:= by
  unfold Partial.evaluateGetAttr
  cases pval₁ <;> simp only [Except.bind_ok]
  case residual r₁ =>
    intro pval h_pval
    simp only [Except.ok.injEq] at h_pval
    subst pval
    simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
  case value v₁ =>
    simp [Partial.Value.WellFormed] at wf₁
    exact getAttr_wf wf₁ wf_e

/--
  If `Partial.getAttr` returns a concrete value, then it returns the same value
  after any substitution of unknowns in `entities`
-/
theorem getAttr_subst_preserves_evaluation_to_value {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.getAttr v₁ attr entities = .ok (.value v) →
  Partial.getAttr v₁ attr (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.getAttr
  unfold Partial.attrsOf
  cases v₁
  case prim p₁ =>
    cases p₁ <;> simp only [Except.bind_err, imp_self]
    case entityUID uid₁ =>
      cases h₁ : entities.attrs uid₁
      <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
      case ok attrs =>
        intro h₂
        replace h₂ := Map.findOrErr_ok_implies_in_kvs h₂
        unfold Map.toList at h₂
        have ⟨attrs', h₃, h₄⟩ := Subst.entities_subst_preserves_concrete_attrs subsmap h₁ h₂
        simp only [h₃, Except.bind_ok]
        apply (Map.findOrErr_ok_iff_in_kvs _).mpr h₄
        have wf' := Subst.entities_subst_preserves_wf wf_e wf_s
        exact (partialEntities_attrs_wf wf' h₃).left
  case set | record => simp
  case ext x => cases x <;> simp

/--
  If `Partial.evaluateGetAttr` returns a concrete value, then it returns the
  same value after any substitution of unknowns in `entities`
-/
theorem subst_preserves_evaluation_to_value {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.evaluateGetAttr pval₁ attr entities = .ok (.value v) →
  Partial.evaluateGetAttr pval₁ attr (entities.subst subsmap) = .ok (.value v)
:= by
  unfold Partial.evaluateGetAttr
  cases pval₁ <;> simp only [Except.bind_ok]
  case value v₁ => exact match h₁ : Partial.getAttr v₁ attr entities with
    | .error _ => by simp only [Except.bind_err, false_implies]
    | .ok (.residual r₁) => by simp only [Except.ok.injEq, false_implies]
    | .ok (.value v₁') => by
      simp only [Except.bind_ok, getAttr_subst_preserves_evaluation_to_value wf_e wf_s h₁]
      simp only [Partial.evaluateValue, Except.ok.injEq, Partial.Value.value.injEq, imp_self]
  case residual r₁ => simp only [Except.ok.injEq, imp_self]

/--
  If `Partial.getAttr` returns an error, then it also returns an error (not
  necessarily the same error) after any substitution of unknowns in `entities`
-/
theorem getAttr_subst_preserves_errors {v₁ : Spec.Value} {attr : Attr} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.getAttr v₁ attr entities = .error e →
  ∃ e', Partial.getAttr v₁ attr (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.getAttr, Partial.attrsOf]
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
      | .error e => by
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
  If `Partial.evaluateGetAttr` returns an error, then it also returns an error
  (not necessarily the same error) after any substitution of unknowns in
  `entities`
-/
theorem subst_preserves_errors {pval₁ : Partial.Value} {attr : Attr} {entities : Partial.Entities} (subsmap : Subsmap)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  Partial.evaluateGetAttr pval₁ attr entities = .error e →
  ∃ e', Partial.evaluateGetAttr pval₁ attr (entities.subst subsmap) = .error e'
:= by
  simp only [Partial.evaluateGetAttr]
  cases pval₁ <;> simp only [exists_false, imp_self]
  case value v₁ => exact getAttr_subst_preserves_errors wf_e wf_s
