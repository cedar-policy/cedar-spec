/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.getAttr` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem getAttrInRecord_has_empty_capabilities {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {rty : RecordType} {ty ty₁ : CedarType} :
  getAttrInRecord ty rty x₁ a c₁ = Except.ok (ty₁, c₂) →
  c₂ = ∅
:= by
  intro h₁
  simp [getAttrInRecord] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  simp [h₁]
  split at h₁ <;> simp at h₁
  simp [h₁]

theorem type_of_getAttr_inversion {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ c₁',
    (∃ ety, typeOf x₁ c₁ env = Except.ok (.entity ety, c₁')) ∨
    (∃ rty, typeOf x₁ c₁ env = Except.ok (.record rty, c₁'))
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    rcases res with ⟨ty₁, c₁'⟩
    simp [typeOfGetAttr] at h₁
    split at h₁ <;> try contradiction
    case mk.h_1 =>
      simp
      apply getAttrInRecord_has_empty_capabilities h₁
    case mk.h_2 =>
      simp
      split at h₁ <;> try simp [err] at h₁
      apply getAttrInRecord_has_empty_capabilities h₁

theorem type_of_getAttr_is_sound_for_records {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {rty : RecordType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, ∅))
  (h₃ : typeOf x₁ c₁ env = Except.ok (CedarType.record rty, c₁'))
  (h₄ : evaluate x₁ request entities = Except.ok v₁)
  (h₅ : InstanceOfType v₁ (CedarType.record rty)) :
  ∃ v,
  (getAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   getAttr v₁ a entities = Except.error Error.extensionError ∨
   getAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   getAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType v ty
:= by
  rcases (instance_of_record_type_is_record h₅) with ⟨r, h₆⟩
  subst h₆
  simp [getAttr, attrsOf, Map.findOrErr]
  cases h₈ : Map.find? r a
  case intro.none =>
    simp only [or_self, false_and, exists_const]
    simp [typeOf, h₃, typeOfGetAttr, getAttrInRecord] at h₂
    split at h₂ <;> simp [ok, err] at h₂
    case h_1 _ _ h₉ =>
      subst h₂
      rcases (required_attribute_is_present h₅ h₉) with ⟨_, h₁₀⟩
      simp [h₈] at h₁₀
    case h_2 =>
      split at h₂ <;> simp at h₂
      subst h₂ ; rename_i h₁₀
      rcases (capability_implies_record_attribute h₁ h₄ h₁₀) with ⟨_, h₁₁⟩
      simp [h₈] at h₁₁
  case intro.some vₐ =>
    simp only [Except.ok.injEq, false_or, exists_eq_left']
    simp [typeOf, h₃, typeOfGetAttr, getAttrInRecord] at h₂
    split at h₂ <;> simp [ok, err] at h₂
    case h_1 _ _ h₉ =>
      subst h₂
      apply instance_of_attribute_type h₅ h₉ (by simp [Qualified.getType]) h₈
    case h_2 _ _ h₉ =>
      split at h₂ <;> simp at h₂
      subst h₂
      apply instance_of_attribute_type h₅ h₉ (by simp [Qualified.getType]) h₈

theorem type_of_getAttr_is_sound_for_entities {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {ety : EntityType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, ∅))
  (h₄ : typeOf x₁ c₁ env = Except.ok (CedarType.entity ety, c₁'))
  (h₅ : evaluate x₁ request entities = Except.ok v₁)
  (h₆ : InstanceOfType v₁ (CedarType.entity ety)) :
  ∃ v,
  (getAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   getAttr v₁ a entities = Except.error Error.extensionError ∨
   getAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   getAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType v ty
:= by
  rcases (instance_of_entity_type_is_entity h₆) with ⟨uid, h₇, h₈⟩
  subst h₈
  simp [getAttr, attrsOf, Entities.attrs, Map.findOrErr]
  cases h₈ : Map.find? entities uid
  case intro.intro.none =>
    simp only [Except.bind_err, Except.error.injEq, or_self, or_false, true_and]
    exact type_is_inhabited ty
  case intro.intro.some d =>
    subst h₇
    simp only [Except.bind_ok]
    cases h₉ : Map.find? d.attrs a
    case none =>
      simp
      simp [typeOf, h₄, typeOfGetAttr, getAttrInRecord] at h₃
      split at h₃ <;> simp [ok, err] at h₃
      split at h₃ <;> try simp at h₃
      case h_1.h_1 _ _ h₁₀ _ _ h₁₁ =>
        subst h₃
        rcases (well_typed_entity_attributes h₂ h₈ h₁₀) with h₁₂
        rcases (required_attribute_is_present h₁₂ h₁₁) with ⟨aᵥ, h₁₃⟩
        simp [h₉] at h₁₃
      case h_1.h_2 =>
        split at h₃ <;> simp at h₃
        subst h₃ ; rename_i h₁₃
        rcases (capability_implies_entity_attribute h₁ h₅ h₈ h₁₃) with ⟨_, h₁₄⟩
        simp [h₉] at h₁₄
    case some vₐ =>
      simp only [Except.ok.injEq, false_or, exists_eq_left']
      simp [typeOf, h₄, typeOfGetAttr, getAttrInRecord] at h₃
      split at h₃ <;> simp [ok, err] at h₃
      split at h₃ <;> try simp at h₃
      case h_1.h_1 _ _ h₁₀ _ _ h₁₁ =>
        subst h₃
        apply instance_of_attribute_type _ h₁₁ (by simp [Qualified.getType]) h₉
        apply well_typed_entity_attributes h₂ h₈ h₁₀
      case h_1.h_2 _ _ h₁₀ _ _ h₁₁ =>
        split at h₃ <;> simp at h₃
        subst h₃
        apply instance_of_attribute_type _ h₁₁ (by simp [Qualified.getType]) h₉
        apply well_typed_entity_attributes h₂ h₈ h₁₀

theorem type_of_getAttr_is_sound {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.getAttr x₁ a) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.getAttr x₁ a) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_getAttr_inversion h₃) with ⟨h₅, c₁', h₄⟩
  subst h₅
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases h₄ with ⟨ety, h₄⟩ | ⟨rty, h₄⟩ <;>
    rcases (ih h₁ h₂ h₄) with ⟨_, v₁, h₆, h₇⟩ <;>
    simp [EvaluatesTo] at h₆ <;>
    simp [EvaluatesTo, evaluate] <;>
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case inl.intro.intro.intro.intro.inr.inr.inr =>
      exact type_of_getAttr_is_sound_for_entities h₁ h₂ h₃ h₄ h₆ h₇
    case inr.intro.intro.intro.intro.inr.inr.inr =>
      exact type_of_getAttr_is_sound_for_records h₁ h₃ h₄ h₆ h₇
    all_goals {
      exact type_is_inhabited ty
    }


end Cedar.Thm
