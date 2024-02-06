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
This file proves that typechecking of `.hasAttr` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_hasAttr_inversion {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂)) :
  (c₂ = ∅ ∨ c₂ = Capabilities.singleton x₁ a) ∧
  ∃ c₁',
    (∃ ety, typeOf x₁ c₁ env = Except.ok (.entity ety, c₁')) ∨
    (∃ rty, typeOf x₁ c₁ env = Except.ok (.record rty, c₁'))
:= by
  simp [typeOf, typeOfHasAttr] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp at h₁
    split at h₁ <;> try simp [err, ok, hasAttrInRecord] at h₁
    case h_1 _ _ =>
      split at h₁ <;> try split at h₁
      all_goals {
        simp [ok] at h₁
        simp [h₁]
      }
    case h_2 _ _ =>
      split at h₁ <;> split at h₁ <;> try split at h₁
      all_goals {
        simp [ok] at h₁
        try simp [h₁]
      }

theorem type_of_hasAttr_is_sound_for_records {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {rty : RecordType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (h₃ : typeOf x₁ c₁ env = Except.ok (CedarType.record rty, c₁'))
  (h₄ : evaluate x₁ request entities = Except.ok v₁)
  (h₅ : InstanceOfType v₁ (CedarType.record rty)) :
  ∃ v,
  (hasAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   hasAttr v₁ a entities = Except.error Error.extensionError ∨
   hasAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   hasAttr v₁ a entities = Except.ok v) ∧
  InstanceOfType v ty
:= by
  have ⟨r, h₅⟩ := instance_of_record_type_is_record h₅
  subst h₅
  simp [hasAttr, attrsOf]
  simp [typeOf, h₃, typeOfHasAttr, hasAttrInRecord] at h₂
  split at h₂
  case h_1 =>
    split at h₂ <;> simp [ok] at h₂ <;>
    have ⟨hₜ, _⟩ := h₂ <;> simp [←hₜ] <;>
    apply InstanceOfType.instance_of_bool <;>
    simp [InstanceOfBoolType]
    cases h₆ : (Map.contains r a) <;> simp
    rename_i h₇ _
    cases h₇
    case inl.h₁.false.inl _ h₇ =>
      simp [CapabilitiesInvariant] at h₁
      specialize h₁ x₁ a h₇
      simp [EvaluatesTo, evaluate, h₄, hasAttr, attrsOf, h₆] at h₁
    case inl.h₁.false.inr h₇ _ h₈ =>
      simp [Qualified.isRequired] at h₈
      split at h₈ <;> simp at h₈
      have h₉ := required_attribute_is_present h₅ h₇
      simp [←Map.contains_iff_some_find?, h₆] at h₉
  case h_2 =>
    simp [ok] at h₂
    have ⟨h₂, _⟩ := h₂
    simp [←h₂]
    apply InstanceOfType.instance_of_bool
    simp [InstanceOfBoolType]
    cases h₆ : (Map.contains r a) <;> simp
    rename_i _ h₇ _ _
    have h₇ := absent_attribute_is_absent h₅ h₇
    simp [Map.contains_iff_some_find?, h₇] at h₆


theorem type_of_hasAttr_is_sound_for_entities {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {ety : EntityType} {request : Request} {entities : Entities} {v₁ : Value}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (h₄ : typeOf x₁ c₁ env = Except.ok (CedarType.entity ety, c₁'))
  (h₅ : evaluate x₁ request entities = Except.ok v₁)
  (h₆ : InstanceOfType v₁ (CedarType.entity ety)) :
  ∃ v,
  (hasAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   hasAttr v₁ a entities = Except.error Error.extensionError ∨
   hasAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   hasAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType v ty
:= by
  have ⟨uid, h₆, h₇⟩ := instance_of_entity_type_is_entity h₆
  subst h₆ h₇
  simp [hasAttr, attrsOf]
  simp [typeOf, h₄, typeOfHasAttr] at h₃
  split at h₃ <;> try simp [err, hasAttrInRecord] at h₃
  rename_i _ rty h₇
  split at h₃
  case h_1.h_1 =>
    split at h₃ <;> rcases h₃ with ⟨h₃, _⟩ <;>
    apply InstanceOfType.instance_of_bool <;>
    simp [InstanceOfBoolType]
    cases h₈ : Map.contains (Entities.attrsOrEmpty entities uid) a <;> simp
    rename_i _ _ _ _  h₉
    simp [CapabilitiesInvariant] at h₁
    specialize h₁ x₁ a h₉
    simp [EvaluatesTo, evaluate, h₅, hasAttr, attrsOf, h₈] at h₁
  case h_1.h_2 =>
    simp [ok] at h₃
    have ⟨h₃, _⟩ := h₃
    simp [←h₃]
    apply InstanceOfType.instance_of_bool
    simp [InstanceOfBoolType]
    cases h₈ : Map.contains (Entities.attrsOrEmpty entities uid) a <;> simp
    rename_i _ _ h₉ _ _
    simp [Entities.attrsOrEmpty] at h₈
    split at h₈
    case h₁.true.h_1 _ _ _ _ _ h₁₀ =>
      have h₁₁ := well_typed_entity_attributes h₂ h₁₀ h₇
      have h₁₂ := absent_attribute_is_absent h₁₁ h₉
      simp [Map.contains_iff_some_find?, h₁₂] at h₈
    case h₁.true.h_2 =>
      rcases (Map.not_contains_of_empty a) with _
      contradiction
  case h_2 =>
    simp [ok] at h₃
    split at h₃ <;> try simp [err, hasAttrInRecord] at h₃
    rcases h₃ with ⟨h₃, _⟩
    simp [←h₃]
    apply InstanceOfType.instance_of_bool
    simp [InstanceOfBoolType]


theorem type_of_hasAttr_is_sound {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.hasAttr x₁ a) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.hasAttr x₁ a) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.hasAttr x₁ a) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₅, c₁', h₄⟩ := type_of_hasAttr_inversion h₃
  apply And.intro
  case left =>
    simp [GuardedCapabilitiesInvariant, CapabilitiesInvariant]
    intro h₆ x aₓ h₇
    cases h₅ <;> rename_i h₈ <;> subst h₈ <;> simp [Capabilities.singleton] at h₇
    have ⟨h₇, h₈⟩ := h₇
    subst h₇; subst h₈
    simp [EvaluatesTo, h₆]
  case right =>
    rcases h₄ with ⟨ety, h₄⟩ | ⟨rty, h₄⟩ <;>
    have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ <;>
    simp [EvaluatesTo] at h₆ <;>
    simp [EvaluatesTo, evaluate] <;>
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case inl.intro.inr.inr.inr =>
      exact type_of_hasAttr_is_sound_for_entities h₁ h₂ h₃ h₄ h₆ h₇
    case inr.intro.inr.inr.inr =>
      exact type_of_hasAttr_is_sound_for_records h₁ h₃ h₄ h₆ h₇
    all_goals {
      exact type_is_inhabited ty
    }

end Cedar.Thm
