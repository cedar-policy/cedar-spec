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

theorem type_of_getAttr_inversion {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {l : Level}
  (h₁ : typeOf (Expr.getAttr x₁ a) c₁ env (l == .infinite) = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ c₁',
    (∃ ety l', typeOf x₁ c₁ env (l == .infinite) = Except.ok (.entity ety l', c₁')) ∨
    (∃ rty, typeOf x₁ c₁ env (l == .infinite) = Except.ok (.record rty, c₁'))
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env (l == .infinite) <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfGetAttr] at h₁
    split at h₁ <;> try contradiction
    case _ =>
      simp only [List.empty_eq, Except.ok.injEq, Prod.mk.injEq, false_and, exists_const,
        CedarType.record.injEq, exists_and_right, exists_eq', true_and, false_or, and_true]
      apply getAttrInRecord_has_empty_capabilities h₁
    case _ =>
      simp [*]
      -- split on level being correct
      split at h₁ <;> try contradiction
      -- split at entity having this attribute
      split at h₁ <;> try contradiction
      simp [bind, Except.bind] at h₁
      split at h₁ <;> try contradiction
      rename_i tuple heq₂
      cases tuple
      rename_i ty caps
      have heq₃ : caps = c₂ := by
        simp at h₁
        apply h₁.right
      subst heq₃
      apply getAttrInRecord_has_empty_capabilities
      apply heq₂


theorem type_of_getAttr_is_sound_for_records {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {rty : RecordType} {request : Request} {entities : Entities} {v₁ : Value} {l : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : typeOf (Expr.getAttr x₁ a) c₁ env (l == .infinite) = Except.ok (ty, ∅))
  (h₃ : typeOf x₁ c₁ env (l == .infinite) = Except.ok (CedarType.record rty, c₁'))
  (h₄ : evaluate x₁ request entities = Except.ok v₁)
  (h₅ : InstanceOfType v₁ (CedarType.record rty)) :
  ∃ v,
  (getAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   getAttr v₁ a entities = Except.error Error.extensionError ∨
   getAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   getAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType v ty
:= by
  have ⟨r, h₆⟩ := instance_of_record_type_is_record h₅
  subst h₆
  simp [getAttr, attrsOf, Map.findOrErr]
  cases h₈ : Map.find? r a
  case none =>
    simp only [or_self, false_and, exists_const]
    simp [typeOf, h₃, typeOfGetAttr, getAttrInRecord] at h₂
    split at h₂ <;> simp [ok, err] at h₂
    case h_1 _ _ h₉ =>
      subst h₂
      have ⟨_, h₁₀⟩ := required_attribute_is_present h₅ h₉
      simp [h₈] at h₁₀
    case h_2 =>
      split at h₂ <;> simp at h₂
      subst h₂ ; rename_i h₁₀
      have ⟨_, h₁₁⟩ := capability_implies_record_attribute h₁ h₄ h₁₀
      simp [h₈] at h₁₁
  case some vₐ =>
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


theorem setLevel_preserves_type {v : Value} {ty : CedarType} {l : Level}
  (h : InstanceOfType v ty) :
  InstanceOfType v (setLevel l.sub1 ty) := by
  cases ty <;> cases v <;> cases h
  case _ =>
    simp [setLevel]
    apply InstanceOfType.instance_of_bool
    assumption
  case _ =>
    apply InstanceOfType.instance_of_int
  case _ =>
    apply InstanceOfType.instance_of_string
  case _ =>
    simp [setLevel]
    apply InstanceOfType.instance_of_entity
    assumption
  case _ =>
    simp [setLevel]
    rename_i ty s h₁
    apply InstanceOfType.instance_of_set
    intros v h₂
    apply setLevel_preserves_type
    apply h₁
    apply h₂
  case _ =>
    rename_i rty m h₁ h₂ h₃
    simp [setLevel]
      -- -- if an attribute is present in the record, then it is present in the type
      -- (h₁ : ∀ (k : Attr), r.contains k → rty.contains k)
      -- -- if an attribute is present, then it has the expected type
      -- (h₂ : ∀ (k : Attr) (v : Value) (qty : QualifiedType),
      --   r.find? k = some v → rty.find? k = some qty → InstanceOfType v qty.getType)
      -- -- required attributes are present
      -- (h₃ : ∀ (k : Attr) (qty : QualifiedType), rty.find? k = some qty → qty.isRequired → r.contains k) :
      -- InstanceOfType (.record r) (.record rty)
    apply InstanceOfType.instance_of_record
    case _ =>
      -- -- if an attribute is present in the record, then it is present in the type
      -- (h₁ : ∀ (k : Attr), r.contains k → rty.contains k)
      intros attr h₄
      apply Map.mapOnValuesAttach_preservesKeys_adapter
      apply h₁
      apply h₄
      exists (λ qual =>
        match _h : qual with
        | .required ty => .required (setLevel l.sub1 ty)
        | .optional ty => .optional (setLevel l.sub1 ty)
      )
    case _ =>
      -- -- if an attribute is present, then it has the expected type
      -- (h₂ : ∀ (k : Attr) (v : Value) (qty : QualifiedType),
      --   r.find? k = some v → rty.find? k = some qty → InstanceOfType v qty.getType)
      intros k v qty h₄ h₅
      sorry
    case _ =>
      sorry

  case _ =>
    simp [setLevel]
    apply InstanceOfType.instance_of_ext
    assumption
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals try omega
  case _ =>
    rename_i c _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [c]
    simp [sizeOf, CedarType._sizeOf_1]
    omega
  -- case _ =>
  --   rename_i c _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _ _
  --   rw [c]
  --   simp [sizeOf, CedarType._sizeOf_1, Map._sizeOf_1, List._sizeOf_1]

  --   omega


    -- sorry




theorem type_of_getAttr_is_sound_for_entities {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {ety : EntityType} {request : Request} {entities : Entities} {v₁ : Value} {l l₁ : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env (l == .infinite) = Except.ok (ty, ∅))
  (h₄ : typeOf x₁ c₁ env (l == .infinite) = Except.ok (CedarType.entity ety l₁, c₁'))
  (h₅ : evaluate x₁ request entities = Except.ok v₁)
  (h₆ : InstanceOfType v₁ (CedarType.entity ety l₁)) :
  ∃ v,
  (getAttr v₁ a entities = Except.error Error.entityDoesNotExist ∨
   getAttr v₁ a entities = Except.error Error.extensionError ∨
   getAttr v₁ a entities = Except.error Error.arithBoundsError ∨
   getAttr v₁ a entities = Except.ok v) ∧
   InstanceOfType v ty
:= by
  have ⟨uid, h₇, h₈⟩ := instance_of_entity_type_is_entity h₆
  subst h₈
  simp [getAttr, attrsOf, Entities.attrs, Map.findOrErr]
  cases h₈ : Map.find? entities uid
  case none =>
    simp only [Except.bind_err, Except.error.injEq, or_self, or_false, true_and]
    exact type_is_inhabited ty
  case some d =>
    subst h₇
    simp only [Except.bind_ok]
    cases h₉ : Map.find? d.attrs a
    case none =>
      simp
      simp [typeOf, typeOfGetAttr, *] at h₃
      split at h₃ <;> try contradiction
      split at h₃  <;> try simp [err] at h₃
      simp [getAttrInRecord] at *
      split at h₃
      case _ =>
        simp [Except.bind, setLevel, ok] at h₃
        rename_i h₁₀ _ _ h₁₁
        have h₁₂ := well_typed_entity_attributes h₂ h₈ h₁₀
        have ⟨v, h₁₃⟩ := required_attribute_is_present h₁₂ h₁₁
        simp [h₉] at h₁₃
      case _ =>
        split at h₃
        case _ =>
          simp [ok, Except.bind] at h₃
          rename_i hin
          have ⟨_, h₁₀⟩  := capability_implies_entity_attribute h₁ h₅ h₈ hin
          simp [h₉] at h₁₀
        case _ =>
          simp [err, Except.bind] at h₃
      case _ =>
        simp [err, Except.bind] at h₃
    case _ =>
      rename_i val
      simp only [Except.ok.injEq, false_or, exists_eq_left']
      simp [typeOf, h₄, typeOfGetAttr, getAttrInRecord] at h₃
      split at h₃ <;> simp [ok, err] at h₃
      split at h₃ <;> try simp [ok, err] at h₃
      split at h₃ <;> try simp [Except.bind] at h₃
      case _ =>
        rename_i heq _ _ _
        have h_entity := well_typed_entity_attributes h₂ h₈ heq
        rename_i attrTy heq₁
        have h_step : InstanceOfType val attrTy := by
          apply instance_of_attribute_type
          apply h_entity
          assumption
          simp [Qualified.getType]
          assumption
        rw [← h₃]
        apply setLevel_preserves_type h_step
      case _ =>
        split at h₃ <;> simp [Except.bind] at h₃
        rename_i heq₁ qual attrTy heq₂  hin
        have h_entity := well_typed_entity_attributes h₂ h₈ heq₁
        have h_step : InstanceOfType val attrTy := by
          apply instance_of_attribute_type
          apply h_entity
          assumption
          simp [Qualified.getType]
          assumption
        rw [← h₃]
        apply setLevel_preserves_type h_step


theorem type_of_getAttr_is_sound {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env (l == .infinite) = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.getAttr x₁ a) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.getAttr x₁ a) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₅, c₁', h₄⟩ := type_of_getAttr_inversion h₃
  subst h₅
  apply And.intro empty_guarded_capabilities_invariant
  rcases h₄ with ⟨ety, l', h₄⟩ | ⟨rty, h₄⟩  <;>
  have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ <;>
  try simp [EvaluatesTo] at h₆ <;>
  try simp [EvaluatesTo, evaluate] <;>
  try rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
  <;> try exact type_is_inhabited ty
  · exact type_of_getAttr_is_sound_for_entities h₁ h₂ h₃ h₄ h₆ h₇
  · exact type_of_getAttr_is_sound_for_records h₁ h₃ h₄ h₆ h₇


end Cedar.Thm
