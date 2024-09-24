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

theorem type_of_getAttr_inversion {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {l₁ : Level}
  (h₁ : typeOf (Expr.getAttr x₁ a) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ c₁',
    (∃ ety l₂, typeOf x₁ c₁ env (l₁ == .infinite) = Except.ok (.entity ety l₂, c₁')) ∨
    (∃ rty, typeOf x₁ c₁ env (l₁ == .infinite) = Except.ok (.record rty, c₁'))
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env (l₁ == .infinite) <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfGetAttr] at h₁
    split at h₁
    case _ ty' rty' => -- Records
      simp
      apply getAttrInRecord_has_empty_capabilities
      assumption
    case _ ty' rty' l' => -- Entities
      split at h₁ <;> try simp [err] at h₁
      rename_i hlevel
      split at h₁ <;> try simp [err] at h₁
      rename_i otp rty'' _
      simp [bind, Except.bind] at h₁
      split at h₁ <;> try simp [err] at h₁
      simp
      rename_i heq
      have ⟨h₁₁, h₁₂⟩ := h₁
      subst h₁₂
      rename_i monad v
      have ⟨result_ty, result_caps⟩ := v
      simp
      apply getAttrInRecord_has_empty_capabilities
      apply heq
    case _ =>
      simp [err] at h₁

theorem type_of_getAttr_inversion_levels {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {l₁ : Level}
  (h₁ : typeOf (Expr.getAttr x₁ a) c₁ env (l₁ == .infinite)= Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ c₁',
    (∃ ety l₂, typeOf x₁ c₁ env (l₁ == .infinite)= Except.ok (.entity ety l₂, c₁') ∧ l₂ > .finite 0) ∨
    (∃ rty, typeOf x₁ c₁ env (l₁ == .infinite) = Except.ok (.record rty, c₁'))
  := by
  have hinv := type_of_getAttr_inversion h₁
  replace ⟨hinv₁, c₁', hinv⟩ := hinv
  constructor <;> try assumption
  exists c₁'
  cases hinv
  case _ hinv =>
    apply Or.inl
    replace ⟨ety, l₂, hinv⟩ := hinv
    exists ety
    exists l₂
    constructor <;> try assumption
    simp [typeOf, hinv, typeOfGetAttr] at h₁
    split at h₁
    case _ hzero =>
      simp
      assumption
    case _ =>
      simp [err] at h₁
  case _ hinv =>
    replace ⟨rty, hinv⟩ := hinv
    apply Or.inr
    exists rty

theorem type_of_getAttr_is_sound_for_records {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {rty : RecordType} {request : Request} {entities : Entities} {v₁ : Value} {l₁ : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : typeOf (Expr.getAttr x₁ a) c₁ env (l₁ == .infinite) = Except.ok (ty, ∅))
  (h₃ : typeOf x₁ c₁ env (l₁ == .infinite) = Except.ok (CedarType.record rty, c₁'))
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
    simp [setLevel]
    apply InstanceOfType.instance_of_int
  case _ =>
    simp [setLevel]
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
    apply InstanceOfType.instance_of_record
    case _ =>
      intros attr h₄
      apply Map.mapOnValuesAttach_preservesKeys_adapter
      apply h₁
      apply h₄
      exists (Functor.map (setLevel l.sub1))
      simp [Functor.map]
      funext
      split <;> rename_i heq <;> rw [heq]
    case _ =>
      intros k v qty h₄ h₅
      have h₆ : rty.contains k = true := by
        apply h₁
        rw [Map.contains_iff_some_find?]
        exists v
      have h₇ : ∃ qty_orig, rty.find? k = .some qty_orig := by
        rw [← Map.contains_iff_some_find?]
        assumption
      replace ⟨qty_orig, h₇⟩ := h₇
      have h₈ : some qty = some (setLevel l.sub1 <$> qty_orig)
        := by
        rw [← h₅]
        rw [@Map.mapOnValues_maps_adapter Attr QualifiedType _ _ _ _ _ _ rty _ (Functor.map (setLevel l.sub1)) k qty_orig]
        apply h₇
        simp [Functor.map]
        funext
        split <;> rename_i heq <;> rw [heq]
      simp at h₈
      have htype : InstanceOfType v (Qualified.getType qty_orig) := by
        apply h₂
        repeat assumption
      rw [h₈]
      simp [Functor.map]
      split
        <;> simp [Qualified.getType]
        <;> apply setLevel_preserves_type
        <;> simp [Qualified.getType] at htype
        <;> assumption
    case _ =>
      intros k qty h₄ h₅
      have h₆ : (rty.mapOnValuesAttach (λ prod => setLevel l.sub1 <$> prod.val)).contains k = true
        := by
        rw [Map.contains_iff_some_find?]
        exists qty
        simp [Functor.map]
        rw [← h₄]
        rw [Map.mapOnValuesAttachFunEq]
        funext
        split <;> rename_i heq <;> rw [heq]
      have h₇ : rty.contains k = true := by
        rw [Map.mapOnValuesAttach_preservesContains_adapter]
        apply h₆
        exists (Functor.map (setLevel l.sub1))
        funext
      rw [Map.contains_iff_some_find?] at h₇
      replace ⟨qty_orig, h₇⟩ := h₇
      apply h₃
      assumption
      have heq : qty = setLevel l.sub1 <$> qty_orig := by
        rw [@Map.mapOnValues_maps_adapter _ _ _ _ _ _ _ _ _ _ (Functor.map (setLevel l.sub1)) k qty_orig] at h₄
        simp at h₄
        rw [← h₄]
        assumption
        funext
        simp [Functor.map]
        split <;> rename_i heq <;> rw [heq]
      cases qty_orig
      case _ =>
        simp [heq, Functor.map, Qualified.isRequired] at h₅
      case _ =>
        simp [Qualified.isRequired]
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
  case _ =>
    rename_i ty' h_orig
    have hsize₁ : sizeOf ty' < sizeOf qty_orig := by
      rw [h_orig]
      simp
      omega
    rename_i rty heq_ty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [heq_ty]
    simp
    rw [← h_orig] at h₇

    have hsize₂ : sizeOf qty_orig < sizeOf rty := by
      have h : (k, qty_orig) ∈ rty.kvs := by
        apply Map.find_means_mem
        assumption

      have h₂ : sizeOf (k, qty_orig) < sizeOf rty.kvs := by
        apply List.sizeOf_lt_of_mem
        assumption

      have h₃ : sizeOf rty.kvs < sizeOf rty := by
        apply Map.sizeOf_lt_of_kvs

      have h₄ : sizeOf qty_orig < sizeOf (k, qty_orig) := by
        simp
        omega

      omega


    omega
  case _ =>
    rename_i h₁₀ h₁₁ hinst₁ type hinst₂
    rename_i heq₁ _ _ _ _ rty _ _ _ _ _ _ _ _ _ heq₂ _ _ _ _ _
    rw [heq₂] at h₁₀
    rw [heq₁]
    rw [heq₂]
    rw [heq₂] at h₇
    have hsize₁ : sizeOf type < sizeOf (Qualified.required type) := by
      simp
      omega
    have hsize₂ : sizeOf (Qualified.required type) < sizeOf rty := by
      have hmem : (k, (Qualified.required type)) ∈ rty.kvs := by
        apply Map.find_means_mem
        assumption
      have h₁ : sizeOf (Qualified.required type) <  sizeOf (k, Qualified.required type) := by
        simp
        omega
      have h₂ : sizeOf (k, Qualified.required type) < sizeOf rty.kvs := by
        apply List.sizeOf_lt_of_mem
        assumption
      have h₃ : sizeOf rty.kvs < sizeOf rty := by
        apply Map.sizeOf_lt_of_kvs
      omega
    simp
    omega
theorem type_of_getAttr_is_sound_for_entities {x₁ : Expr} {a : Attr} {c₁ c₁' : Capabilities} {env : Environment} {ety : EntityType} {request : Request} {entities : Entities} {v₁ : Value} {l₁ l₂ : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env (l₁ == .infinite) = Except.ok (ty, ∅))
  (h₄ : typeOf x₁ c₁ env (l₁ == .infinite) = Except.ok (CedarType.entity ety l₂, c₁'))
  (h₅ : evaluate x₁ request entities = Except.ok v₁)
  (h₆ : InstanceOfType v₁ (CedarType.entity ety l₂)) :
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
      simp only [Except.error.injEq, or_self, false_and, exists_const]
      simp only [typeOf, h₄, typeOfGetAttr, getAttrInRecord, List.empty_eq, Except.bind_ok] at h₃
      split at h₃ <;> simp [ok, err] at h₃
      split at h₃ <;> try simp at h₃
      split at h₃ <;> try simp at h₃
      case h_1.h_1 _ _ h₁₀ _ _ h₁₁ =>
        subst h₃
        have h₁₂ := well_typed_entity_attributes h₂ h₈ h₁₀
        have ⟨aᵥ, h₁₃⟩ := required_attribute_is_present h₁₂ h₁₁
        simp [h₉] at h₁₃
      case h_1.h_2 =>
        split at h₃ <;> simp at h₃
        subst h₃ ; rename_i h₁₃
        have ⟨_, h₁₄⟩ := capability_implies_entity_attribute h₁ h₅ h₈ h₁₃
        simp [h₉] at h₁₄
    case some vₐ =>
      simp only [Except.ok.injEq, false_or, exists_eq_left']
      simp [typeOf, h₄, typeOfGetAttr, getAttrInRecord] at h₃
      split at h₃ <;> simp [ok, err] at h₃
      split at h₃ <;> try simp at h₃
      split at h₃ <;> try simp at h₃
      case h_1.h_1 _ _ h₁₀ _ _ h₁₁ =>
        subst h₃
        apply setLevel_preserves_type
        apply instance_of_attribute_type _ h₁₁ (by simp [Qualified.getType]) h₉
        apply well_typed_entity_attributes h₂ h₈ h₁₀
      case h_1.h_2 _ _ h₁₀ _ _ h₁₁ =>
        split at h₃ <;> simp at h₃
        subst h₃
        apply setLevel_preserves_type
        apply instance_of_attribute_type _ h₁₁ (by simp [Qualified.getType]) h₉
        apply well_typed_entity_attributes h₂ h₈ h₁₀

theorem type_of_getAttr_is_sound {x₁ : Expr} {a : Attr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l₁ : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.getAttr x₁ a) c₁ env (l₁ == .infinite) = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.getAttr x₁ a) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.getAttr x₁ a) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₅, c₁', h₄⟩ := type_of_getAttr_inversion h₃
  subst h₅
  apply And.intro empty_guarded_capabilities_invariant
  rcases h₄ with ⟨ety, l₂, h₄⟩ | ⟨rty, h₄⟩ <;>
  have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ <;>
  simp [EvaluatesTo] at h₆ <;>
  simp [EvaluatesTo, evaluate] <;>
  rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
  <;> try exact type_is_inhabited ty
  · exact type_of_getAttr_is_sound_for_entities h₁ h₂ h₃ h₄ h₆ h₇
  · exact type_of_getAttr_is_sound_for_records h₁ h₃ h₄ h₆ h₇


end Cedar.Thm
