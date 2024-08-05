import Cedar.Validation.RequestEntityValidator
import Cedar.Thm.Validation.Typechecker.Types

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem instance_of_bool_type_refl (b : Bool) (bty : BoolType) :
  instanceOfBoolType b bty = true → InstanceOfBoolType b bty
:= by
  simp only [InstanceOfBoolType, instanceOfBoolType]
  intro h₀
  cases h₁ : b <;> cases h₂ : bty <;> subst h₁ <;> subst h₂ <;> simp only at *

theorem instance_of_entity_type_refl (e : EntityUID) (ety : EntityType) :
  instanceOfEntityType e ety = true → InstanceOfEntityType e ety
:= by
  simp only [InstanceOfEntityType, instanceOfEntityType]
  intro h₀
  simp at h₀
  assumption

theorem instance_of_ext_type_refl (ext : Ext) (extty : ExtType) :
  instanceOfExtType ext extty = true → InstanceOfExtType ext extty
:= by
  simp only [InstanceOfExtType, instanceOfExtType]
  intro h₀
  cases h₁ : ext <;> cases h₂ : extty <;> subst h₁ <;> subst h₂ <;> simp only at *

theorem instance_of_type_refl (v : Value) (ty : CedarType) :
  instanceOfType v ty = true → InstanceOfType v ty
:= by
  intro h₀
  unfold instanceOfType at h₀
  cases v with
  | prim p =>
    cases p with
    | bool b =>
      cases ty
      case bool bty =>
        apply InstanceOfType.instance_of_bool b bty
        apply instance_of_bool_type_refl
        assumption
      all_goals
        contradiction
    | int i =>
      cases ty
      case int =>
        apply InstanceOfType.instance_of_int
      all_goals
        contradiction
    | string s =>
      cases ty
      case string =>
        apply InstanceOfType.instance_of_string
      all_goals
        contradiction
    | entityUID uid =>
      cases ty
      case entity ety =>
        apply InstanceOfType.instance_of_entity uid ety
        apply instance_of_entity_type_refl
        assumption
      all_goals
        contradiction
  | set s =>
    cases ty
    case set sty =>
      apply InstanceOfType.instance_of_set s sty
      simp at h₀
      intro v hv
      simp only [← Set.in_list_iff_in_set] at hv
      specialize h₀ ⟨v, hv⟩
      simp only [List.attach_def, List.mem_pmap_subtype, hv, true_implies] at h₀
      exact instance_of_type_refl v sty h₀
    all_goals
      contradiction
    all_goals
      contradiction
  | record r =>
    cases ty
    case record rty =>
      apply InstanceOfType.instance_of_record r rty
      all_goals
        simp at h₀
      intro k h₁
      simp only [Map.contains_iff_some_find?] at h₁
      have ⟨⟨h₂, h₃⟩, h₄⟩ := h₀
      obtain ⟨v, h₁⟩ := h₁
      specialize h₂ (k, v)
      simp only at h₂
      apply h₂
      exact Map.find?_mem_toList h₁
      intro k v qty h₁ h₂
      have ⟨⟨h₃, h₄⟩, h₅⟩ := h₀
      have h₆ : sizeOf (k,v).snd < 1 + sizeOf r.kvs
      := by
        have hin := Map.find?_mem_toList h₁
        simp only
        replace hin := List.sizeOf_lt_of_mem hin
        simp only [Prod.mk.sizeOf_spec] at hin
        sorry
      specialize h₄ ⟨(k, v), h₆⟩
      simp only [List.attach₂, List.mem_pmap_subtype] at h₄
      have h₇ := h₄ (Map.find?_mem_toList h₁)
      cases h₈ : rty.find? k with
      | none =>
        rw [h₂] at h₈
        contradiction
      | some vl =>
        simp [h₈] at h₇
        simp [h₈] at h₂
        subst h₂
        exact instance_of_type_refl v vl.getType h₇
      intro k qty h₁ h₂
      have ⟨⟨h₃, h₄⟩, h₅⟩ := h₀
      sorry
    all_goals
      contradiction
  | ext e =>
    cases ty
    case ext ety =>
      apply InstanceOfType.instance_of_ext
      apply instance_of_ext_type_refl
      assumption
    all_goals
      contradiction

theorem instance_of_request_type_refl (request : Request) (reqty : RequestType) :
  instanceOfRequestType request reqty = true → InstanceOfRequestType request reqty
:= by
  intro h₀
  simp [InstanceOfRequestType]
  simp [instanceOfRequestType] at h₀
  obtain ⟨⟨⟨h₁,h₂⟩,h₃⟩, h₄⟩ := h₀
  constructor
  case left =>
    apply instance_of_entity_type_refl
    exact h₁
  case right =>
    constructor
    case left =>
      exact h₂
    case right =>
      constructor
      case left =>
        apply instance_of_entity_type_refl
        exact h₃
      case right =>
        apply instance_of_type_refl
        exact h₄

theorem instance_of_entity_schema_refl (entities : Entities) (ets : EntitySchema) :
  instanceOfEntitySchema entities ets = .ok () → InstanceOfEntitySchema entities ets
:= by
  intro h₀
  simp [InstanceOfEntitySchema]
  simp [instanceOfEntitySchema] at h₀
  intro uid data h₁

  sorry

theorem instance_of_action_schema_refl (entities : Entities) (acts : ActionSchema) :
  instanceOfActionSchema entities acts = .ok () → InstanceOfActionSchema entities acts
:= by
  intro h₀
  simp [InstanceOfActionSchema]
  simp [instanceOfActionSchema] at h₀
  intro uid entry h₁
  sorry
