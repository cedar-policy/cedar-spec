import Cedar.Validation.RequestEntityValidator
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Validator

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
        simp only [Prod.mk.sizeOf_spec, Map.toList] at hin
        omega
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
      clear h₀
      simp only [List.attach₂] at h₄
      simp [requiredAttributePresent] at h₅
      specialize h₅ (k, qty)
      simp [h₁] at h₅
      have h₆ := Map.find?_mem_toList h₁
      simp [Map.toList] at h₆
      have h₅ := h₅ h₆
      cases h₅ with
      | inl h₅ =>
        rw [h₂] at h₅
        contradiction
      | inr h₅ => exact h₅
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
termination_by v
decreasing_by
  all_goals simp_wf
  sorry
  sorry


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
  generalize h₁ : (fun x : EntityUID × EntityData => instanceOfEntitySchema.instanceOfEntityData ets x.fst x.snd) = f
  rw [h₁] at h₀
  intro uid data h₂
  have h₀ := List.forM_ok_implies_all_ok (Map.toList entities) f h₀
  specialize h₀ (uid, data)
  have h₀ := h₀ (Map.find?_mem_toList h₂)
  rw [← h₁] at h₀
  simp [instanceOfEntitySchema.instanceOfEntityData] at h₀
  cases h₂ : Map.find? ets uid.ty <;> simp [h₂] at h₀
  case some entry =>
    exists entry
    constructor
    rfl
    cases h₃ : instanceOfType (Value.record data.attrs) (CedarType.record entry.attrs) <;> simp [h₃] at h₀
    simp [Set.all] at h₀
    constructor
    exact instance_of_type_refl (Value.record data.attrs) (CedarType.record entry.attrs) h₃
    intro anc ancin
    simp [Set.contains] at h₀
    simp [Membership.mem] at *
    apply h₀
    exact ancin

theorem instance_of_action_schema_refl (entities : Entities) (acts : ActionSchema) :
  instanceOfActionSchema entities acts = .ok () → InstanceOfActionSchema entities acts
:= by
  intro h₀
  simp [InstanceOfActionSchema]
  simp [instanceOfActionSchema] at h₀
  generalize h₁ : (fun x : EntityUID × ActionSchemaEntry => instanceOfActionSchema.instanceOfActionSchemaData entities x.fst x.snd) = f
  rw [h₁] at h₀
  intro uid entry h₂
  have h₀ := List.forM_ok_implies_all_ok (Map.toList acts) f h₀
  specialize h₀ (uid, entry)
  have h₀ := h₀ (Map.find?_mem_toList h₂)
  rw [← h₁] at h₀
  simp [instanceOfActionSchema.instanceOfActionSchemaData] at h₀
  cases h₂ : Map.find? entities uid <;> simp [h₂] at h₀
  case some data =>
    exists data
    constructor
    rfl
    simp [h₀]


theorem request_and_entities_match_env (env : Environment) (request : Request) (entities : Entities) :
  requestMatchesEnvironment env request ∧ entitiesMatchEnvironment env entities = .ok () → RequestAndEntitiesMatchEnvironment env request entities
:= by
  intro ⟨h₀, h₁⟩
  simp [RequestAndEntitiesMatchEnvironment]
  simp [requestMatchesEnvironment] at h₀
  simp [entitiesMatchEnvironment] at h₁
  constructor
  exact instance_of_request_type_refl request env.reqty h₀
  cases h₂ : instanceOfEntitySchema entities env.ets <;> simp [h₂] at h₁
  constructor
  exact instance_of_entity_schema_refl entities env.ets h₂
  exact instance_of_action_schema_refl entities env.acts h₁

theorem request_and_entities_validate_implies_match_schema (schema : Schema) (request : Request) (entities : Entities) :
  validateRequest schema request = .ok () ∧ validateEntities schema entities = .ok () → RequestAndEntitiesMatchSchema schema request entities
:= by
  sorry
