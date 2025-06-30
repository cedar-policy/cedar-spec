import Cedar.Validation.RequestEntityValidator
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Validator

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem instance_of_bool_type_refl {b : Bool} {bty : BoolType} :
  instanceOfBoolType b bty = true → InstanceOfBoolType b bty
:= by
  simp only [instanceOfBoolType, InstanceOfBoolType]
  intro h₀
  cases h₁ : b <;> cases h₂ : bty <;> subst h₁ <;> subst h₂ <;> simp only [Bool.false_eq_true] at *

theorem instance_of_entity_type_refl {env : Environment} {e : EntityUID} {ety : EntityType} {eids: EntityType → Option (Set String)} :
  instanceOfEntityType e ety eids = true → InstanceOfEntityType env e ety
:= by
  simp only [InstanceOfEntityType, instanceOfEntityType]
  intro h₀
  have h₁ : (ety == e.ty) := by
    simp at h₀
    simp [h₀.left]
  simp only [beq_iff_eq] at h₁
  exact h₁

theorem instance_of_ext_type_refl {ext : Ext} {extty : ExtType} :
  instanceOfExtType ext extty = true → InstanceOfExtType ext extty
:= by
  simp only [InstanceOfExtType, instanceOfExtType]
  intro h₀
  cases h₁ : ext <;> cases h₂ : extty <;> subst h₁ <;> subst h₂ <;> simp only [Bool.false_eq_true] at *

theorem instance_of_type_refl {env : Environment} {v : Value} {ty : CedarType} {schema: EntitySchema} :
  instanceOfType v ty schema = true → InstanceOfType env v ty
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
      all_goals contradiction
    | int i =>
      cases ty
      case int => exact InstanceOfType.instance_of_int
      all_goals contradiction
    | string s =>
      cases ty
      case string => exact InstanceOfType.instance_of_string
      all_goals contradiction
    | entityUID uid =>
      cases ty
      case entity ety =>
        apply InstanceOfType.instance_of_entity uid ety
        apply instance_of_entity_type_refl
        assumption
      all_goals contradiction
  | set s =>
    cases ty
    case set sty =>
      apply InstanceOfType.instance_of_set s sty
      simp only [List.all_eq_true] at h₀
      intro v hv
      simp only [← Set.in_list_iff_in_set] at hv
      specialize h₀ ⟨v, hv⟩
      simp only [List.attach_def, List.mem_pmap_subtype, hv, true_implies] at h₀
      exact instance_of_type_refl h₀
    all_goals contradiction
  | record r =>
    cases ty
    case record rty =>
      apply InstanceOfType.instance_of_record r rty
      all_goals simp only [Bool.and_eq_true, List.all_eq_true] at h₀
      intro k h₁
      simp only [Map.contains_iff_some_find?] at h₁
      have ⟨⟨h₂, _⟩, _⟩ := h₀
      replace ⟨v, h₁⟩ := h₁
      specialize h₂ (k, v)
      simp only at h₂
      apply h₂ (Map.find?_mem_toList h₁)
      intro k v qty h₁ h₂
      have ⟨⟨_, h₄⟩, _⟩ := h₀
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
        simp only [h₈] at h₇
        simp only [h₈, Option.some.injEq] at h₂
        subst h₂
        exact instance_of_type_refl h₇
      intro k qty h₁ h₂
      have ⟨⟨_, h₄⟩, h₅⟩ := h₀ ; clear h₀
      simp only [List.attach₂] at h₄
      simp only [requiredAttributePresent, Bool.if_true_right, Bool.decide_eq_true] at h₅
      specialize h₅ (k, qty)
      simp only [h₁, Bool.or_eq_true, Bool.not_eq_true'] at h₅
      have h₆ := Map.find?_mem_toList h₁
      simp only [Map.toList] at h₆
      cases h₅ h₆ with
      | inl h₅ =>
        rw [h₂] at h₅
        contradiction
      | inr h₅ => exact h₅
    all_goals contradiction
  | ext e =>
    cases ty
    case ext ety =>
      apply InstanceOfType.instance_of_ext
      apply instance_of_ext_type_refl
      assumption
    all_goals contradiction
termination_by v
decreasing_by
  all_goals
    simp_wf
    simp only [Bool.and_eq_true, List.all_eq_true] at h₀
  case _ v' _ _ _ _ h₁ _ _ _ =>
    subst h₁
    simp only [Value.set.sizeOf_spec]
    have := Set.sizeOf_lt_of_mem hv
    omega
  case _ h₉ _ _ _ _ _ _ =>
    subst h₉
    have h₁ := Map.find?_mem_toList h₁
    simp only [Map.toList, Map.kvs] at h₁
    simp only [Value.record.sizeOf_spec, gt_iff_lt]
    have := Map.sizeOf_lt_of_value h₁
    omega

theorem instance_of_request_type_refl {env : Environment} {request : Request} {reqty : RequestType} {schema: EntitySchema}:
  instanceOfRequestType request reqty schema = true → InstanceOfRequestType env request reqty
:= by
  intro h₀
  simp only [InstanceOfRequestType]
  simp only [instanceOfRequestType, Bool.and_eq_true, beq_iff_eq] at h₀
  have ⟨⟨⟨h₁,h₂⟩,h₃⟩, h₄⟩ := h₀
  and_intros
  · exact instance_of_entity_type_refl h₁
  · exact h₂
  · exact instance_of_entity_type_refl h₃
  · exact instance_of_type_refl h₄

theorem instance_of_entity_schema_refl {env : Environment} {entities : Entities} :
  instanceOfEntitySchema env entities = .ok () → InstanceOfEntitySchema env entities
:= by
  intro h₀
  simp only [InstanceOfEntitySchema]
  simp only [instanceOfEntitySchema] at h₀
  generalize h₁ : (λ x : EntityUID × EntityData => instanceOfEntitySchema.instanceOfEntityData env x.fst x.snd) = f
  rw [h₁] at h₀
  intro uid data h₂
  have h₀ := List.forM_ok_implies_all_ok (Map.toList entities) f h₀ (uid, data)
  replace h₀ := h₀ (Map.find?_mem_toList h₂)
  rw [← h₁] at h₀
  simp only [instanceOfEntitySchema.instanceOfEntityData] at h₀
  cases h₂ : Map.find? env.ets uid.ty <;> simp [h₂] at h₀
  case some entry =>
    exists entry
    simp only [true_and]
    split at h₀ <;> try simp only [reduceCtorEq] at h₀
    rename_i hv
    constructor
    simp only [EntitySchemaEntry.isValidEntityEID] at hv
    simp only [IsValidEntityEID]
    split at hv
    · simp
    · simp
      rw [Set.contains_prop_bool_equiv] at hv
      exact hv
    split at h₀ <;> try simp only [reduceCtorEq] at h₀
    constructor <;> rename_i h₃
    · exact instance_of_type_refl h₃
    · split at h₀ <;> try simp only [reduceCtorEq] at h₀
      rename_i h₄
      simp only [Set.all, List.all_eq_true] at h₄
      constructor
      · intro anc ancin
        simp only [Set.contains, List.elem_eq_mem, decide_eq_true_eq] at h₄
        rw [← Set.in_list_iff_in_set] at ancin
        replace h₄ := h₄ anc ancin
        simp at h₄
        exact h₄.left
      · split at h₀ <;> try simp only [reduceCtorEq] at h₀
        unfold InstanceOfEntityTags
        rename_i h₅
        simp only [instanceOfEntitySchema.instanceOfEntityTags] at h₅
        split at h₅ <;> rename_i heq <;> simp only [heq]
        · intro v hv
          simp only [List.all_eq_true] at h₅
          exact instance_of_type_refl (h₅ v hv)
        · simp only [beq_iff_eq] at h₅
          exact h₅

theorem instance_of_action_schema_refl {entities : Entities} {acts : ActionSchema} :
  instanceOfActionSchema entities acts = .ok () → InstanceOfActionSchema entities acts
:= by
  intro h₀
  simp only [InstanceOfActionSchema]
  simp only [instanceOfActionSchema] at h₀
  generalize h₁ : (fun x : EntityUID × ActionSchemaEntry => instanceOfActionSchema.instanceOfActionSchemaData entities x.fst x.snd) = f
  rw [h₁] at h₀
  intro uid entry h₂
  replace h₀ := List.forM_ok_implies_all_ok (Map.toList acts) f h₀ (uid, entry)
  replace h₀ := h₀ (Map.find?_mem_toList h₂)
  rw [← h₁] at h₀
  simp only [instanceOfActionSchema.instanceOfActionSchemaData, beq_iff_eq] at h₀
  cases h₂ : Map.find? entities uid <;> simp [h₂] at h₀
  case some data =>
    exists data
    apply And.intro rfl
    simp only [h₀]


theorem request_and_entities_match_env {env : Environment} {request : Request} {entities : Entities} :
  requestMatchesEnvironment env request →
  entitiesMatchEnvironment env entities = .ok () →
  RequestAndEntitiesMatchEnvironment env request entities
:= by
  intro h₀ h₁
  simp only [RequestAndEntitiesMatchEnvironment]
  simp only [requestMatchesEnvironment] at h₀
  simp only [entitiesMatchEnvironment] at h₁
  constructor
  exact instance_of_request_type_refl h₀
  cases h₂ : instanceOfEntitySchema env entities <;> simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h₁
  exact And.intro (instance_of_entity_schema_refl h₂) (instance_of_action_schema_refl h₁)

theorem request_and_entities_validate_implies_match_schema (schema : Schema) (request : Request) (entities : Entities) :
  validateRequest schema request = .ok () →
  validateEntities schema entities = .ok () →
  RequestAndEntitiesMatchSchema schema request entities
:= by
  intro h₀ h₁
  simp only [RequestAndEntitiesMatchSchema]
  simp only [validateRequest, List.any_eq_true, ite_eq_left_iff, not_exists, not_and,
    Bool.not_eq_true, reduceCtorEq, imp_false, Classical.not_forall, not_imp,
    Bool.not_eq_false] at h₀
  simp only [validateEntities] at h₁
  replace ⟨env, ⟨h₀, h₂⟩⟩ := h₀
  exists env
  apply And.intro h₀
  apply request_and_entities_match_env h₂
  simp only [List.forM_ok_implies_all_ok schema.environments (entitiesMatchEnvironment · entities) h₁ env h₀]
