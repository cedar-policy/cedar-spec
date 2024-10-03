
import Cedar.Data.Map
import Cedar.Spec.EntitySlice
import Cedar.Spec.Value
import Cedar.Thm.Entities
import Cedar.Thm.Data.Map
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Validation.Types
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Levels
import Cedar.Thm.SubExpression

namespace Cedar.Thm
open Cedar.Data
open Cedar.Validation
open Cedar.Spec

theorem append_membership {α : Type} (l₁ : List α) (l₂ : List α) (a : α) :
  a ∈ (l₁ ++ l₂) →
  a ∈ l₁ ∨ a ∈ l₂
  := by
  intros in_append
  cases l₁
  case nil =>
    simp [List.append] at in_append
    simp [in_append]
  case cons head tail =>
    cases in_append
    case head =>
      simp
    case tail in_tail =>
      have step : a ∈ tail ∨ a ∈ l₂ := by
        apply append_membership
        apply in_tail
      rcases step with step | step
        <;> simp [step]

theorem in_joins_in_member {α : Type} (l : List (List α)) (a : α)
  (in_lists : a ∈ l.join) :
  ∃ l',
    l' ∈ l ∧ a ∈ l'
  := by
  cases l
  case nil =>
    simp [List.join] at in_lists
  case cons head tail =>
    rw [List.join_cons] at in_lists
    have step : a ∈ head ∨ a ∈ tail.join := by
      apply append_membership
      assumption
    rcases step with step | step
    case _ =>
      exists head
      constructor
      · simp
      · apply step
    case _ =>
      have step₂ : ∃ l', l' ∈ tail ∧ a ∈ l' := by
        apply in_joins_in_member
        assumption
      replace ⟨l', step₂⟩ := step₂
      exists l'
      constructor <;> try simp
      repeat simp [step₂]

theorem in_joins_in_member' {α : Type} (head_list : List α) (tail_list : List (List α)) (a : α)
  (in_lists : a ∈ (head_list :: tail_list).join) :
  ∃ target_list,
    a ∈ target_list ∧
    (
      target_list = head_list ∨ target_list ∈ tail_list
    )
  := by
  have h := in_joins_in_member (head_list :: tail_list) a in_lists
  replace ⟨target, h₁, h₂⟩ := h
  clear h
  exists target
  simp [h₂]
  cases h₁
  case head =>
    simp
  case tail in_tail =>
    apply Or.inr
    apply in_tail

def in_list_in_join {α : Type} (list : List α) (lists : List (List α)) (a : α)
  (in_list : a ∈ list)
  (in_lists : list ∈ lists) :
  a ∈ lists.join
  := by
  exact List.mem_join_of_mem in_lists in_list

def join_cons {α : Type} (list : List α) (lists : List (List α)) (a : α) :
  a ∈ lists.join →
  a ∈ (list :: lists).join
  := by
  intros h
  simp [List.join]
  apply Or.inr
  simp at h
  apply h


def SimpleSliceContxtSoundness (v : Value) : Prop :=
  ∀ euid edata (entities slice : Entities) (list : List (EntityUID × EntityData)),
    v.findEuids entities = some list →
    slice.find? euid = some edata →
    (euid, edata) ∈ list →
    slice.find? euid = entities.find? euid

theorem simpleSlice_set (members : List Value) (euid : EntityUID) (edata : EntityData) (entities slice : Entities) (list : List (List (EntityUID × EntityData)))
  (h : members.mapM (λ value => value.findEuids entities) = some list)
  (in_slice : slice.find? euid = some edata)
  (in_list : (euid, edata) ∈ list.join)
  (ih : ∀ v, v ∈ members → SimpleSliceContxtSoundness v) :
  slice.find? euid = entities.find? euid
  := by
  cases members
  case nil =>
    simp [List.mapM, List.mapM.loop] at h
    subst h
    simp [List.join] at in_list
  case cons head tail =>
    rw [List.mapM_cons] at h
    cases find_in_head : head.findEuids entities
    <;> simp [find_in_head] at h
    cases find_in_tail : tail.mapM (λ value => value.findEuids entities)
    <;> simp [find_in_tail] at h
    rename_i head_list tail_list
    have step : ∃ target_list,
      (euid, edata) ∈ target_list ∧
      (
        target_list = head_list ∨ target_list ∈ tail_list
      ) := by
      apply in_joins_in_member'
      rw [← h] at in_list
      apply in_list
    replace ⟨target_list, step₁, step₂⟩ := step
    clear step
    subst h
    cases step₂
    case _ step₂ =>
      subst step₂
      apply ih
      simp
      apply Or.inl
      rfl
      apply find_in_head
      apply in_slice
      apply step₁
    case _ step₂ =>
      apply simpleSlice_set
      apply find_in_tail
      apply in_slice
      apply in_list_in_join
      apply step₁
      apply step₂
      intros v in_tail
      apply ih
      simp [in_tail]


theorem simpleSlice_context_record (kvs : Map Attr  Value) (euid : EntityUID) (edata : EntityData) (entities slice : Entities)
  (h : (Value.record kvs).findEuids entities = some list)
  (in_slice : slice.find? euid = some edata)
  (in_list : (euid, edata) ∈ list)
  (ih : ∀ v, v ∈ kvs.values → SimpleSliceContxtSoundness v) :
  slice.find? euid = entities.find? euid
  := by
  simp [Value.findEuids, List.mapM₁, List.attach, List.attachWith] at h
  simp [List.mapM_pmap_subtype (λ (value : Value) => value.findEuids entities)] at h
  cases mapping : kvs.values.mapM (λ value => value.findEuids entities)
  <;> simp [mapping] at h
  rename_i llist
  apply simpleSlice_set kvs.values
  apply mapping
  apply in_slice
  rw [h]
  apply in_list
  apply ih

theorem simpleSlice_context_value (v : Value) (euid : EntityUID) (edata : EntityData) (entities slice : Entities) (context_entities : List (EntityUID × EntityData))
  (context_entities_def : v.findEuids entities = some context_entities)
  (in_slice : slice.find? euid = some edata)
  (in_context_entities : (euid, edata) ∈ context_entities) :
  slice.find? euid = entities.find? euid
  := by
  cases v
  case prim p =>
    cases p
    case bool b =>
      exfalso
      simp [Value.findEuids, Prim.findEuids] at context_entities_def
      subst context_entities_def
      simp at in_context_entities
    case int i =>
      exfalso
      simp [Value.findEuids, Prim.findEuids] at context_entities_def
      subst context_entities_def
      simp at in_context_entities
    case string s =>
      exfalso
      simp [Value.findEuids, Prim.findEuids] at context_entities_def
      subst context_entities_def
      simp at in_context_entities
    case entityUID euid' =>
      simp [Value.findEuids, Prim.findEuids] at context_entities_def
      cases find : entities.find? euid'
        <;> simp [find] at context_entities_def
      subst context_entities_def
      cases in_context_entities
      case tail h =>
        cases h
      case head =>
        simp [find, in_slice]
  case set members =>
    simp [Value.findEuids] at context_entities_def
    simp [List.mapM₁, List.attach, List.attachWith] at context_entities_def
    simp [List.mapM_pmap_subtype (λ (value : Value) => value.findEuids entities )] at context_entities_def
    cases mapping : members.toList.mapM (λ value => value.findEuids entities)
    <;> simp [mapping] at context_entities_def
    rename_i list_of_lists
    apply simpleSlice_set
    apply mapping
    apply in_slice
    rw [← context_entities_def] at in_context_entities
    apply in_context_entities
    intros v in_values
    apply simpleSlice_context_value
  case record =>
    apply simpleSlice_context_record
    repeat assumption
    rename_i kvs
    intros v in_map
    apply simpleSlice_context_value
  case ext =>
    simp [Value.findEuids] at context_entities_def
    subst context_entities_def
    simp at in_context_entities
termination_by (sizeOf v)
decreasing_by
  all_goals simp_wf
  all_goals try omega
  case _ =>
    rename Value => v'
    rename Set Value => set
    rename v = Value.set set => eq
    rw [eq]
    have step₁ : sizeOf v' < sizeOf set := by
      apply Set.sizeOf_lt_of_mem
      exact in_values
    simp
    omega
  case _ =>
    rename Value => v'
    rename Map Attr Value => map
    rename v = Value.record map => eq
    rw [eq]
    have step : sizeOf v' < sizeOf map := by
      exact Map.sizeOf_lt_of_in_values in_map
    simp
    omega



theorem simpleSlice_context (req : Request) (euid : EntityUID) (edata : EntityData) (entities slice : Entities) (context_entities : List (EntityUID × EntityData))
  (context_entities_def : loadEuids req.context entities = some context_entities)
  (in_slice : slice.find? euid = some edata)
  (in_context_entiites : (euid, edata) ∈ context_entities) :
  slice.find? euid = entities.find? euid
  := by
  simp [loadEuids] at context_entities_def
  apply simpleSlice_context_value
  apply context_entities_def
  apply in_slice
  apply in_context_entiites



theorem simpleSlice_is_subslice (req : Request) (entities slice : Entities)
  (slice_def : simpleSlice req entities = some slice) :
  subslice slice entities
  := by
  simp [subslice]
  intros euid edata in_slice
  simp [simpleSlice] at slice_def
  cases find_principal : entities.find? req.principal
    <;> simp [find_principal] at slice_def
  cases find_action : entities.find? req.action
    <;> simp [find_action] at slice_def
  cases find_resource : entities.find? req.resource
    <;> simp [find_resource] at slice_def
  rename_i principal action resource
  cases find_entities_in_context : (loadEuids req.context entities)
    <;> simp [find_entities_in_context] at slice_def
  rename_i context_entities
  have location : (euid, edata) ∈ (req.principal, principal) :: (req.action, action) :: (req.resource, resource) :: context_entities := by
    have in_kvs : (euid, edata) ∈ slice.kvs := by
      exact Map.find_means_mem in_slice
    apply Map.make_mem_list_mem
    rw [slice_def]
    assumption
  cases location
  -- It's the principal
  simp [in_slice, find_principal]
  rename_i location
  cases location
  -- It's the action
  simp [in_slice, find_action]
  rename_i location
  cases location
  -- It's the resource
  simp [in_slice, find_resource]
  rename_i location

  apply simpleSlice_context
  repeat assumption


theorem simpleSlice_respects_entity_schema (req : Request) (entities slice : Entities) (env : Environment)
  (h₁ : simpleSlice req entities = some slice)
  (h₂ : InstanceOfEntitySchema entities env.ets) :
  InstanceOfEntitySchema slice env.ets
  := by
  simp [InstanceOfEntitySchema]
  have is_subslice : subslice slice entities  := by
    apply simpleSlice_is_subslice
    assumption
  intros uid edata in_slice
  have in_full_store : edata = Map.find? entities uid := by
    rw [← in_slice]
    apply is_subslice
    apply in_slice
  apply h₂
  simp [in_full_store]





theorem simpleSlice_complete (euid : EntityUID) (request : Request) (entities slice : Entities)
  (slice_def : simpleSlice request entities = some slice )
  (euid_correct : euid = request.principal ∨ euid = request.action ∨ euid = request.resource ) :
  euid ∈ slice.keys
  := by
  simp [simpleSlice] at slice_def
  cases find_principal : Map.find? entities request.principal
    <;> simp [find_principal] at slice_def
  cases find_action : Map.find? entities request.action
    <;> simp [find_action] at slice_def
  cases find_resource : Map.find? entities request.resource
    <;> simp [find_resource] at slice_def
  cases find_context : loadEuids request.context entities
    <;> simp [find_context] at slice_def
  rename_i principal action resource context

  rw [← slice_def]
  rcases euid_correct with is_principal | is_action | is_resource
  case _ =>
    subst is_principal
    apply Map.in_constructor_in_keys
    simp
    apply Or.inl
    rfl
  case _ =>
    subst is_action
    apply Map.in_constructor_in_keys
    simp
    inrl
    rfl
  case _ =>
    subst is_resource
    apply Map.in_constructor_in_keys
    simp
    inrrl
    rfl

end Cedar.Thm
