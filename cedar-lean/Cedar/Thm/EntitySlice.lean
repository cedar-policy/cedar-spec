import Cedar.Data.Map
import Cedar.Spec.EntitySlice
import Cedar.Spec.Value
import Cedar.Thm.Entities
import Cedar.Thm.Data.Map
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Validation.Types

namespace Cedar.Thm
open Cedar.Data
open Cedar.Validation
open Cedar.Spec

theorem simpleSlice_is_subslice (req : Request) (entities slice : Entities)
  (h : simpleSlice req entities = some slice) :
  subslice slice entities
  := by
  simp [subslice]
  intros euid edata h'
  simp [simpleSlice] at h
  cases find_principal : entities.find? req.principal
    <;> simp [find_principal] at h
  cases find_action : entities.find? req.action
    <;> simp [find_action] at h
  cases find_resource : entities.find? req.resource
    <;> simp [find_resource] at h
  rename_i principal action resource
  have location : (euid, edata) ∈ [(req.principal, principal), (req.action, action), (req.resource, resource)] := by
    have in_map : (euid, edata) ∈ slice.kvs := by
      exact Map.find_means_mem h'
    apply Map.make_mem_list_mem
    rw [h]
    assumption
  rcases location with location | location
  case _ =>
    rw [h']
    rw [find_principal]
  rename_i location
  rcases location with location | location
  case _ =>
    rw [h']
    rw [find_action]
  rename_i location
  rcases location with location | location
  case _ =>
    rw [h']
    rw [find_resource]
  case _ =>
    rename_i location
    cases location

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











theorem simpleSlice_wf (req : Request) (entities slice : Entities) (env : Environment)
  (h₁ : simpleSlice req entities = some slice)
  (h₂ : InstanceOfRequestTypeLevel req env.reqty (.finite 1))
  (h₃ : InstanceOfEntitySchema entities env.ets)
  (h₃ : InstanceOfActionSchema entities env.acts)
  :
  RequestAndEntitiesMatchEnvironmentLeveled env request slice (.finite 1)
  := by
  simp [RequestAndEntitiesMatchEnvironmentLeveled]





  sorry









end Cedar.Thm
