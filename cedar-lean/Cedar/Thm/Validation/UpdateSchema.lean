import Cedar.Validation.RequestEntityValidator
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Validator

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-!
This file proves properties about the `updateSchema` utility function.
-/

/-- `updateSchema` does not modify the action part of the schema. -/
def update_schema_preserves_action_schema (schema : Schema) :
  (updateSchema schema).acts = schema.acts
:= by simp only [updateSchema]

/--
In order to apply `updateSchema` safely, no actions types should be defined in
entity type store. We expect the Rust code to produce schemas that satisfy this
requirement.

(Technically, we could be more flexible here and say that re-definition is allowed
as long as the two definitions are consistent, but that generalization is not
needed at the moment.)
-/
def NoActionTypesInETS (schema : Schema) : Prop :=
  ∀ uid ∈ schema.acts, uid.ty ∉ schema.ets

def EntriesMatch (actsEntry: EntityUID × ActionSchemaEntry) (etsEntry: EntityType × EntitySchemaEntry) : Prop :=
  actsEntry.1.ty = etsEntry.1 ∧ ∀ ancestor ∈ actsEntry.2.ancestors, ancestor.ty ∈ etsEntry.2.ancestors

def mem_action_schema_to_entity_schema (acts : ActionSchema) :
  ∀ ty etsEntry, (ty, etsEntry) ∈ (actionSchemaToEntitySchema acts).kvs →
  ∃ uid actsEntry, (uid, actsEntry) ∈ acts.kvs ∧ EntriesMatch (uid, actsEntry) (ty, etsEntry)
:= by
  intro ty etsEntry h₀
  simp only [actionSchemaToEntitySchema] at h₀
  replace h₀ := Map.make_mem_list_mem h₀
  -- TODO
  sorry

def no_action_types_in_ets_implies_disjoint (schema : Schema) :
  NoActionTypesInETS schema →
  schema.ets.Disjoint (actionSchemaToEntitySchema schema.acts)
:= by
   -- TODO
   sorry

/--
`updateSchema` preserves existing entity types in the schema, assuming there
is no overlap with the action types.
-/
def update_schema_preserves_entity_types (schema : Schema) :
  NoActionTypesInETS schema →
  ∀ ty etsEntry, (ty, etsEntry) ∈ schema.ets.kvs →
  (ty, etsEntry) ∈ (updateSchema schema).ets.kvs
:= by
  intro h₀ ty etsEntry h₁
  simp only [updateSchema]
  apply Map.mem_append_converse
  apply no_action_types_in_ets_implies_disjoint
  assumption
  left
  assumption

/--
`updateSchema` adds an appropriate entity type for every action, assuming there
is no overlap between entity and action types.
-/
def update_schema_adds_action_entity_types (schema : Schema) :
  NoActionTypesInETS schema →
  ∀ uid actsEntry, (uid, actsEntry) ∈ schema.acts.kvs →
  ∃ ty etsEntry, (ty, etsEntry) ∈ (updateSchema schema).ets.kvs ∧
  EntriesMatch (uid, actsEntry) (ty, etsEntry)
:= by
  intro h₀ uid actsEntry h₁
  simp only [updateSchema]
  exists uid.ty
  exists Prod.snd (makeEntitySchemaEntry uid.ty (schema.acts.mapOnValues actionSchemaEntryToEntityData))
  constructor
  case left =>
    generalize h₂ : (makeEntitySchemaEntry uid.ty (schema.acts.mapOnValues actionSchemaEntryToEntityData)) = etsPair
    replace ⟨ety, etsEntry⟩ := etsPair
    simp only
    apply Map.mem_append_converse
    apply no_action_types_in_ets_implies_disjoint
    assumption
    right
    -- TODO
    sorry
  case right =>
    -- TODO
    sorry

/--
`updateSchema` doesn't add any new entity type entries, beyond what is covered
by `update_schema_preserves_entity_types` and `update_schema_adds_action_entities`.
I.e. every entity type in the updated schema is either a type from the original
schema, or there exists some action with that type.
-/
def update_schema_does_not_add_extra_types (schema : Schema) :
  ∀ ty etsEntry, (ty, etsEntry) ∈ (updateSchema schema).ets.kvs →
  (ty, etsEntry) ∈ schema.ets.kvs ∨
  ∃ uid actsEntry, (uid, actsEntry) ∈ schema.acts.kvs ∧ EntriesMatch (uid, actsEntry) (ty, etsEntry)
:= by
  intro ty etsEntry h₀
  simp only [updateSchema] at h₀
  replace h₀ := Map.mem_append _ _ _ _ h₀
  cases h₀
  left
  assumption
  rename_i h₁
  right
  apply mem_action_schema_to_entity_schema
  assumption
