import Cedar.Validation.RequestEntityValidator
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Validator

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation


-- For example, we could prove that actionSchema data is consistent with the result of updateSchema according to the constraints given in InstanceOfEntitySchema.

-- def InstanceOfEntitySchema (entities : Entities) (ets: EntitySchema) : Prop :=
--   ∀ uid data, entities.find? uid = some data →
--     ∃ entry, ets.find? uid.ty = some entry ∧
--       InstanceOfType data.attrs (.record entry.attrs) ∧
--       ∀ ancestor, ancestor ∈ data.ancestors → ancestor.ty ∈ entry.ancestors

-- We can also prove that the contents of a schema are always included in updateSchema, and finally, that nothing other than action type data is added by updateSchema.

-- From these, some auxiliary lemmas should follow easily. For example, if an entity is InstanceOfEntitySchema for the original schema, then it's also InstanceOfEntitySchema for the updated schema. And same for InstanceOfActionSchema.

def actionSchemaConsistentWithUpdateSchemaResults (schema newSchema : Schema) :
  newSchema = updateSchema schema →
  (∀ uid actsEntry, schema.acts.find? uid = some actsEntry →
  ∃ etsEntry, newSchema.ets.find? uid.ty = some etsEntry ∧
  ∀ ancestor ∈ actsEntry.ancestors, ancestor.ty ∈ etsEntry.ancestors)
:= by
  intro h₀ uid actsEntry h₁
  simp only [updateSchema, updateSchema.makeEntitySchemaEntries] at h₀
  sorry

def schemaIsWellFormed (schema newSchema : Schema) :
  newSchema = updateSchema schema →
  newSchema.acts = schema.acts ∧
  ∀ ty etsEntry, newSchema.ets.find? ty = some etsEntry →
  ((schema.ets.find? ty = some etsEntry) ∧ ¬ ((∃ uid actsEntry, uid.ty = ty ∧ schema.acts.find? uid = some actsEntry))
  ∨ ((¬ schema.ets.find? ty = some etsEntry) ∧ (∃ uid actsEntry, uid.ty = ty ∧ schema.acts.find? uid = some actsEntry)))
:= by
  intro h₀
  constructor
  case left =>
    simp only [updateSchema] at h₀
    simp [h₀]
  case right =>
    intro ty etsEntry h₁
    simp only [exists_and_left]
    simp only [updateSchema] at h₀
    generalize h₂ : List.map
            (fun x =>
              updateSchema.makeEntitySchemaEntries x (Map.mapOnValues actionSchemaEntryToEntityData schema.acts))
            (Set.make
                (Set.map (fun x => x.ty) (Map.mapOnValues actionSchemaEntryToEntityData schema.acts).keys).elts).elts = f
    rw [h₂] at h₀
    sorry
