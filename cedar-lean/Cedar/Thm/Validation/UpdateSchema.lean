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



def wf_schema (schema : Schema) : Prop :=
Map.WellFormed schema.ets ∧ Map.WellFormed schema.acts

def updateSchemaPreservesEntityTypes (schema newSchema : Schema) :
  wf_schema schema →
  wf_schema newSchema →
  newSchema = updateSchema schema →
  (∀ uid actsEntry, schema.acts.find? uid = some actsEntry →
  ∃ etsEntry, newSchema.ets.find? uid.ty = some etsEntry ∧
  ∀ ancestor ∈ actsEntry.ancestors, ancestor.ty ∈ etsEntry.ancestors)
:= by
  simp [wf_schema, Map.WellFormed, Map.toList]
  intro wfe₀ wfa₀ wfe₁ wfa₁ h₀ uid actsEntry h₁
  simp only [updateSchema] at h₀
  exists Prod.snd <| updateSchema.makeEntitySchemaEntries uid.ty (schema.acts.mapOnValues actionSchemaEntryToEntityData)
  constructor
  case left =>
    simp [h₀]
    generalize h₂ : (updateSchema.makeEntitySchemaEntries uid.ty (Map.mapOnValues actionSchemaEntryToEntityData schema.acts)) = etsPair
    have ⟨ety, etsEntry⟩ := etsPair
    simp only
    generalize h₃ : (Map.make
        (Map.kvs schema.ets ++
          (Map.make
              (List.map
                (fun x =>
                  updateSchema.makeEntitySchemaEntries x (Map.mapOnValues actionSchemaEntryToEntityData schema.acts))
                (Set.make
                    (Set.map (fun x => x.ty)
                        (Map.mapOnValues actionSchemaEntryToEntityData schema.acts).keys).elts).elts)).kvs)) = m₀
    have h₄ : Map.WellFormed m₀
    := by
      have h₅ := Map.make_wf ((Map.kvs schema.ets ++
      (Map.make
          (List.map
            (fun x =>
              updateSchema.makeEntitySchemaEntries x (Map.mapOnValues actionSchemaEntryToEntityData schema.acts))
            (Set.make
                (Set.map (fun x => x.ty)
                    (Map.mapOnValues actionSchemaEntryToEntityData schema.acts).keys).elts).elts)).kvs))
      rw [← h₃]
      exact h₅
    rw [← Map.in_list_iff_find?_some h₄]
    rw [← h₃]
    generalize h₅ : (List.map
              (fun x =>
                updateSchema.makeEntitySchemaEntries x (Map.mapOnValues actionSchemaEntryToEntityData schema.acts))
              (Set.make
                  (Set.map (fun x => x.ty)
                      (Map.mapOnValues actionSchemaEntryToEntityData schema.acts).keys).elts).elts) = m₁
    sorry
  case right =>
    intro ancestor ain
    sorry

def schemaIsWellFormed (schema newSchema : Schema) :
  wf_schema schema →
  wf_schema newSchema →
  newSchema = updateSchema schema →
  newSchema.acts = schema.acts ∧
  ∀ ty etsEntry, newSchema.ets.find? ty = some etsEntry →
  ((schema.ets.find? ty = some etsEntry)
  ∨ ((¬ schema.ets.find? ty = some etsEntry) ∧ (∃ uid actsEntry, uid.ty = ty ∧ schema.acts.find? uid = some actsEntry)))
:= by
  simp [wf_schema, Map.WellFormed, Map.toList]
  intro wfe₀ wfa₀ wfe₁ wfa₁ h₀
  constructor
  case left =>
    simp only [updateSchema] at h₀
    simp [h₀]
  case right =>
    intro ty etsEntry h₁
    simp only [updateSchema] at h₀
    generalize h₂ : List.map
            (fun x =>
              updateSchema.makeEntitySchemaEntries x (Map.mapOnValues actionSchemaEntryToEntityData schema.acts))
            (Set.make
                (Set.map (fun x => x.ty) (Map.mapOnValues actionSchemaEntryToEntityData schema.acts).keys).elts).elts = f
    rw [h₂] at h₀
    rw [h₀] at h₁
    simp only at h₁
    cases h₃ : Map.find? schema.ets ty with
    | none =>
      right
      constructor
      simp only [not_false_eq_true]
      sorry
    | some ese =>
      left
      simp only [Option.some.injEq]
      sorry
    -- have h₃ := Map.find_append_in_one (Map.kvs schema.ets) f ty etsEntry h₁
    -- cases h₃ with
    -- | inl h₃ =>
    --   left
    --   rw [← wfe₀] at h₃
    --   exact h₃
    -- | inr h₃ =>
    --   right
