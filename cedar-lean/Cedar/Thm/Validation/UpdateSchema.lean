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
∧ (∀ k ∈ schema.acts, k.ty ∉ schema.ets)

def updateSchemaPreservesEntityTypes (schema newSchema : Schema) :
  wf_schema schema →
  wf_schema newSchema →
  newSchema = updateSchema schema →
  (∀ uid actsEntry, schema.acts.find? uid = some actsEntry →
  ∃ etsEntry, newSchema.ets.find? uid.ty = some etsEntry ∧
  ∀ ancestor ∈ actsEntry.ancestors, ancestor.ty ∈ etsEntry.ancestors)
:= by
  simp [wf_schema]
  -- simp [wf_schema, Map.WellFormed, Map.toList]
  intro wfe₀ wfa₀ sch₀ wfe₁ wfa₁ sch₁ h₀ uid actsEntry h₁
  simp only [updateSchema] at h₀
  exists Prod.snd <| updateSchema.makeEntitySchemaEntries uid.ty (schema.acts.mapOnValues actionSchemaEntryToEntityData)
  constructor
  case left =>
    simp [h₀]
    generalize h₂ : (updateSchema.makeEntitySchemaEntries uid.ty (Map.mapOnValues actionSchemaEntryToEntityData schema.acts)) = etsPair
    have ⟨ety, etsEntry⟩ := etsPair
    simp only
    generalize h₃ : (List.map
          (fun x => updateSchema.makeEntitySchemaEntries x (Map.mapOnValues actionSchemaEntryToEntityData schema.acts))
          (Set.make
              (Set.map (fun x => x.ty) (Map.mapOnValues actionSchemaEntryToEntityData schema.acts).keys).elts).elts) = m₀
    rw [← Map.in_list_iff_find?_some]
    apply Map.mem_append
    have h₄ : uid.ty = ety := by
      simp [updateSchema.makeEntitySchemaEntries] at h₂
      simp [h₂]
    subst h₄
    right
    have h₄ : uid ∈ (Map.mapOnValues actionSchemaEntryToEntityData schema.acts).keys := by
      rw [Map.keys_mapOnValues]
      have h₅ := Map.find?_mem_toList h₁
      simp [Map.toList] at h₅
      simp [Map.in_list_in_keys h₅]
    have h₅ : uid.ty ∈ ((Set.map (fun x => x.ty) (Map.mapOnValues actionSchemaEntryToEntityData schema.acts).keys)) := by
      simp [Set.map]
      rw [← Set.make_mem]
      simp [Set.elts]
      exists uid
    have ⟨h₆, _⟩ := Set.make_mem uid.ty (Set.map (fun x => x.ty) (Map.mapOnValues actionSchemaEntryToEntityData schema.acts).keys).elts
    rw [← Set.in_list_iff_in_set] at h₅
    simp [h₅] at h₆
    rw [← Set.in_list_iff_in_set] at h₆
    generalize h₇ : (fun x => updateSchema.makeEntitySchemaEntries x (Map.mapOnValues actionSchemaEntryToEntityData schema.acts)) = f
    rw [h₇] at h₃
    generalize h₈ : (Set.make (Set.map (fun x => x.ty) (Map.mapOnValues actionSchemaEntryToEntityData schema.acts).keys).elts).elts = s
    rw [h₈] at h₃
    rw [h₈] at h₆
    have h₉ := List.mem_map_of_mem f h₆
    rw [h₃] at h₉
    rw [← h₇] at h₉
    simp only at h₉
    rw [h₂] at h₉
    apply Map.mem_list_mem_make

    sorry
    exact h₉
    have h₄ : Map.WellFormed (Map.make m₀) := by simp [Map.make_wf m₀]
    apply Map.wf_append wfe₀ h₄
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
  intro wfe₀ wfa₀ sch₀ wfe₁ wfa₁ sch₁ h₀
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
