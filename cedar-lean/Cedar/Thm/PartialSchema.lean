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

import Cedar.Thm.Validation.Typechecker.WF
import Cedar.Thm.Data.Map
import Cedar.Validation.PartialRequestEntityValidator

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

/--
Every ancestor set is transitively closed.
TODO: it is a bit suprising how this does not already exists.
Maybe define it for complete schema and see if it is useful for proving some nice facts about schema.
-/
def PartialEntitySchema.AncestorsClosed (schema : PartialEntitySchema) : Prop :=
  ∀ ety entry ancestor ancestorEntry,
    schema.find? ety = some entry →
    ancestor ∈ entry.ancestors →
    schema.find? ancestor = some ancestorEntry →
    ancestorEntry.ancestors ⊆ entry.ancestors

/--
A partial schema is well-formed when its definitions satisfy the existing
schema conditions and its externals satisfy those conditions using only their
known ancestors.
-/
def PartialSchema.WellFormed (schema : PartialSchema) : Prop :=
  let view := schema.validationView
  let env : TypeEnv := {
    ets := view.ets
    acts := view.acts
    reqty := default
  }
  schema.ets.AncestorsClosed ∧
  env.ets.WellFormed env ∧ env.acts.WellFormed env

/--
`t` keeps every declaration of `s`: its entity types with their definitions,
standard entity types, and listed ancestors, and its actions with their
ancestors and definitions.
-/
structure DeclarationsKept (s t : PartialSchema) : Prop where
  entities : ∀ ety, s.ets.contains ety → t.ets.contains ety
  definitions : ∀ ety entry, s.ets.find? ety = some (.defined entry) →
    t.ets.find? ety = some (.defined entry)
  standard : ∀ ety entry, s.ets.find? ety = some entry → entry.isStandard = true →
    ∃ entry', t.ets.find? ety = some entry' ∧ entry'.isStandard = true
  ancestors : ∀ ety entry ancestor, s.ets.find? ety = some entry → ancestor ∈ entry.ancestors →
    ∃ entry', t.ets.find? ety = some entry' ∧ ancestor ∈ entry'.ancestors
  actions : ∀ uid entry, s.acts.find? uid = some entry →
    ∃ entry', t.acts.find? uid = some entry' ∧ entry'.ancestors = entry.ancestors
  actionDefinitions : ∀ uid entry, s.acts.find? uid = some (.defined entry) →
    t.acts.find? uid = some (.defined entry)

---- Results ---

/-- Coercing a schema to a partial schema and back preserves it. -/
theorem toPartialSchema_asSchema? (schema : Schema) :
    (Schema.toPartialSchema schema).asSchema? = some schema := by
  simp only [Schema.toPartialSchema, PartialSchema.asSchema?,
    Map.mapMOnValues_mapOnValues]
  change (do
    let ets ← schema.ets.mapMOnValues some
    let acts ← schema.acts.mapMOnValues some
    pure { ets, acts }) = some schema
  rw [Map.mapMOnValues_some, Map.mapMOnValues_some]
  rfl

/-- Coercing a schema to a partial schema preserves its validation view. -/
theorem toPartialSchema_validationView (schema : Schema) :
    (Schema.toPartialSchema schema).validationView = schema := by
  cases schema
  simp only [Schema.toPartialSchema, PartialSchema.validationView,
    Map.mapOnValues_mapOnValues, Schema.mk.injEq]
  constructor <;>
    apply Map.mapOnValues_restricted_id <;>
    intro entry _ <;>
    rfl

/-- A partial schema converts to a schema exactly when it is complete. -/
theorem asSchema?_isSome_iff_isComplete (schema : PartialSchema) :
    schema.asSchema?.isSome ↔ schema.isComplete := by
  let entityResult := schema.ets.mapMOnValues
    PartialEntitySchemaEntry.toEntitySchemaEntry?
  let actionResult := schema.acts.mapMOnValues
    PartialActionSchemaEntry.toActionSchemaEntry?
  have hentities : entityResult.isSome =
      schema.ets.values.all (!·.isExternal) := by
    unfold entityResult
    rw [Map.mapMOnValues_isSome]
    apply congrArg (fun predicate => schema.ets.values.all predicate)
    funext entry
    cases entry <;> rfl
  have hactions : actionResult.isSome =
      schema.acts.values.all (!·.isExternal) := by
    unfold actionResult
    rw [Map.mapMOnValues_isSome]
    apply congrArg (fun predicate => schema.acts.values.all predicate)
    funext entry
    cases entry <;> rfl
  unfold PartialSchema.asSchema? PartialSchema.isComplete
  change ((do
    let ets ← entityResult
    let acts ← actionResult
    pure ({ ets, acts } : Schema)).isSome = true ↔
      (schema.ets.values.all (!·.isExternal) &&
        schema.acts.values.all (!·.isExternal)) = true)
  cases he : entityResult <;> cases ha : actionResult
  all_goals simp [he, ha] at hentities hactions ⊢
  all_goals grind

/-- The entity validation view maps the entry found in the partial schema. -/
theorem validationView_find?_ets (schema : PartialSchema) (ety : EntityType) :
    schema.validationView.ets.find? ety =
      (schema.ets.find? ety).map PartialEntitySchemaEntry.validationView := by
  simp [PartialSchema.validationView, Map.find?_mapOnValues]

/-- The action validation view maps the entry found in the partial schema. -/
theorem validationView_find?_acts (schema : PartialSchema) (uid : EntityUID) :
    schema.validationView.acts.find? uid =
      (schema.acts.find? uid).map PartialActionSchemaEntry.validationView := by
  simp [PartialSchema.validationView, Map.find?_mapOnValues]

/-- The validation view keeps an action's ancestors. -/
theorem PartialActionSchemaEntry.validationView_ancestors
    (entry : PartialActionSchemaEntry) :
    entry.validationView.ancestors = entry.ancestors := by
  cases entry <;> rfl

/-- A completed partial schema agrees with its validation view. -/
theorem validationView_eq_of_asSchema?
    {ps : PartialSchema} {schema : Schema}
    (h : ps.asSchema? = some schema) :
    ps.validationView = schema := by
  unfold PartialSchema.asSchema? at h
  cases he : ps.ets.mapMOnValues
      PartialEntitySchemaEntry.toEntitySchemaEntry? with
  | none => simp [he] at h
  | some ets =>
    cases ha : ps.acts.mapMOnValues
        PartialActionSchemaEntry.toActionSchemaEntry? with
    | none => simp [he, ha] at h
    | some acts =>
      simp only [he, ha, Option.bind_some_fun] at h
      change some ({ ets, acts } : Schema) = some schema at h
      injection h with h
      subst schema
      simp only [PartialSchema.validationView, Schema.mk.injEq]
      constructor
      · apply Map.mapOnValues_eq_of_mapMOnValues_some
          PartialEntitySchemaEntry.validationView he
        intro input output houtput
        cases input with
        | defined entry =>
          simp only [PartialEntitySchemaEntry.toEntitySchemaEntry?,
            Option.some.injEq] at houtput
          subst output
          rfl
        | external ancestors =>
          simp [PartialEntitySchemaEntry.toEntitySchemaEntry?] at houtput
      · apply Map.mapOnValues_eq_of_mapMOnValues_some
          PartialActionSchemaEntry.validationView ha
        intro input output houtput
        cases input with
        | defined entry =>
          simp only [PartialActionSchemaEntry.toActionSchemaEntry?,
            Option.some.injEq] at houtput
          subst output
          rfl
        | external ancestors =>
          simp [PartialActionSchemaEntry.toActionSchemaEntry?] at houtput

end Cedar.Validation
