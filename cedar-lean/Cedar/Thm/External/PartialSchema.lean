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
The environment in which `PartialSchema.WellFormed` checks a partial schema and
`PartialSchema.validateEntities` validates entities: the validation view with the
default request type.
-/
def PartialSchema.wfEnv (schema : PartialSchema) : TypeEnv :=
  { ets := schema.validationView.ets, acts := schema.validationView.acts, reqty := default }

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

/-- `z` keeps the definition, the standard kind, and the ancestors of the entity entry `x`. -/
structure EntryKept (x z : PartialEntitySchemaEntry) : Prop where
  definition : ∀ entry, x = .defined entry → z = .defined entry
  standard : x.isStandard = true → z.isStandard = true
  ancestors : x.ancestors ⊆ z.ancestors

/--
The definition that completes an entity entry: its definition, or a standard
entity type with its ancestors, the attributes `attrs`, and no tags.
-/
def PartialEntitySchemaEntry.completeWith (attrs : RecordType) :
    PartialEntitySchemaEntry → EntitySchemaEntry
  | .defined entry => entry
  | .external ancestors => .standard { ancestors, attrs, tags := none }

/--
The schema that completes `p`: it defines each external entity type of `p` with
the attributes `attrs`, and each external action by its validation view.
-/
def PartialSchema.completeWith (p : PartialSchema) (attrs : RecordType) : Schema where
  ets := p.ets.mapOnValues (PartialEntitySchemaEntry.completeWith attrs)
  acts := p.acts.mapOnValues PartialActionSchemaEntry.validationView

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

/-- Coercing a schema to a partial schema defines each of its entity types. -/
theorem toPartialSchema_ets_find? (schema : Schema) (ety : EntityType) :
    (Schema.toPartialSchema schema).ets.find? ety = (schema.ets.find? ety).map .defined :=
  Map.find?_mapOnValues _ _ _

/-- Coercing a schema to a partial schema defines each of its actions. -/
theorem toPartialSchema_acts_find? (schema : Schema) (uid : EntityUID) :
    (Schema.toPartialSchema schema).acts.find? uid = (schema.acts.find? uid).map .defined :=
  Map.find?_mapOnValues _ _ _

/-- A coerced schema is checked in the environment with its own maps. -/
theorem toPartialSchema_wfEnv (schema : Schema) :
    (Schema.toPartialSchema schema).wfEnv =
      { ets := schema.ets, acts := schema.acts, reqty := default } := by
  simp [PartialSchema.wfEnv, toPartialSchema_validationView]

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

-- Facts about entries.

/-- The validation view keeps an action's ancestors. -/
theorem PartialActionSchemaEntry.validationView_ancestors
    (entry : PartialActionSchemaEntry) :
    entry.validationView.ancestors = entry.ancestors := by
  cases entry <;> rfl

/-- The validation view keeps whether an entity type is standard or external. -/
theorem PartialEntitySchemaEntry.validationView_isStandard
    (entry : PartialEntitySchemaEntry) :
    entry.validationView.isStandard = entry.isStandard := by
  cases entry <;> rfl

/-- A standard or external entity type accepts every entity id in the validation view. -/
theorem PartialEntitySchemaEntry.validationView_isValidEntityEID
    {entry : PartialEntitySchemaEntry}
    (h : entry.isStandard = true)
    (eid : String) :
    entry.validationView.isValidEntityEID eid = true := by
  cases entry with
  | defined entry =>
    cases entry with
    | standard => rfl
    | enum => simp [PartialEntitySchemaEntry.isStandard, EntitySchemaEntry.isStandard] at h
  | external => rfl

/-- Replacing ancestors keeps an entry standard or external. -/
theorem PartialEntitySchemaEntry.withAncestors_isStandard
    (entry : PartialEntitySchemaEntry) (ancestors : Set EntityType) :
    (entry.withAncestors ancestors).isStandard = entry.isStandard := by
  cases entry with
  | defined entry => cases entry <;> rfl
  | external => rfl

-- Facts about well-formed partial schemas.

/-- A well-formed partial schema has a well-formed entity map. -/
theorem PartialSchema.WellFormed.etsMap
    {schema : PartialSchema} (h : schema.WellFormed) :
    schema.ets.WellFormed := by
  simp only [PartialSchema.WellFormed, PartialSchema.validationView] at h
  exact Map.mapOnValues_wf.mpr h.2.1.1

/-- A well-formed partial schema has a well-formed action map. -/
theorem PartialSchema.WellFormed.actsMap
    {schema : PartialSchema} (h : schema.WellFormed) :
    schema.acts.WellFormed := by
  simp only [PartialSchema.WellFormed, PartialSchema.validationView] at h
  exact Map.mapOnValues_wf.mpr h.2.2.1

/-- `PartialSchema.WellFormed` checks the maps in `wfEnv`. -/
theorem PartialSchema.wellFormed_iff {schema : PartialSchema} :
    schema.WellFormed ↔ schema.ets.AncestorsClosed ∧
      schema.wfEnv.ets.WellFormed schema.wfEnv ∧ schema.wfEnv.acts.WellFormed schema.wfEnv :=
  Iff.rfl

/-- Each entity entry of `wfEnv` is the view of an entry of the partial schema. -/
theorem PartialSchema.wfEnv_ets_find? {schema : PartialSchema} {ety : EntityType}
    {entry : EntitySchemaEntry} (h : schema.wfEnv.ets.find? ety = some entry) :
    ∃ entry', schema.ets.find? ety = some entry' ∧ entry'.validationView = entry :=
  Option.map_eq_some_iff.mp ((validationView_find?_ets schema ety).symm.trans h)

/-- Each action entry of `wfEnv` is the view of an entry of the partial schema. -/
theorem PartialSchema.wfEnv_acts_find? {schema : PartialSchema} {uid : EntityUID}
    {entry : ActionSchemaEntry} (h : schema.wfEnv.acts.find? uid = some entry) :
    ∃ entry', schema.acts.find? uid = some entry' ∧ entry'.validationView = entry :=
  Option.map_eq_some_iff.mp ((validationView_find?_acts schema uid).symm.trans h)

/-- `wfEnv` declares the entity types of the partial schema. -/
theorem PartialSchema.wfEnv_ets_contains (schema : PartialSchema) (ety : EntityType) :
    schema.wfEnv.ets.contains ety = schema.ets.contains ety := by
  simp [PartialSchema.wfEnv, EntitySchema.contains, Map.contains, validationView_find?_ets]

/-- `wfEnv` declares the actions of the partial schema. -/
theorem PartialSchema.wfEnv_acts_contains (schema : PartialSchema) (uid : EntityUID) :
    schema.wfEnv.acts.contains uid = schema.acts.contains uid := by
  simp [PartialSchema.wfEnv, ActionSchema.contains, Map.contains, validationView_find?_acts]

/-- In a well-formed partial schema, the view of each entity entry is well-formed. -/
theorem PartialSchema.WellFormed.entry {schema : PartialSchema} {ety : EntityType}
    {entry : PartialEntitySchemaEntry} (h : schema.WellFormed)
    (hfind : schema.ets.find? ety = some entry) :
    entry.validationView.WellFormed schema.wfEnv :=
  h.2.1.2 ety _ (by simp [validationView_find?_ets, hfind])

/-- In a well-formed partial schema, the view of each action is well-formed. -/
theorem PartialSchema.WellFormed.action {schema : PartialSchema} {uid : EntityUID}
    {entry : PartialActionSchemaEntry} (h : schema.WellFormed)
    (hfind : schema.acts.find? uid = some entry) :
    entry.validationView.WellFormed schema.wfEnv :=
  h.2.2.2.1 uid _ (by simp [validationView_find?_acts, hfind])

/-- In a well-formed partial schema, every ancestor of an entity type is standard or external. -/
theorem PartialSchema.WellFormed.ancestor_isStandard {schema : PartialSchema}
    {ety ancestor : EntityType} {entry : PartialEntitySchemaEntry} (h : schema.WellFormed)
    (hfind : schema.ets.find? ety = some entry) (hmem : ancestor ∈ entry.ancestors) :
    ∃ entry', schema.ets.find? ancestor = some entry' ∧ entry'.isStandard = true := by
  have hwf := h.entry hfind
  have hstd : ∃ ventry, schema.wfEnv.ets.find? ancestor = some ventry ∧ ventry.isStandard := by
    cases entry with
    | defined entry =>
      cases entry with
      | enum => exact absurd hmem (Set.not_mem_empty _)
      | standard => exact hwf.2.1 ancestor hmem
    | external => exact hwf.2.1 ancestor hmem
  obtain ⟨_, hventry, hstd⟩ := hstd
  obtain ⟨entry', hentry', rfl⟩ := PartialSchema.wfEnv_ets_find? hventry
  exact ⟨entry', hentry', by rwa [PartialEntitySchemaEntry.validationView_isStandard] at hstd⟩

/-- In a well-formed partial schema, every ancestor of an action is an action. -/
theorem PartialSchema.WellFormed.action_ancestor {schema : PartialSchema}
    {uid ancestor : EntityUID} {entry : PartialActionSchemaEntry} (h : schema.WellFormed)
    (hfind : schema.acts.find? uid = some entry) (hmem : ancestor ∈ entry.ancestors) :
    schema.acts.contains ancestor := by
  obtain ⟨-, -, -, -, -, hancestors, -⟩ := h.action hfind
  rw [← PartialSchema.wfEnv_acts_contains]
  exact hancestors ancestor (by rwa [PartialActionSchemaEntry.validationView_ancestors])

/-- A well-formed partial schema has no action among its own ancestors. -/
theorem PartialSchema.WellFormed.acyclic {schema : PartialSchema} {uid : EntityUID}
    {entry : PartialActionSchemaEntry} (h : schema.WellFormed)
    (hfind : schema.acts.find? uid = some entry) :
    uid ∉ entry.ancestors := by
  rw [← PartialActionSchemaEntry.validationView_ancestors]
  exact h.2.2.2.2.2.1 uid _ (by simp [validationView_find?_acts, hfind])

/-- A well-formed partial schema has transitively closed action ancestors. -/
theorem PartialSchema.WellFormed.transitive {schema : PartialSchema}
    {uid₁ uid₂ : EntityUID} {entry₁ entry₂ : PartialActionSchemaEntry}
    (h : schema.WellFormed)
    (hfind₁ : schema.acts.find? uid₁ = some entry₁)
    (hfind₂ : schema.acts.find? uid₂ = some entry₂)
    (hmem : uid₂ ∈ entry₁.ancestors) :
    entry₂.ancestors ⊆ entry₁.ancestors := by
  rw [← PartialActionSchemaEntry.validationView_ancestors,
    ← PartialActionSchemaEntry.validationView_ancestors]
  exact h.2.2.2.2.2.2 uid₁ _ uid₂ _
    (by simp [validationView_find?_acts, hfind₁])
    (by simp [validationView_find?_acts, hfind₂])
    (by rwa [PartialActionSchemaEntry.validationView_ancestors])

/-- A well-formed partial schema declares no action type as an entity type. -/
theorem PartialSchema.WellFormed.disjoint {schema : PartialSchema} {uid : EntityUID}
    (h : schema.WellFormed) (haction : schema.acts.contains uid) :
    ¬schema.ets.contains uid.ty := by
  rw [← PartialSchema.wfEnv_ets_contains]
  exact (PartialSchema.wellFormed_iff.mp h).2.2.2.2.1 uid
    (by rw [PartialSchema.wfEnv_acts_contains]; exact haction)

/-- In a well-formed partial schema, every entity entry has well-formed ancestors. -/
theorem PartialSchema.WellFormed.ancestors_wf {schema : PartialSchema}
    {ety : EntityType} {entry : PartialEntitySchemaEntry} (h : schema.WellFormed)
    (hfind : schema.ets.find? ety = some entry) :
    entry.ancestors.WellFormed := by
  have hwf := h.entry hfind
  cases entry with
  | defined entry =>
    cases entry with
    | standard => exact hwf.1
    | enum => exact Set.empty_wf
  | external => exact hwf.1

/-- With closed ancestors, every entity type reachable through listed ancestors is listed. -/
theorem PartialEntitySchema.AncestorsClosed.reach {ets : PartialEntitySchema}
    (h : ets.AncestorsClosed) {ety ancestor : EntityType} {entry : PartialEntitySchemaEntry}
    (hfind : ets.find? ety = some entry)
    (hreach : Relation.TransGen (fun x y => ∃ e, ets.find? x = some e ∧ y ∈ e.ancestors)
      ety ancestor) :
    ancestor ∈ entry.ancestors := by
  induction hreach with
  | single hedge =>
    obtain ⟨e, he, hmem⟩ := hedge
    rw [hfind, Option.some.injEq] at he
    exact he ▸ hmem
  | tail _ hedge ih =>
    obtain ⟨e, he, hmem⟩ := hedge
    exact Set.mem_subset_mem hmem (h _ _ _ _ hfind ih he)

/-- An external action's view is well-formed when its ancestors are a well-formed set of actions. -/
theorem PartialActionSchemaEntry.external_validationView_wf {env : TypeEnv}
    {ancestors : Set EntityUID} (hwf : ancestors.WellFormed)
    (hactions : ∀ a ∈ ancestors, env.acts.contains a) :
    (PartialActionSchemaEntry.external ancestors).validationView.WellFormed env :=
  ⟨Set.empty_wf, Set.empty_wf, hwf,
    fun _ h => by simp [PartialActionSchemaEntry.validationView, Set.contains] at h,
    fun _ h => by simp [PartialActionSchemaEntry.validationView, Set.contains] at h,
    hactions, emptyRecord_wf, emptyRecord_lifted⟩

-- Facts about `DeclarationsKept`.

/-- `t` declares every action of `s`. -/
theorem DeclarationsKept.acts_contains {s t : PartialSchema} (h : DeclarationsKept s t)
    {uid : EntityUID} (hs : s.acts.contains uid) :
    t.acts.contains uid := by
  obtain ⟨entry, hentry⟩ := Map.contains_iff_some_find?.mp hs
  obtain ⟨entry', hentry', -⟩ := h.actions uid entry hentry
  exact Map.contains_iff_some_find?.mpr ⟨entry', hentry'⟩

/-- An entity type well-formed for `s` is well-formed for `t`. -/
theorem DeclarationsKept.entityType_wf {s t : PartialSchema} (h : DeclarationsKept s t)
    {ety : EntityType} (hwf : EntityType.WellFormed s.wfEnv ety) :
    EntityType.WellFormed t.wfEnv ety := by
  rcases hwf with hets | ⟨uid, hacts, hty⟩
  · left
    rw [PartialSchema.wfEnv_ets_contains] at hets ⊢
    exact h.entities ety hets
  · right
    rw [PartialSchema.wfEnv_acts_contains] at hacts
    exact ⟨uid, by rw [PartialSchema.wfEnv_acts_contains]; exact h.acts_contains hacts, hty⟩

/-- A type well-formed for `s` is well-formed for `t`. -/
theorem DeclarationsKept.cedarType_wf {s t : PartialSchema} (h : DeclarationsKept s t)
    {ty : CedarType} (hwf : CedarType.WellFormed s.wfEnv ty) :
    CedarType.WellFormed t.wfEnv ty :=
  CedarType.WellFormed.mono (fun _ => h.entityType_wf) hwf

/-- An ancestor listed in a well-formed `s` is standard or external in `t`. -/
theorem DeclarationsKept.ancestor_isStandard {s t : PartialSchema}
    (h : DeclarationsKept s t) (hs : s.WellFormed) {ety ancestor : EntityType}
    {entry : PartialEntitySchemaEntry}
    (hfind : s.ets.find? ety = some entry) (hmem : ancestor ∈ entry.ancestors) :
    ∃ ventry, t.wfEnv.ets.find? ancestor = some ventry ∧ ventry.isStandard = true := by
  obtain ⟨entry', hentry', hstd⟩ := hs.ancestor_isStandard hfind hmem
  obtain ⟨entry'', hentry'', hstd'⟩ := h.standard _ _ hentry' hstd
  exact ⟨entry''.validationView,
    by rw [PartialSchema.wfEnv, validationView_find?_ets, hentry'']; rfl,
    by rw [PartialEntitySchemaEntry.validationView_isStandard]; exact hstd'⟩

/-- A definition of a well-formed `s` is well-formed in `t`. -/
theorem DeclarationsKept.definition_wf {s t : PartialSchema}
    (h : DeclarationsKept s t) (hs : s.WellFormed) {ety : EntityType}
    {entry : EntitySchemaEntry} (hfind : s.ets.find? ety = some (.defined entry)) :
    entry.WellFormed t.wfEnv := by
  have hwf := hs.entry hfind
  cases entry with
  | enum => exact hwf
  | standard std =>
    obtain ⟨hancestors, -, hattrs, hlifted, htags⟩ := hwf
    exact ⟨hancestors, fun _ hmem => h.ancestor_isStandard hs hfind hmem,
      h.cedarType_wf hattrs, hlifted,
      fun ty hty => ⟨h.cedarType_wf (htags ty hty).1, (htags ty hty).2⟩⟩

/-- An action of a well-formed `s` is well-formed in `t`. -/
theorem DeclarationsKept.action_wf {s t : PartialSchema}
    (h : DeclarationsKept s t) (hs : s.WellFormed) {uid : EntityUID}
    {entry : PartialActionSchemaEntry} (hfind : s.acts.find? uid = some entry) :
    entry.validationView.WellFormed t.wfEnv := by
  obtain ⟨h₁, h₂, h₃, hprincipals, hresources, hancestors, hcontext, hlifted⟩ :=
    hs.action hfind
  refine ⟨h₁, h₂, h₃, fun ety hety => h.entityType_wf (hprincipals ety hety),
    fun ety hety => h.entityType_wf (hresources ety hety), fun uid hmem => ?_,
    h.cedarType_wf hcontext, hlifted⟩
  have := hancestors uid hmem
  rw [PartialSchema.wfEnv_acts_contains] at this ⊢
  exact h.acts_contains this

/--
In `t`, the ancestors of an ancestor of an action of a well-formed `s` are
ancestors of that action.
-/
theorem DeclarationsKept.transitive {s t : PartialSchema}
    (h : DeclarationsKept s t) (hs : s.WellFormed) {uid₁ uid₂ : EntityUID}
    {entry₁ entry₂ : PartialActionSchemaEntry}
    (hfind₁ : s.acts.find? uid₁ = some entry₁)
    (hfind₂ : t.acts.find? uid₂ = some entry₂)
    (hmem : uid₂ ∈ entry₁.ancestors) :
    entry₂.ancestors ⊆ entry₁.ancestors := by
  obtain ⟨entry₂', hentry₂'⟩ :=
    Map.contains_iff_some_find?.mp (hs.action_ancestor hfind₁ hmem)
  obtain ⟨entry₂'', hentry₂'', hancestors⟩ := h.actions _ _ hentry₂'
  rw [hfind₂, Option.some.injEq] at hentry₂''
  rw [hentry₂'', hancestors]
  exact hs.transitive hfind₁ hentry₂' hmem

/-- Keeping declarations is transitive. -/
theorem DeclarationsKept.trans {s t u : PartialSchema}
    (hst : DeclarationsKept s t) (htu : DeclarationsKept t u) :
    DeclarationsKept s u where
  entities ety h := htu.entities ety (hst.entities ety h)
  definitions ety entry h := htu.definitions ety entry (hst.definitions ety entry h)
  standard ety entry h hstd :=
    let ⟨_, h', hstd'⟩ := hst.standard ety entry h hstd
    htu.standard ety _ h' hstd'
  ancestors ety entry a h ha :=
    let ⟨_, h', ha'⟩ := hst.ancestors ety entry a h ha
    htu.ancestors ety _ a h' ha'
  actions uid entry h :=
    let ⟨_, h', hancestors'⟩ := hst.actions uid entry h
    let ⟨entry'', h'', hancestors''⟩ := htu.actions uid _ h'
    ⟨entry'', h'', hancestors''.trans hancestors'⟩
  actionDefinitions uid entry h :=
    htu.actionDefinitions uid entry (hst.actionDefinitions uid entry h)

/-- The entry of `t` for an entity type of `s` keeps the entry of `s`. -/
theorem DeclarationsKept.entry {s t : PartialSchema} (h : DeclarationsKept s t)
    {ety : EntityType} {x z : PartialEntitySchemaEntry}
    (hx : s.ets.find? ety = some x) (hz : t.ets.find? ety = some z) :
    EntryKept x z where
  definition entry hentry := by
    have := h.definitions ety entry (hentry ▸ hx)
    rwa [hz, Option.some.injEq] at this
  standard hstd := by
    obtain ⟨z', hz', hstd'⟩ := h.standard ety x hx hstd
    rw [hz, Option.some.injEq] at hz'
    exact hz' ▸ hstd'
  ancestors := Set.subset_def.mpr fun a ha => by
    obtain ⟨z', hz', ha'⟩ := h.ancestors ety x a hx ha
    rw [hz, Option.some.injEq] at hz'
    exact hz' ▸ ha'

/-- Well-formed partial schemas that keep each other's declarations are equal. -/
theorem DeclarationsKept.antisymm {s t : PartialSchema}
    (hs : s.WellFormed) (ht : t.WellFormed)
    (hst : DeclarationsKept s t) (hts : DeclarationsKept t s) :
    s = t := by
  have hets : s.ets = t.ets := by
    refine Map.find?_ext hs.etsMap ht.etsMap fun ety => ?_
    cases hx : s.ets.find? ety with
    | none =>
      cases hz : t.ets.find? ety with
      | none => rfl
      | some z =>
        have := hts.entities ety (Map.find?_some_implies_contains hz)
        simp [Map.contains, hx] at this
    | some x =>
      obtain ⟨z, hz⟩ := Map.contains_iff_some_find?.mp
        (hst.entities ety (Map.find?_some_implies_contains hx))
      rw [hz]
      have hxz := hst.entry hx hz
      have hzx := hts.entry hz hx
      cases x with
      | defined entry => rw [hxz.definition entry rfl]
      | external =>
        cases z with
        | defined entry => rw [hzx.definition entry rfl]
        | external =>
          have heq := (Set.subset_iff_eq (hs.ancestors_wf hx) (ht.ancestors_wf hz)).mp
            ⟨hxz.ancestors, hzx.ancestors⟩
          simp only [PartialEntitySchemaEntry.ancestors] at heq
          rw [heq]
  have hacts : s.acts = t.acts := by
    refine Map.find?_ext hs.actsMap ht.actsMap fun uid => ?_
    cases hx : s.acts.find? uid with
    | none =>
      cases hz : t.acts.find? uid with
      | none => rfl
      | some z =>
        obtain ⟨_, hx', -⟩ := hts.actions uid z hz
        simp [hx] at hx'
    | some x =>
      obtain ⟨z, hz, hancestors⟩ := hst.actions uid x hx
      rw [hz]
      cases x with
      | defined entry => rw [← hz, hst.actionDefinitions uid entry hx]
      | external =>
        cases z with
        | defined entry => simp [hts.actionDefinitions uid entry hz] at hx
        | external =>
          simp only [PartialActionSchemaEntry.ancestors] at hancestors
          rw [hancestors]
  cases s
  cases t
  dsimp only at hets hacts
  rw [hets, hacts]

/-- A partial schema with well-formed maps is a schema that it keeps and that keeps it. -/
theorem DeclarationsKept.eq_toPartialSchema {t : PartialSchema} {schema : Schema}
    (hets : t.ets.WellFormed) (hacts : t.acts.WellFormed)
    (hschema : (Schema.toPartialSchema schema).WellFormed)
    (hts : DeclarationsKept t schema) (hst : DeclarationsKept schema t) :
    t = schema := by
  -- The schema defines every key it declares; `t` keeps these definitions and has no other key.
  have hets : t.ets = (Schema.toPartialSchema schema).ets := by
    refine Map.find?_ext hets hschema.etsMap fun ety => ?_
    rw [toPartialSchema_ets_find?]
    cases hx : schema.ets.find? ety with
    | some d => exact hst.definitions ety d (by rw [toPartialSchema_ets_find?, hx]; rfl)
    | none =>
      cases hz : t.ets.find? ety with
      | none => rfl
      | some z =>
        have := hts.entities ety (Map.find?_some_implies_contains hz)
        simp [Map.contains, toPartialSchema_ets_find?, hx] at this
  have hacts : t.acts = (Schema.toPartialSchema schema).acts := by
    refine Map.find?_ext hacts hschema.actsMap fun uid => ?_
    rw [toPartialSchema_acts_find?]
    cases hx : schema.acts.find? uid with
    | some d => exact hst.actionDefinitions uid d (by rw [toPartialSchema_acts_find?, hx]; rfl)
    | none =>
      cases hz : t.acts.find? uid with
      | none => rfl
      | some z =>
        obtain ⟨_, hz', -⟩ := hts.actions uid z hz
        simp [toPartialSchema_acts_find?, hx] at hz'
  obtain ⟨ets, acts⟩ := t
  dsimp only at hets hacts
  rw [hets, hacts]

-- Facts about `completeWith`.

/-- Completing a partial schema completes each of its entity entries. -/
theorem completeWith_ets_find? (p : PartialSchema) (attrs : RecordType) (ety : EntityType) :
    (p.completeWith attrs).ets.find? ety = (p.ets.find? ety).map (·.completeWith attrs) :=
  Map.find?_mapOnValues _ _ _

/-- Completing with no attributes gives the validation view. -/
theorem completeWith_empty (p : PartialSchema) : p.completeWith Map.empty = p.validationView := by
  have hentry : PartialEntitySchemaEntry.completeWith Map.empty =
      PartialEntitySchemaEntry.validationView := by
    funext entry
    cases entry <;> rfl
  simp [PartialSchema.completeWith, PartialSchema.validationView, hentry]

/-- Completing an entry keeps its ancestors. -/
theorem PartialEntitySchemaEntry.completeWith_ancestors (attrs : RecordType)
    (entry : PartialEntitySchemaEntry) :
    (entry.completeWith attrs).ancestors = entry.ancestors := by
  cases entry <;> rfl

/-- Completing an entry keeps whether it is standard or external. -/
theorem PartialEntitySchemaEntry.completeWith_isStandard (attrs : RecordType)
    (entry : PartialEntitySchemaEntry) :
    (entry.completeWith attrs).isStandard = entry.isStandard := by
  cases entry <;> rfl

/-- The partial schema of a completion defines each entity type of `p` by its completion. -/
theorem toPartialSchema_completeWith_ets_find? (p : PartialSchema) (attrs : RecordType)
    (ety : EntityType) :
    (Schema.toPartialSchema (p.completeWith attrs)).ets.find? ety =
      (p.ets.find? ety).map fun entry => .defined (entry.completeWith attrs) := by
  rw [toPartialSchema_ets_find?, completeWith_ets_find?, Option.map_map]
  rfl

/-- The partial schema of a completion defines each action of `p` by its validation view. -/
theorem toPartialSchema_completeWith_acts_find? (p : PartialSchema) (attrs : RecordType)
    (uid : EntityUID) :
    (Schema.toPartialSchema (p.completeWith attrs)).acts.find? uid =
      (p.acts.find? uid).map fun entry => .defined entry.validationView := by
  simp only [toPartialSchema_acts_find?, PartialSchema.completeWith, Map.find?_mapOnValues,
    Option.map_map]
  rfl

/-- Completing `p` keeps the declarations of `p`. -/
theorem DeclarationsKept.completeWith (p : PartialSchema) (attrs : RecordType) :
    DeclarationsKept p (p.completeWith attrs) where
  entities ety h := by
    simpa [Map.contains, toPartialSchema_completeWith_ets_find?] using h
  definitions ety entry h := by
    rw [toPartialSchema_completeWith_ets_find?, h]
    rfl
  standard ety entry h hstd :=
    ⟨.defined (entry.completeWith attrs), by rw [toPartialSchema_completeWith_ets_find?, h]; rfl,
      by rw [← hstd]; exact PartialEntitySchemaEntry.completeWith_isStandard attrs entry⟩
  ancestors ety entry a h ha :=
    ⟨.defined (entry.completeWith attrs), by rw [toPartialSchema_completeWith_ets_find?, h]; rfl,
      by
        show a ∈ (entry.completeWith attrs).ancestors
        rwa [PartialEntitySchemaEntry.completeWith_ancestors]⟩
  actions uid entry h :=
    ⟨.defined entry.validationView, by rw [toPartialSchema_completeWith_acts_find?, h]; rfl,
      PartialActionSchemaEntry.validationView_ancestors entry⟩
  actionDefinitions uid entry h := by
    rw [toPartialSchema_completeWith_acts_find?, h]
    rfl

/-- Completing a well-formed partial schema with well-formed lifted attributes is well-formed. -/
theorem PartialSchema.WellFormed.completeWith {p : PartialSchema} {attrs : RecordType}
    (hp : p.WellFormed) (hwf : ∀ env, (CedarType.record attrs).WellFormed env)
    (hlifted : (CedarType.record attrs).IsLifted) :
    PartialSchema.WellFormed (p.completeWith attrs) := by
  have hpu := DeclarationsKept.completeWith p attrs
  rw [PartialSchema.wellFormed_iff]
  refine ⟨?closed, ⟨?etsMap, ?ets⟩, ⟨?actsMap, ?acts, ?disjoint, ?acyclic, ?transitive⟩⟩
  case closed =>
    intro ety entry ancestor ancestorEntry hfind hmem hfind'
    rw [toPartialSchema_completeWith_ets_find?, Option.map_eq_some_iff] at hfind hfind'
    obtain ⟨pe, hpe, rfl⟩ := hfind
    obtain ⟨pa, hpa, rfl⟩ := hfind'
    change ancestor ∈ (pe.completeWith attrs).ancestors at hmem
    change (pa.completeWith attrs).ancestors ⊆ (pe.completeWith attrs).ancestors
    rw [PartialEntitySchemaEntry.completeWith_ancestors] at hmem ⊢
    rw [PartialEntitySchemaEntry.completeWith_ancestors]
    exact hp.1 _ _ _ _ hpe hmem hpa
  case etsMap =>
    exact Map.mapOnValues_wf.mp (Map.mapOnValues_wf.mp (Map.mapOnValues_wf.mp hp.etsMap))
  case ets =>
    -- Definitions are those of `p`, and externals become standard entity types with `attrs`.
    intro ety ventry hventry
    obtain ⟨entry, hfind, rfl⟩ := PartialSchema.wfEnv_ets_find? hventry
    rw [toPartialSchema_completeWith_ets_find?, Option.map_eq_some_iff] at hfind
    obtain ⟨pe, hpe, rfl⟩ := hfind
    cases pe with
    | defined => exact hpu.definition_wf hp hpe
    | external =>
      exact standardEntry_wf (hp.ancestors_wf hpe) (fun _ ha => hpu.ancestor_isStandard hp hpe ha)
        (hwf _) hlifted
  case actsMap =>
    exact Map.mapOnValues_wf.mp (Map.mapOnValues_wf.mp (Map.mapOnValues_wf.mp hp.actsMap))
  case acts =>
    intro uid ventry hventry
    obtain ⟨entry, hfind, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry
    rw [toPartialSchema_completeWith_acts_find?, Option.map_eq_some_iff] at hfind
    obtain ⟨pa, hpa, rfl⟩ := hfind
    have hwf := hpu.action_wf hp hpa
    exact hwf
  case disjoint =>
    intro uid haction
    rw [PartialSchema.wfEnv_acts_contains] at haction
    rw [PartialSchema.wfEnv_ets_contains]
    simp only [Map.contains, toPartialSchema_completeWith_ets_find?,
      toPartialSchema_completeWith_acts_find?, Option.isSome_map] at haction ⊢
    exact hp.disjoint haction
  case acyclic =>
    intro uid ventry hventry
    obtain ⟨entry, hfind, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry
    rw [toPartialSchema_completeWith_acts_find?, Option.map_eq_some_iff] at hfind
    obtain ⟨pa, hpa, rfl⟩ := hfind
    change uid ∉ pa.validationView.ancestors
    rw [PartialActionSchemaEntry.validationView_ancestors]
    exact hp.acyclic hpa
  case transitive =>
    intro uid₁ ventry₁ uid₂ ventry₂ hventry₁ hventry₂ hmem
    obtain ⟨entry₁, hfind₁, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry₁
    obtain ⟨entry₂, hfind₂, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry₂
    rw [toPartialSchema_completeWith_acts_find?, Option.map_eq_some_iff] at hfind₁ hfind₂
    obtain ⟨pa₁, hpa₁, rfl⟩ := hfind₁
    obtain ⟨pa₂, hpa₂, rfl⟩ := hfind₂
    change uid₂ ∈ pa₁.validationView.ancestors at hmem
    change pa₂.validationView.ancestors ⊆ pa₁.validationView.ancestors
    simp only [PartialActionSchemaEntry.validationView_ancestors] at hmem ⊢
    exact hp.transitive hpa₁ hpa₂ hmem

end Cedar.Validation
