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

import Cedar.Thm.External.Linker
import Cedar.Thm.Validation.RequestEntityValidation

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

---- Helpers ---

/-- Linking keeps every action of the first schema's validation view, with the same ancestors. -/
private theorem link_validationView_acts
    {p c t : PartialSchema}
    {uid : EntityUID}
    {entry : ActionSchemaEntry}
    (hlink : link p c = .ok t)
    (hfind : p.validationView.acts.find? uid = some entry) :
    ∃ entry', t.validationView.acts.find? uid = some entry' ∧ entry'.ancestors = entry.ancestors := by
  rw [validationView_find?_acts, Option.map_eq_some_iff] at hfind
  obtain ⟨action, haction, rfl⟩ := hfind
  obtain ⟨action', haction', hancestors⟩ := (linker_preserves_action_ancestors hlink).1 _ _ haction
  refine ⟨action'.validationView, ?_, ?_⟩
  · rw [validationView_find?_acts, haction', Option.map_some]
  · rw [action'.validationView_ancestors, action.validationView_ancestors, hancestors]

-- A record type with a required attribute. Completing an external entity type with it, and with
-- no attributes, gives two completions that no entity passes both of.

/-- A record type with one required attribute. -/
private def requiredAttr : RecordType := Map.make [("", .required .int)]

private theorem requiredAttr_toList : requiredAttr.toList = [("", .required .int)] := rfl

private theorem requiredAttr_find? : requiredAttr.find? "" = some (.required .int) := rfl

private theorem requiredAttr_mem {a : Attr} {qty : QualifiedType}
    (h : (a, qty) ∈ requiredAttr.toList) :
    qty = .required .int := by
  simp only [requiredAttr_toList, List.mem_singleton, Prod.mk.injEq] at h
  exact h.2

private theorem requiredAttr_wf (env : TypeEnv) : (CedarType.record requiredAttr).WellFormed env :=
  .record_wf (Map.make_wf _) fun _ _ hfind => by
    rw [requiredAttr_mem (Map.find?_mem_toList hfind)]
    exact .required_wf .int_wf

private theorem requiredAttr_lifted : (CedarType.record requiredAttr).IsLifted :=
  .record_lifted fun _ _ hmem => by
    rw [requiredAttr_mem hmem]
    exact .required_lifted .int_lifted

---- Minor Validation Results ---

/--
Partial entity validation accepts a store exactly when no entity has an external
type and every entity is valid in `wfEnv`.
-/
theorem PartialSchema.validateEntities_ok_iff {ps : PartialSchema} {entities : Entities} :
    ps.validateEntities entities = .ok () ↔
      ∀ uid data, (uid, data) ∈ entities.toList →
        (∀ ancestors, ps.ets.find? uid.ty ≠ some (.external ancestors)) ∧
        instanceOfSchema.instanceOfSchemaEntry ps.wfEnv uid data = .ok () := by
  unfold PartialSchema.validateEntities
  constructor
  · intro h uid data hmem
    have hstep := List.forM_ok_implies_all_ok' h (uid, data) hmem
    simp only at hstep
    split at hstep
    · contradiction
    · rename_i hnot
      exact ⟨hnot, hstep⟩
  · intro h
    apply List.all_ok_implies_forM_ok
    intro ⟨uid, data⟩ hmem
    -- `hnot` rules out the external case of the check.
    obtain ⟨hnot, hok⟩ := h uid data hmem
    simpa [PartialSchema.wfEnv] using hok

/-- An entity reference valid against a partial schema remains valid after linking. -/
theorem entity_reference_validation_soundness
    {p c t : PartialSchema}
    {uid : EntityUID}
    {ety : EntityType}
    (hlink : link p c = .ok t)
    (hvalid : instanceOfEntityType uid ety p.validationView = true) :
    instanceOfEntityType uid ety t.validationView = true := by
  simp only [instanceOfEntityType, Bool.and_eq_true, Bool.or_eq_true] at hvalid ⊢
  obtain ⟨hty, hentity | haction⟩ := hvalid
  · refine ⟨hty, .inl ?_⟩
    simp only [EntitySchema.isValidEntityUID, validationView_find?_ets] at hentity ⊢
    cases hp : p.ets.find? uid.ty with
    | none => simp [hp] at hentity
    | some entry =>
      cases entry with
      | defined entry =>
        simpa [hp, (linker_preserves_definitions hlink).1 _ _ hp] using hentity
      | external =>
        obtain ⟨_, ht, hstd⟩ := (linker_preserves_standard_entities hlink).1 _ _ hp rfl
        simpa [ht] using PartialEntitySchemaEntry.validationView_isValidEntityEID hstd uid.eid
  · refine ⟨hty, .inr ?_⟩
    simp only [ActionSchema.contains, validationView_find?_acts, Option.isSome_map] at haction ⊢
    exact (linker_preserves_action_declarations hlink uid).mpr (.inl haction)

/-- A value valid against a partial schema remains valid after linking. -/
theorem value_validation_soundness
    {p c t : PartialSchema}
    {v : Value}
    {ty : CedarType}
    (hlink : link p c = .ok t)
    (hvalid : instanceOfType v ty p.validationView = true) :
    instanceOfType v ty t.validationView = true :=
  Cedar.Thm.instanceOfType_mono (fun _ _ => entity_reference_validation_soundness hlink) v ty hvalid

/--
Linking keeps every request type of a well-formed partial schema: each request
environment of its validation view has a counterpart in the result's.
-/
theorem request_environment_soundness
    {p c t : PartialSchema}
    {env : TypeEnv}
    (hp : p.WellFormed)
    (hlink : link p c = .ok t)
    (henv : env ∈ p.validationView.environments) :
    { ets := t.validationView.ets, acts := t.validationView.acts, reqty := env.reqty } ∈
      t.validationView.environments := by
  obtain ⟨ets, acts, ⟨principal, action, resource, context⟩⟩ := env
  obtain ⟨-, -, entry, hmem, hprincipal, hresource, hcontext⟩ := Cedar.Thm.mem_environments henv
  dsimp only at hmem hprincipal hresource hcontext ⊢
  have hacts : Map.WellFormed p.validationView.acts := Map.mapOnValues_wf.mp hp.actsMap
  have hfind := (Map.in_list_iff_find?_some hacts).mp hmem
  rw [validationView_find?_acts, Option.map_eq_some_iff] at hfind
  obtain ⟨pa, hpa, rfl⟩ := hfind
  cases pa with
  | external => exact (Set.not_mem_empty _ hprincipal).elim
  | defined e =>
    -- The action applies to a principal, so `p` defines it, and the link keeps the definition.
    have hte := (linker_preserves_definitions hlink).2.2.1 _ _ hpa
    simp only [PartialActionSchemaEntry.validationView] at hprincipal hresource hcontext
    apply Cedar.Thm.environment_some_mem_environments (principal := principal)
      (resource := resource) (action := action)
    simp [Schema.environment?, validationView_find?_acts, hte,
      PartialActionSchemaEntry.validationView, Set.contains_prop_bool_equiv.mpr hprincipal,
      Set.contains_prop_bool_equiv.mpr hresource, hcontext]

---- Major Validation results ---

/-- Entities valid against a partial schema remain valid after linking. -/
theorem entity_validation_soundness
    {p c t : PartialSchema}
    {entities : Entities}
    (hlink : link p c = .ok t)
    (hvalid : p.validateEntities entities = .ok ()) :
    t.validateEntities entities = .ok () := by
  refine PartialSchema.validateEntities_ok_iff.mpr fun uid data hmem => ?_
  obtain ⟨hnot, hstep⟩ := PartialSchema.validateEntities_ok_iff.mp hvalid uid data hmem
  cases hpe : p.ets.find? uid.ty with
  | some pe =>
    cases pe with
    | external ancestors => exact absurd hpe (hnot ancestors)
    | defined entry =>
      -- Linking keeps the definition of the entity's type.
      have hte := (linker_preserves_definitions hlink).1 _ _ hpe
      refine ⟨by simp [hte], ?_⟩
      simp only [instanceOfSchema.instanceOfSchemaEntry, PartialSchema.wfEnv,
        validationView_find?_ets, hpe, hte, Option.map_some,
        PartialEntitySchemaEntry.validationView] at hstep ⊢
      exact Cedar.Thm.instanceOfEntitySchemaEntry_mono hstep fun _ _ =>
        entity_reference_validation_soundness hlink
  | none =>
    -- The entity is an action of `p`; linking keeps it an action with the same ancestors.
    simp only [instanceOfSchema.instanceOfSchemaEntry, PartialSchema.wfEnv,
      validationView_find?_ets, hpe, Option.map_none] at hstep
    obtain ⟨_, hfind⟩ := Cedar.Thm.instanceOfActionSchemaEntry_find? hstep
    obtain ⟨_, hfind', _⟩ := link_validationView_acts hlink hfind
    have hte : t.ets.find? uid.ty = none := by
      have haction : t.acts.contains uid := by
        simpa [Map.contains, validationView_find?_acts] using congrArg Option.isSome hfind'
      simpa [Map.contains] using linker_action_types_not_entity_types hlink haction
    refine ⟨by simp [hte], ?_⟩
    simp only [instanceOfSchema.instanceOfSchemaEntry, PartialSchema.wfEnv,
      validationView_find?_ets, hte, Option.map_none]
    exact Cedar.Thm.instanceOfActionSchemaEntry_mono hstep fun _ => link_validationView_acts hlink

/-- Requests valid against a partial schema remain valid after linking. -/
theorem request_validation_soundness
    {p c t : PartialSchema}
    {request : Request}
    (hp : p.WellFormed)
    (hc : c.WellFormed)
    (hlink : link p c = .ok t)
    (hvalid : p.validateRequest request = .ok ()) :
    t.validateRequest request = .ok () := by
  unfold PartialSchema.validateRequest validateRequest at hvalid ⊢
  split at hvalid <;> try contradiction
  rename_i hany
  obtain ⟨env, henv, hmatch⟩ := List.any_eq_true.mp hany
  obtain ⟨hets, hacts, -⟩ := Cedar.Thm.mem_environments henv
  -- The request matches the same request type against the linked schema.
  have hschema : env.schema = p.validationView := by simp [TypeEnv.schema, hets, hacts]
  simp only [requestMatchesEnvironment, instanceOfRequestType, Bool.and_eq_true, hschema]
    at hmatch
  obtain ⟨⟨⟨hprincipal, haction⟩, hresource⟩, hcontext⟩ := hmatch
  have hmatch : requestMatchesEnvironment
      { ets := t.validationView.ets, acts := t.validationView.acts, reqty := env.reqty }
      request = true := by
    simp only [requestMatchesEnvironment, instanceOfRequestType, Bool.and_eq_true]
    exact ⟨⟨⟨entity_reference_validation_soundness hlink hprincipal, haction⟩,
      entity_reference_validation_soundness hlink hresource⟩,
      value_validation_soundness hlink hcontext⟩
  have hany : (t.validationView.environments.any (requestMatchesEnvironment · request)) = true :=
    List.any_eq_true.mpr ⟨_, request_environment_soundness hp hlink henv, hmatch⟩
  rw [ite_eq_left hany]

/--
Entities valid against every complete linking extension are valid against the
partial schema.
-/
theorem entity_validation_completeness
    {p : PartialSchema}
    {entities : Entities}
    (hp : p.WellFormed)
    (hvalid : ∀ c t,
      c.WellFormed →
      link p c = .ok t →
      t.asSchema?.isSome = true →
      t.validateEntities entities = .ok ()) :
    p.validateEntities entities = .ok () := by
  -- `p` links into its validation view, and into its completion with `requiredAttr`.
  have hvalidView :
      (p.validationView : PartialSchema).validateEntities entities = .ok () := by
    obtain ⟨c, hc, hlink⟩ := linker_completion_validationView hp
    exact hvalid c _ hc hlink (by rw [toPartialSchema_asSchema?]; rfl)
  have hvalidRequired :
      (p.completeWith requiredAttr : PartialSchema).validateEntities entities = .ok () := by
    obtain ⟨c, hc, hlink⟩ := linker_completion hp requiredAttr_wf requiredAttr_lifted
    exact hvalid c _ hc hlink (by rw [toPartialSchema_asSchema?]; rfl)
  refine PartialSchema.validateEntities_ok_iff.mpr fun uid data hmem => ?_
  have hview := (PartialSchema.validateEntities_ok_iff.mp hvalidView uid data hmem).2
  have hrequired := (PartialSchema.validateEntities_ok_iff.mp hvalidRequired uid data hmem).2
  rw [toPartialSchema_wfEnv] at hview hrequired
  refine ⟨fun ancestors hexternal => ?_, hview⟩
  -- An entity of external type has no attributes in the validation view, but has the attribute
  -- of `requiredAttr` in the completion with it.
  have hempty := Cedar.Thm.instanceOfSchemaEntry_attrs hview
    (entry := .standard { ancestors, attrs := Map.empty, tags := none })
    (by simp [validationView_find?_ets, hexternal, PartialEntitySchemaEntry.validationView])
  have hattr := Cedar.Thm.instanceOfSchemaEntry_attrs hrequired
    (entry := .standard { ancestors, attrs := requiredAttr, tags := none })
    (by simp [completeWith_ets_find?, hexternal, PartialEntitySchemaEntry.completeWith])
  exact Map.not_contains_of_empty _ (Cedar.Thm.instanceOfType_record_contains hempty
    (Cedar.Thm.instanceOfType_record_required hattr requiredAttr_find?))

/--
Requests valid against every complete linking extension are valid against the
partial schema.
-/
theorem request_validation_completeness
    {p : PartialSchema}
    {request : Request}
    (hp : p.WellFormed)
    (hvalid : ∀ c t,
      c.WellFormed →
      link p c = .ok t →
      t.asSchema?.isSome = true →
      t.validateRequest request = .ok ()) :
    p.validateRequest request = .ok () := by
  -- `p` links into its validation view, against which it validates requests.
  obtain ⟨c, hc, hlink⟩ := linker_completion_validationView hp
  have h := hvalid c _ hc hlink (by rw [toPartialSchema_asSchema?]; rfl)
  rwa [PartialSchema.validateRequest, toPartialSchema_validationView] at h

/-- At a complete link, request validation agrees exactly. -/
theorem complete_request_validation_agreement
    {p c t : PartialSchema}
    {schema : Schema}
    {request : Request}
    (hp : p.WellFormed)
    (hc : c.WellFormed)
    (hlink : link p c = .ok t)
    (hcomplete : t.asSchema? = some schema) :
    t.validateRequest request = validateRequest schema request := by
  rw [PartialSchema.validateRequest, validationView_eq_of_asSchema? hcomplete]

/--
At a complete link, partial entity validation implies complete validation after
adding the canonical entity for every action.
-/
theorem complete_entity_validation_agreement
    {p c t : PartialSchema}
    {schema : Schema}
    {entities : Entities}
    (hp : p.WellFormed)
    (hc : c.WellFormed)
    (hlink : link p c = .ok t)
    (hcomplete : t.asSchema? = some schema)
    (hvalid : t.validateEntities entities = .ok ()) :
    validateEntities schema
      (entities ++ schema.acts.mapOnValues actionSchemaEntryToEntityData) = .ok () := by
  have hview := validationView_eq_of_asSchema? hcomplete
  -- Every environment of `schema` is well-formed, since `schema` passes the well-formedness check.
  have hschema := linker_completed_schema_well_formed hp hc hlink hcomplete
  unfold validateEntities
  apply List.all_ok_implies_forM_ok
  intro env henv
  have hwf := Cedar.Thm.env_validate_well_formed_is_sound
    (List.forM_ok_implies_all_ok' hschema env henv)
  obtain ⟨hets, hacts, -⟩ := Cedar.Thm.mem_environments henv
  unfold entitiesMatchEnvironment instanceOfSchema
  rw [List.all_ok_implies_forM_ok _ _ ?entities, List.all_ok_implies_forM_ok _ _ ?actions]
  · rfl
  case entities =>
    intro ⟨uid, data⟩ hmem
    rcases List.mem_append.mp (Map.mem_make_mem_list hmem) with hmem | hmem
    · -- `t` validates the entity in an environment with the maps of `schema`.
      rw [Cedar.Thm.instanceOfSchemaEntry_eq (env₂ := t.wfEnv)
        (by simp [PartialSchema.wfEnv, hview, hets]) (by simp [PartialSchema.wfEnv, hview, hacts])]
      exact (PartialSchema.validateEntities_ok_iff.mp hvalid uid data hmem).2
    · -- The entity of an action is valid in a well-formed environment.
      obtain ⟨entry, rfl, hentry⟩ := Map.in_mapOnValues_in_toList' hmem
      exact Cedar.Thm.instanceOfSchemaEntry_actionEntity hwf (hacts ▸ hentry)
  case actions =>
    -- The added entities include every action.
    intro ⟨uid, _⟩ hmem
    have haction : Map.contains schema.acts uid := hacts ▸ Map.in_list_implies_contains hmem
    simp [instanceOfSchema.actionExists, Map.contains_append, haction]

end Cedar.Validation
