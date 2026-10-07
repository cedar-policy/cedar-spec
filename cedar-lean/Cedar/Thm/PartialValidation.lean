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

import Cedar.Thm.Linker

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

---- Helpers ---

/-- A standard or external entity type accepts every entity id in the validation view. -/
private theorem isStandard_isValidEntityEID
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

/-- The validation view keeps an action's ancestors. -/
private theorem PartialActionSchemaEntry.validationView_ancestors
    (entry : PartialActionSchemaEntry) :
    entry.validationView.ancestors = entry.ancestors := by
  cases entry <;> rfl

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

/-- `instanceOfType` depends on its schema only through `instanceOfEntityType`. -/
private theorem instanceOfType_mono {s₁ s₂ : Schema}
    (hmono : ∀ e ety, instanceOfEntityType e ety s₁ = true →
      instanceOfEntityType e ety s₂ = true)
    (v : Value) (ty : CedarType) (h : instanceOfType v ty s₁ = true) :
    instanceOfType v ty s₂ = true := by
  suffices hsize : ∀ n (v : Value) (ty : CedarType), sizeOf v < n →
      instanceOfType v ty s₁ = true → instanceOfType v ty s₂ = true from
    hsize (sizeOf v + 1) v ty (Nat.lt_succ_self _) h
  intro n
  induction n with
  | zero => intro _ _ hlt; omega
  | succ n ih =>
    intro v ty hlt h
    cases v with
    | prim p =>
      cases p with
      | entityUID e =>
        cases ty
        case entity ety =>
          unfold instanceOfType at h ⊢
          exact hmono e ety h
        all_goals unfold instanceOfType at h ⊢; exact h
      | _ => cases ty <;> (unfold instanceOfType at h ⊢; exact h)
    | set s =>
      cases ty
      case set ty =>
        unfold instanceOfType at h ⊢
        rw [Set.all₁_eq_all (f := (instanceOfType · ty s₁))] at h
        rw [Set.all₁_eq_all (f := (instanceOfType · ty s₂))]
        rw [Set.all_eq_true] at h ⊢
        intro x hx
        apply ih x ty _ (h x hx)
        have := Set.sizeOf_lt_of_mem hx
        simp only [Value.set.sizeOf_spec] at hlt
        omega
      all_goals unfold instanceOfType at h ⊢; exact h
    | record r =>
      cases ty
      case record rty =>
        unfold instanceOfType at h ⊢
        simp only [Bool.and_eq_true] at h ⊢
        obtain ⟨⟨hkeys, hvals⟩, hreq⟩ := h
        refine ⟨⟨hkeys, ?_⟩, hreq⟩
        rw [List.all_eq_true] at hvals ⊢
        intro ⟨⟨k, v⟩, hv⟩ hmem
        have hval := hvals ⟨⟨k, v⟩, hv⟩ hmem
        simp only at hval ⊢
        cases hq : rty.find? k with
        | none => rfl
        | some qty =>
          simp only [hq] at hval
          apply ih v qty.getType _ hval
          have hmem' : (k, v) ∈ r.1 := List.mem_attach₂ hmem
          have hlt' := Map.sizeOf_lt_of_value hmem'
          simp only [Value.record.sizeOf_spec] at hlt
          omega
      all_goals unfold instanceOfType at h ⊢; exact h
    | ext _ => cases ty <;> (unfold instanceOfType at h ⊢; exact h)

-- The facts below unfold the nested definitions generated for `instanceOfSchema`.

/-- Entity-entry validation depends on its schema only through `instanceOfEntityType`. -/
private theorem instanceOfEntitySchemaEntry_mono {env₁ env₂ : TypeEnv}
    {uid : EntityUID} {data : EntityData} {entry : EntitySchemaEntry}
    (h : instanceOfSchema.instanceOfEntitySchemaEntry env₁ uid data entry = .ok ())
    (hmono : ∀ e ety, instanceOfEntityType e ety env₁.schema = true →
      instanceOfEntityType e ety env₂.schema = true) :
    instanceOfSchema.instanceOfEntitySchemaEntry env₂ uid data entry = .ok () := by
  simp only [instanceOfSchema.instanceOfEntitySchemaEntry] at h ⊢
  split at h <;> try contradiction
  rename_i heid
  split at h <;> try contradiction
  rename_i hattrs
  split at h <;> try contradiction
  rename_i hancestors
  split at h <;> try contradiction
  rename_i htags
  have hattrs' := instanceOfType_mono hmono _ _ hattrs
  have hancestors' : data.ancestors.all (fun ancestor =>
      entry.ancestors.contains ancestor.ty &&
      instanceOfEntityType ancestor ancestor.ty env₂.schema) = true := by
    rw [Set.all_eq_true] at hancestors ⊢
    intro ancestor hmem
    have hancestor := hancestors ancestor hmem
    simp only [Bool.and_eq_true] at hancestor ⊢
    exact ⟨hancestor.1, hmono _ _ hancestor.2⟩
  have htags' : instanceOfSchema.instanceOfEntityTags env₂ data entry = true := by
    simp only [instanceOfSchema.instanceOfEntityTags] at htags ⊢
    cases htty : entry.tags? with
    | none => simpa [htty] using htags
    | some tty =>
      simp only [htty, List.all_eq_true] at htags ⊢
      exact fun value hvalue => instanceOfType_mono hmono _ _ (htags value hvalue)
  simp [heid, hattrs', hancestors', htags']

/-- Action-entry validation depends on its schema only through the action's ancestors. -/
private theorem instanceOfActionSchemaEntry_mono {env₁ env₂ : TypeEnv}
    {uid : EntityUID} {data : EntityData}
    (h : instanceOfSchema.instanceOfActionSchemaEntry env₁ uid data = .ok ())
    (hacts : ∀ entry, env₁.acts.find? uid = some entry →
      ∃ entry', env₂.acts.find? uid = some entry' ∧ entry'.ancestors = entry.ancestors) :
    instanceOfSchema.instanceOfActionSchemaEntry env₂ uid data = .ok () := by
  simp only [instanceOfSchema.instanceOfActionSchemaEntry] at h ⊢
  split at h <;> try contradiction
  rename_i hattrs
  split at h <;> try contradiction
  rename_i htags
  split at h
  · rename_i entry hentry
    split at h <;> try contradiction
    rename_i hancestors
    obtain ⟨_, hentry', heq⟩ := hacts entry hentry
    simp only [beq_iff_eq] at hancestors
    simp [hattrs, htags, hentry', heq, hancestors]
  · contradiction

/-- A valid action entity is an action of the schema. -/
private theorem instanceOfActionSchemaEntry_find? {env : TypeEnv}
    {uid : EntityUID} {data : EntityData}
    (h : instanceOfSchema.instanceOfActionSchemaEntry env uid data = .ok ()) :
    ∃ entry, env.acts.find? uid = some entry := by
  simp only [instanceOfSchema.instanceOfActionSchemaEntry] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  · rename_i entry hentry
    exact ⟨entry, hentry⟩
  · contradiction

---- Minor Validation Results ---

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
        simpa [ht] using isStandard_isValidEntityEID hstd uid.eid
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
  instanceOfType_mono (fun _ _ => entity_reference_validation_soundness hlink) v ty hvalid

---- Major Validation results ---

/-- Entities valid against a partial schema remain valid after linking. -/
theorem entity_validation_soundness
    {p c t : PartialSchema}
    {entities : Entities}
    (hlink : link p c = .ok t)
    (hvalid : p.validateEntities entities = .ok ()) :
    t.validateEntities entities = .ok () := by
  unfold PartialSchema.validateEntities at hvalid ⊢
  apply List.all_ok_implies_forM_ok
  intro ⟨uid, data⟩ hmem
  have hstep := List.forM_ok_implies_all_ok' hvalid (uid, data) hmem
  simp only at hstep ⊢
  cases hpe : p.ets.find? uid.ty with
  | some pe =>
    cases pe with
    | external => simp [hpe] at hstep
    | defined entry =>
      -- Linking keeps the definition of the entity's type.
      have hte := (linker_preserves_definitions hlink).1 _ _ hpe
      simp only [hpe, hte, instanceOfSchema.instanceOfSchemaEntry, validationView_find?_ets,
        Option.map_some, PartialEntitySchemaEntry.validationView] at hstep ⊢
      exact instanceOfEntitySchemaEntry_mono hstep fun _ _ =>
        entity_reference_validation_soundness hlink
  | none =>
    -- The entity is an action of `p`; linking keeps it an action with the same ancestors.
    simp only [hpe, instanceOfSchema.instanceOfSchemaEntry, validationView_find?_ets,
      Option.map_none] at hstep
    obtain ⟨_, hfind⟩ := instanceOfActionSchemaEntry_find? hstep
    obtain ⟨_, hfind', _⟩ := link_validationView_acts hlink hfind
    have hte : t.ets.find? uid.ty = none := by
      have haction : t.acts.contains uid := by
        simpa [Map.contains, validationView_find?_acts] using congrArg Option.isSome hfind'
      simpa [Map.contains] using linker_action_types_not_entity_types hlink haction
    simp only [hte, instanceOfSchema.instanceOfSchemaEntry, validationView_find?_ets,
      Option.map_none]
    exact instanceOfActionSchemaEntry_mono hstep fun _ => link_validationView_acts hlink

/-- Requests valid against a partial schema remain valid after linking. -/
theorem request_validation_soundness
    {p c t : PartialSchema}
    {request : Request}
    (hlink : link p c = .ok t)
    (hvalid : p.validateRequest request = .ok ()) :
    t.validateRequest request = .ok () := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Cedar.Validation
