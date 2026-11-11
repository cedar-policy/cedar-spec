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

module

public import Cedar.Thm.Validation.Relational.Request
public import Cedar.Validation.Relational.Entities
import Batteries.Data.List.Lemmas
import all Cedar.Data.Map -- unfolds `contains`, `empty`, `find`, …
import all Cedar.Data.Set -- unfolds `all`, `contains`, `elts`, …
import all Cedar.Spec.Entities -- unfolds `Entities`, `Tag`, `ancestors`, …
import all Cedar.Spec.Value -- unfolds `Attr`, `EntityType`
import all Cedar.Validation.EnvironmentValidator -- unfolds `validateWellFormed`
import all Cedar.Validation.RequestEntityValidator -- unfolds `entitiesMatchEnvironment`, `instanceOfEntityType`, `instanceOfSchema`, …
import all Cedar.Validation.Types -- unfolds `ActionSchema`, `EntitySchema`, `RecordType`, …
import all Cedar.Validation.Validator -- unfolds `environment`, `environments`

/-! # `ValidEntities` characterizes `validateEntities` -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Helpers -/

private theorem ite_ok_iff {ε : Type} {b : Bool} {x : Except ε Unit} {e : ε} :
    (if b = true then x else .error e) = .ok () ↔ b = true ∧ x = .ok () := by
  cases b <;> simp

private theorem beq_empty_iff {α β : Type} [DecidableEq α] [DecidableEq β] {m : Map α β} :
    (m == Map.empty) = true ↔ m = .mk [] := by
  simp [Map.empty]

/-! ## Standard and enumerated entities -/

theorem ancestorsAllowed_iff {ets : EntitySchema} {acts : ActionSchema} {ancTys : Set EntityType}
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup) :
    ∀ {ancs : List EntityUID}, AncestorsAllowed ets acts ancTys ancs ↔
      ancs.all (fun a => ancTys.contains a.ty && instanceOfEntityType a a.ty ⟨ets, acts⟩) = true
  | [] => ⟨fun _ => by simp, fun _ => .nil _ _ _⟩
  | ⟨ety, eid⟩ :: ancs => by
    rw [List.all_cons, Bool.and_eq_true, ← ancestorsAllowed_iff hndE hndA, Bool.and_eq_true,
      instanceOfEntityType_iff hndE hndA, ← setContains_iff_contains]
    constructor
    · intro h
      cases h with
      | cons _ _ _ hs hv hrest => exact ⟨⟨hs, rfl, hv⟩, hrest⟩
    · rintro ⟨⟨hs, -, hv⟩, hrest⟩
      exact .cons _ _ _ _ _ _ hs hv hrest

theorem tagValuesInstance_iff {ets : EntitySchema} {acts : ActionSchema} {ty : CedarType}
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup)
    (hty : TyWf ty) :
    ∀ {tags : List (Tag × Value)}, TagValuesInstance ets acts tags ty ↔
      (Map.mk tags).values.all (instanceOfType · ty ⟨ets, acts⟩) = true
  | [] => ⟨fun _ => by simp [Map.values], fun _ => .nil _ _ _⟩
  | (k, v) :: tags => by
    have ih := tagValuesInstance_iff hndE hndA hty (tags := tags)
    simp only [Map.values, Map.toList, List.map_cons, List.all_cons, Bool.and_eq_true] at ih ⊢
    rw [← ih, ← instanceOfType_iff hndE hndA v hty]
    constructor
    · intro h
      cases h with
      | cons _ _ _ _ hv hrest => exact ⟨hv, hrest⟩
    · rintro ⟨hv, hrest⟩
      exact .cons _ _ _ _ _ _ hv hrest

theorem tagsInstance_iff {env : TypeEnv} {data : EntityData} {ancTys : Set EntityType}
    {attrTys : RecordType} {tagTy : Option CedarType}
    (hndE : (env.ets.toList.map Prod.fst).Nodup) (hndA : (env.acts.toList.map Prod.fst).Nodup)
    (hty : ∀ ty, tagTy = some ty → TyWf ty) :
    TagsInstance env.ets env.acts data.tags tagTy ↔
      instanceOfSchema.instanceOfEntityTags env data (.standard ⟨ancTys, attrTys, tagTy⟩) = true := by
  obtain ⟨attrs, ancs, ⟨tags⟩⟩ := data
  simp only [instanceOfSchema.instanceOfEntityTags, EntitySchemaEntry.tags?, TypeEnv.schema]
  cases tagTy with
  | some ty =>
    simp only
    rw [← tagValuesInstance_iff hndE hndA (hty ty rfl)]
    constructor
    · intro h; cases h with | some _ _ h => exact h
    · exact fun h => .some _ _ _ _ h
  | none =>
    simp only [beq_empty_iff]
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; exact .none _ _

/-- A standard entity's schema entry is found under the entity's type. -/
theorem standard_attrs?_tags? {ets : EntitySchema} {ety : EntityType} {ancTys attrTys tagTy}
    (hndE : (ets.toList.map Prod.fst).Nodup)
    (hmc : MapContains ety (EntitySchemaEntry.standard ⟨ancTys, attrTys, tagTy⟩) ets) :
    ets.attrs? ety = some attrTys ∧ ets.tags? ety = some tagTy := by
  have hf := mapContains_find?_nodup hmc hndE
  simp [EntitySchema.attrs?, EntitySchema.tags?, hf, EntitySchemaEntry.attrs,
    EntitySchemaEntry.tags?]

theorem record_instance_empty_iff {ets : EntitySchema} {acts : ActionSchema}
    {attrs : Map Attr Value} :
    instanceOfType (.record attrs) (.record Map.empty) ⟨ets, acts⟩ = true ↔ attrs = .mk [] := by
  obtain ⟨avs⟩ := attrs
  rw [Map.empty, instanceOfType_record_iff (rty := []) (by simp)]
  constructor
  · rintro ⟨h, -⟩
    cases avs with
    | nil => rfl
    | cons p _ =>
      obtain ⟨_, hmc, _⟩ := h p (List.mem_cons_self ..)
      cases hmc
  · intro h; cases h; simp

private theorem set_all_empty_iff {α : Type} {f : α → Bool} {s : Set α}
    (hf : ∀ a, f a = false) : s.all f = true ↔ s = .mk [] := by
  obtain ⟨l⟩ := s
  cases l with
  | nil => simp [Set.all, Set.elts]
  | cons a _ => simp [Set.all, Set.elts, hf a]

/-- `InstanceOfEntitySchemaEntry` agrees with `instanceOfEntitySchemaEntry` for the entry found
    under the entity's type. -/
theorem instanceOfEntitySchemaEntry_iff {env : TypeEnv} {uid : EntityUID} {data : EntityData}
    {entry : EntitySchemaEntry} (hwf : EnvAssumptions env)
    (hmc : MapContains uid.ty entry env.ets) :
    InstanceOfEntitySchemaEntry env.ets env.acts uid data entry ↔
      instanceOfSchema.instanceOfEntitySchemaEntry env uid data entry = .ok () := by
  have hndE := hwf.ets_keys_nodup
  have hndA := hwf.acts_keys_nodup
  simp only [instanceOfSchema.instanceOfEntitySchemaEntry]
  simp only [ite_ok_iff, and_true]
  cases entry with
  | standard sentry =>
    obtain ⟨ancTys, attrTys, tagTy⟩ := sentry
    obtain ⟨hattrs, htags⟩ := standard_attrs?_tags? hndE hmc
    have hwfa : TyWf (.record attrTys) := hwf.attrs_tyWf hattrs
    have hwft : ∀ ty, tagTy = some ty → TyWf ty := by
      rintro ty rfl; exact hwf.tags_tyWf htags
    rw [← tagsInstance_iff hndE hndA hwft]
    obtain ⟨ets, acts, reqty⟩ := env
    obtain ⟨attrs, ancs, tags⟩ := data
    simp only [EntitySchemaEntry.isValidEntityEID, EntitySchemaEntry.attrs,
      EntitySchemaEntry.ancestors, true_and, Set.all, TypeEnv.schema] at *
    rw [← instanceOfType_iff hndE hndA _ hwfa, ← ancestorsAllowed_iff hndE hndA]
    constructor
    · intro h; cases h with | standard _ _ _ _ _ _ _ ha hanc ht => exact ⟨ha, hanc, ht⟩
    · rintro ⟨ha, hanc, ht⟩; exact .standard _ _ _ _ _ _ _ _ _ ha hanc ht
  | enum eids =>
    obtain ⟨ets, acts, reqty⟩ := env
    obtain ⟨attrs, ancs, tags⟩ := data
    obtain ⟨ety, eid⟩ := uid
    simp only [instanceOfSchema.instanceOfEntityTags, TypeEnv.schema,
      EntitySchemaEntry.isValidEntityEID, EntitySchemaEntry.attrs,
      EntitySchemaEntry.ancestors, EntitySchemaEntry.tags?, record_instance_empty_iff,
      beq_empty_iff, Set.empty]
    rw [set_all_empty_iff (fun a => by simp [Set.contains, Set.elts]), ← setContains_iff_contains]
    constructor
    · intro h; cases h with | enum _ _ _ hs => exact ⟨hs, rfl, rfl, rfl⟩
    · rintro ⟨hs, rfl, rfl, rfl⟩; exact .enum _ _ _ _ _ hs

/-! ## Action entities -/

/-- `InstanceOfActionSchemaEntry` agrees with `instanceOfActionSchemaEntry`. -/
theorem instanceOfActionSchemaEntry_iff {env : TypeEnv} {uid : EntityUID} {data : EntityData}
    (hndA : (env.acts.toList.map Prod.fst).Nodup) :
    InstanceOfActionSchemaEntry env.acts uid data ↔
      instanceOfSchema.instanceOfActionSchemaEntry env uid data = .ok () := by
  obtain ⟨attrs, ancs, tags⟩ := data
  simp only [instanceOfSchema.instanceOfActionSchemaEntry]
  simp only [ite_ok_iff]
  simp only [beq_empty_iff]
  constructor
  · intro h
    cases h with
    | mk entry hmc => simp [mapContains_find?_nodup hmc hndA]
  · rintro ⟨rfl, rfl, h⟩
    split at h
    · rename_i entry hf
      simp only [beq_iff_eq] at h
      split at h
      · rename_i heq; subst heq; exact .mk _ _ _ (find?_mapContains hf)
      · cases h
    · simp at h

/-- `InstanceOfSchemaEntry` agrees with `instanceOfSchemaEntry`. -/
theorem instanceOfSchemaEntry_iff {env : TypeEnv} {uid : EntityUID} {data : EntityData}
    (hwf : EnvAssumptions env) :
    InstanceOfSchemaEntry env.ets env.acts uid data ↔
      instanceOfSchema.instanceOfSchemaEntry env uid data = .ok () := by
  have hndE := hwf.ets_keys_nodup
  simp only [instanceOfSchema.instanceOfSchemaEntry]
  split
  · rename_i entry hf
    rw [← instanceOfEntitySchemaEntry_iff hwf (find?_mapContains hf)]
    constructor
    · intro h
      cases h with
      | entity entry' hmc' h =>
        rw [mapContains_find?_nodup hmc' hndE] at hf
        cases hf; exact h
      | action hn _ => rw [mapNotContainsKey_find? hn] at hf; cases hf
    · exact fun h => .entity _ _ _ _ _ (find?_mapContains hf) h
  · rename_i hf
    have hnone : env.ets.find? uid.ty = none := by
      cases h : env.ets.find? uid.ty with
      | none => rfl
      | some e => exact absurd h (hf e)
    rw [← instanceOfActionSchemaEntry_iff hwf.acts_keys_nodup]
    constructor
    · intro h
      cases h with
      | entity _ hmc' _ => rw [mapContains_find?_nodup hmc' hndE] at hnone; cases hnone
      | action _ h => exact h
    · exact fun h => .action _ _ _ _ (mapNotContainsKey_of_find?_none hnone) h

/-! ## Entity stores -/

theorem entityEntriesInstance_iff {ets : EntitySchema} {acts : ActionSchema} :
    ∀ {es : List (EntityUID × EntityData)}, EntityEntriesInstance ets acts es ↔
      ∀ p ∈ es, InstanceOfSchemaEntry ets acts p.1 p.2
  | [] => ⟨fun _ => by simp, fun _ => .nil _ _⟩
  | (uid, data) :: es => by
    rw [List.forall_mem_cons, ← entityEntriesInstance_iff]
    constructor
    · intro h; cases h with | cons _ _ _ h hrest => exact ⟨h, hrest⟩
    · rintro ⟨h, hrest⟩; exact .cons _ _ _ _ _ h hrest

theorem actionsExist_iff {entities : Entities} :
    ∀ {acs : List (EntityUID × ActionSchemaEntry)}, ActionsExist entities acs ↔
      ∀ p ∈ acs, entities.contains p.1 = true
  | [] => ⟨fun _ => by simp, fun _ => .nil _⟩
  | (uid, entry) :: acs => by
    rw [List.forall_mem_cons, ← actionsExist_iff, map_contains_iff_mapContains]
    constructor
    · intro h; cases h with | cons _ _ data _ hmc hrest => exact ⟨⟨data, hmc⟩, hrest⟩
    · rintro ⟨⟨data, hmc⟩, hrest⟩; exact .cons _ _ _ _ _ hmc hrest

/-- `InstanceOfSchema` agrees with `instanceOfSchema` on an environment satisfying
    `EnvAssumptions`. -/
theorem instanceOfSchema_iff {env : TypeEnv} {entities : Entities} (hwf : EnvAssumptions env) :
    InstanceOfSchema env.ets env.acts entities ↔ instanceOfSchema entities env = .ok () := by
  obtain ⟨es⟩ := entities
  simp only [instanceOfSchema, bind_unit_ok_iff, forM_ok_iff]
  have hents : EntityEntriesInstance env.ets env.acts es ↔
      ∀ p ∈ (Map.mk es).toList, instanceOfSchema.instanceOfSchemaEntry env p.1 p.2 = .ok () := by
    rw [entityEntriesInstance_iff]
    exact forall₂_congr fun p _ => instanceOfSchemaEntry_iff hwf
  have hacts : ActionsExist (.mk es) env.acts.toList ↔
      ∀ p ∈ env.acts.toList, instanceOfSchema.actionExists (.mk es) p.1 = .ok () := by
    rw [actionsExist_iff]
    exact forall₂_congr fun p _ => by simp [instanceOfSchema.actionExists]
  rw [← hents, ← hacts]
  constructor
  · intro h; cases h with | mk _ he ha => exact ⟨he, ha⟩
  · rintro ⟨he, ha⟩; exact .mk _ _ _ he ha

/-! ## Entity validation -/

theorem noRequestTypes_iff :
    ∀ {acs : List (EntityUID × ActionSchemaEntry)}, NoRequestTypes acs ↔
      ∀ p ∈ acs, p.2.appliesToPrincipal.toList = [] ∨ p.2.appliesToResource.toList = []
  | [] => ⟨fun _ => by simp, fun _ => .nil⟩
  | (uid, ⟨⟨ptys⟩, ⟨rtys⟩, ancs, ctx⟩) :: acs => by
    rw [List.forall_mem_cons, ← noRequestTypes_iff]
    simp only [Set.toList, Set.elts]
    constructor
    · intro h
      cases h with
      | noPrincipals _ _ _ _ _ h => exact ⟨.inl rfl, h⟩
      | noResources _ _ _ _ _ h => exact ⟨.inr rfl, h⟩
    · rintro ⟨rfl | rfl, h⟩
      · exact .noPrincipals _ _ _ _ _ h
      · exact .noResources _ _ _ _ _ h

/-- `NoRequestTypes` says the schema has no environments. -/
theorem noRequestTypes_iff_environments_nil {schema : Schema} :
    NoRequestTypes schema.acts.toList ↔ schema.environments = [] := by
  rw [noRequestTypes_iff, List.eq_nil_iff_forall_not_mem]
  simp only [mem_environments_iff, not_exists, not_and]
  constructor
  · intro h env act entry p r hmem hp hr _
    rcases h _ hmem with h | h
    · rw [h] at hp; cases hp
    · rw [h] at hr; cases hr
  · intro h p hp
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨p', hp'⟩ := List.exists_mem_of_ne_nil _ hne.1
    obtain ⟨r', hr'⟩ := List.exists_mem_of_ne_nil _ hne.2
    exact h _ p.1 p.2 p' r' hp hp' hr' rfl

/-- **Entity validation.** On a schema whose environments satisfy `EnvAssumptions`,
    `validateEntities` accepts an entity store exactly when `ValidEntities` holds for it. -/
theorem validateEntities_iff {schema : Schema} {entities : Entities}
    (hwf : ∀ env ∈ schema.environments, EnvAssumptions env) :
    validateEntities schema entities = .ok () ↔ ValidEntities schema entities := by
  have hval : ValidEntities schema entities ↔
      NoRequestTypes schema.acts.toList ∨ InstanceOfSchema schema.ets schema.acts entities := by
    obtain ⟨ets, acts⟩ := schema
    constructor
    · intro h
      cases h with
      | noEnvironments _ _ _ h => exact .inl h
      | «instance» _ _ _ h => exact .inr h
    · rintro (h | h)
      · exact .noEnvironments _ _ _ h
      · exact .instance _ _ _ h
  rw [hval, noRequestTypes_iff_environments_nil, validateEntities, forM_ok_iff]
  cases henvs : schema.environments with
  | nil => simp
  | cons env₀ envs =>
    have hmem : ∀ env ∈ schema.environments,
        (instanceOfSchema entities env = .ok () ↔
          InstanceOfSchema schema.ets schema.acts entities) := by
      intro env henv
      obtain ⟨hets, hacts⟩ := mem_environments henv
      rw [← instanceOfSchema_iff (hwf env henv), hets, hacts]
    rw [henvs] at hmem
    simp only [reduceCtorEq, false_or, entitiesMatchEnvironment]
    constructor
    · intro h; exact (hmem env₀ (List.mem_cons_self ..)).mp (h env₀ (List.mem_cons_self ..))
    · intro h env henv; exact (hmem env henv).mpr h

/-- `validateEntities_iff` on a schema that passes Cedar's schema well-formedness check. -/
theorem validateEntities_iff_of_validateWellFormed {schema : Schema} {entities : Entities}
    (hwf : schema.validateWellFormed = .ok ()) :
    validateEntities schema entities = .ok () ↔ ValidEntities schema entities :=
  validateEntities_iff (envAssumptions_of_validateWellFormed hwf)

end Cedar.Validation.Relational
