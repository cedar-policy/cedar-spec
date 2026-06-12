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

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Slice.ValidationPolicySlice
import Cedar.Thm.Validation.TypeOfCongruence
import Cedar.Thm.Data

/-!
This file proves environment membership lemmas used by the validation policy
slice soundness proof. It also provides a reusable helper for constructing
`TypeEnvAgreement` from `IncrementallyRevalidatable` schemas.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.Slice

/--
Every environment in `schema.environments` has `ets = schema.ets` and `acts = schema.acts`.
-/
theorem env_mem_environments_schema {schema : Schema} {env : TypeEnv}
    (henv : env ∈ schema.environments) :
    env.ets = schema.ets ∧ env.acts = schema.acts := by
  simp only [Schema.environments, List.mem_map] at henv
  obtain ⟨_, _, henv_eq⟩ := henv
  exact ⟨congrArg TypeEnv.ets henv_eq.symm, congrArg TypeEnv.acts henv_eq.symm⟩

/--
The action of every environment's reqty is contained in the schema's action map.
-/
theorem env_mem_environments_action_contained {schema : Schema} {env : TypeEnv}
    (henv : env ∈ schema.environments) :
    schema.acts.contains env.reqty.action := by
  simp only [Schema.environments, List.mem_map, List.mem_flatMap] at henv
  obtain ⟨rt, ⟨⟨action, entry⟩, hmem_acts, hmem_rt⟩, henv_eq⟩ := henv
  have hreqty : env.reqty = rt := congrArg TypeEnv.reqty henv_eq.symm
  rw [hreqty]
  simp only [ActionSchemaEntry.requestTypes, List.mem_map] at hmem_rt
  obtain ⟨⟨p, r⟩, _, hrt_eq⟩ := hmem_rt
  have haction : rt.action = action := congrArg RequestType.action hrt_eq.symm
  rw [haction]
  exact Map.in_list_implies_contains hmem_acts

/--
If an env is in schema₂.environments and the action entry is the same in both schemas
(same `find?`), then an env with the same reqty exists in schema₁.environments.
-/
theorem env_in_other_schema_environments
    {schema₁ schema₂ : Schema} {env₂ : TypeEnv}
    (henv₂ : env₂ ∈ schema₂.environments)
    (hfind_eq : schema₁.acts.find? env₂.reqty.action = schema₂.acts.find? env₂.reqty.action)
    (hwf₂ : Map.WellFormed schema₂.acts) :
    ∃ env₁ ∈ schema₁.environments, env₁.reqty = env₂.reqty := by
  simp only [Schema.environments, List.mem_map, List.mem_flatMap] at henv₂ ⊢
  obtain ⟨rt₂, ⟨⟨action₂, entry₂⟩, hmem_acts₂, hmem_rt₂⟩, henv₂_eq⟩ := henv₂
  have hreqty₂ : env₂.reqty = rt₂ := congrArg TypeEnv.reqty henv₂_eq.symm
  simp only [ActionSchemaEntry.requestTypes, List.mem_map] at hmem_rt₂
  obtain ⟨⟨p, r⟩, hpr_mem, hrt₂_eq⟩ := hmem_rt₂
  have haction₂ : rt₂.action = action₂ := congrArg RequestType.action hrt₂_eq.symm
  have henv_action : env₂.reqty.action = action₂ := by rw [hreqty₂, haction₂]
  -- From (action₂, entry₂) ∈ schema₂.acts.toList and WellFormed:
  have hfind₂ : schema₂.acts.find? action₂ = some entry₂ :=
    (Map.in_list_iff_find?_some hwf₂).mp hmem_acts₂
  -- Transfer to schema₁
  have hfind₁ : schema₁.acts.find? action₂ = some entry₂ := by
    have h := hfind_eq; rw [henv_action] at h; rw [h, hfind₂]
  -- So (action₂, entry₂) ∈ schema₁.acts.toList
  have hmem_acts₁ : (action₂, entry₂) ∈ schema₁.acts.toList :=
    Map.find?_mem_toList hfind₁
  -- Same reqty in schema₁.environments
  -- The env₁ we construct: { ets := schema₁.ets, acts := schema₁.acts, reqty := rt₂ }
  refine ⟨{ ets := schema₁.ets, acts := schema₁.acts, reqty := rt₂ }, ?_, ?_⟩
  · -- Show it's in schema₁.environments (goal is existential form from simp)
    exact ⟨rt₂, ⟨⟨action₂, entry₂⟩, hmem_acts₁, by
      simp only [ActionSchemaEntry.requestTypes, List.mem_map]
      exact ⟨⟨p, r⟩, hpr_mem, hrt₂_eq⟩⟩, rfl⟩
  · -- Show reqty matches
    exact hreqty₂.symm

private theorem list_product_mem {a : α} {b : β} {l1 : List α} {l2 : List β}
    (h : (a, b) ∈ l1.product l2) : a ∈ l1 ∧ b ∈ l2 := by
  simp [List.product, List.mem_flatMap, List.mem_map] at h; exact h

private theorem list_mem_product {a : α} {b : β} {l1 : List α} {l2 : List β}
    (h1 : a ∈ l1) (h2 : b ∈ l2) : (a, b) ∈ l1.product l2 := by
  simp [List.product, List.mem_flatMap, List.mem_map]; exact ⟨h1, h2⟩

/--
Subset variant: if an env is in schema₂.environments and the action's appliesTo
in schema₁ *contains* that of schema₂ (and context matches), then a corresponding
env exists in schema₁. This handles the appliesTo truncation case.
-/
theorem env_in_other_schema_environments_subset
    {schema₁ schema₂ : Schema} {env₂ : TypeEnv}
    (henv₂ : env₂ ∈ schema₂.environments)
    {entry₁ entry₂ : ActionSchemaEntry}
    (hfind₁ : schema₁.acts.find? env₂.reqty.action = some entry₁)
    (hfind₂ : schema₂.acts.find? env₂.reqty.action = some entry₂)
    (hctx : entry₁.context = entry₂.context)
    (hprincipal : entry₂.appliesToPrincipal ⊆ entry₁.appliesToPrincipal)
    (hresource : entry₂.appliesToResource ⊆ entry₁.appliesToResource)
    (hwf₂ : Map.WellFormed schema₂.acts) :
    ∃ env₁ ∈ schema₁.environments, env₁.reqty = env₂.reqty := by
  simp only [Schema.environments, List.mem_map, List.mem_flatMap] at henv₂ ⊢
  obtain ⟨rt₂, ⟨⟨action₂, entry₂'⟩, hmem_acts₂, hmem_rt₂⟩, henv₂_eq⟩ := henv₂
  have hreqty₂ : env₂.reqty = rt₂ := congrArg TypeEnv.reqty henv₂_eq.symm
  simp only [ActionSchemaEntry.requestTypes, List.mem_map] at hmem_rt₂
  obtain ⟨⟨p, r⟩, hpr_mem, hrt₂_eq⟩ := hmem_rt₂
  have haction₂ : rt₂.action = action₂ := congrArg RequestType.action hrt₂_eq.symm
  have henv_action : env₂.reqty.action = action₂ := by rw [hreqty₂, haction₂]
  have hentry₂_eq : entry₂' = entry₂ := by
    have hfind₂' := (Map.in_list_iff_find?_some hwf₂).mp hmem_acts₂
    exact Option.some.inj ((henv_action ▸ hfind₂) ▸ hfind₂').symm
  subst hentry₂_eq
  have ⟨hp, hr⟩ := list_product_mem hpr_mem
  have hp₁ := Set.mem_subset_mem hp hprincipal
  have hr₁ := Set.mem_subset_mem hr hresource
  have hfind₁' : schema₁.acts.find? action₂ = some entry₁ := henv_action ▸ hfind₁
  refine ⟨{ ets := schema₁.ets, acts := schema₁.acts, reqty := rt₂ }, ?_, ?_⟩
  · exact ⟨rt₂, ⟨⟨action₂, entry₁⟩, Map.find?_mem_toList hfind₁', by
      simp only [ActionSchemaEntry.requestTypes, List.mem_map]
      exact ⟨⟨p, r⟩, list_mem_product hp₁ hr₁, by rw [← hrt₂_eq, hctx]⟩⟩, rfl⟩
  · exact hreqty₂.symm

/--
For actions not in `computeActionChanges`: same context and new appliesTo ⊆ old.
-/
theorem computeActionChanges_not_in_gives_subset
    {oldSchema newSchema : Schema} {action : EntityUID}
    {oldEntry newEntry : ActionSchemaEntry}
    (hnotinchanges : ¬ (computeActionChanges oldSchema newSchema).any (fun c => c.action == action) = true)
    (hfind_old : oldSchema.acts.find? action = some oldEntry)
    (hfind_new : newSchema.acts.find? action = some newEntry) :
    oldEntry.context = newEntry.context ∧
    newEntry.appliesToPrincipal.subset oldEntry.appliesToPrincipal ∧
    newEntry.appliesToResource.subset oldEntry.appliesToResource := by
  have hmem_new := Map.find?_mem_toList hfind_new
  have hctx : oldEntry.context = newEntry.context := by
    by_contra h
    have hne : (oldEntry.context != newEntry.context) = true := by simp [bne, h]
    have hmem_out : ActionChange.contextChanged action ∈ computeActionChanges oldSchema newSchema :=
      List.mem_filterMap.mpr ⟨(action, newEntry), hmem_new, by simp [hfind_old, hne]⟩
    exact absurd (List.any_eq_true.mpr ⟨_, hmem_out, by simp [ActionChange.action]⟩) hnotinchanges
  have hprincipal : newEntry.appliesToPrincipal.subset oldEntry.appliesToPrincipal := by
    by_contra h
    have hf := Bool.eq_false_iff.mpr h
    have hne : (!(newEntry.appliesToPrincipal.subset oldEntry.appliesToPrincipal) ||
                !(newEntry.appliesToResource.subset oldEntry.appliesToResource)) = true := by simp [hf]
    have hctx_bne : (oldEntry.context != newEntry.context) = false := by simp [bne, hctx]
    have hmem_out : ActionChange.appliesToExtended action ∈ computeActionChanges oldSchema newSchema := by
      simp only [computeActionChanges, List.mem_filterMap]
      refine ⟨(action, newEntry), hmem_new, ?_⟩
      simp only [hfind_old]; simp_all [bne]
    exact absurd (List.any_eq_true.mpr ⟨_, hmem_out, by simp [ActionChange.action]⟩) hnotinchanges
  have hresource : newEntry.appliesToResource.subset oldEntry.appliesToResource := by
    by_contra h
    have hf := Bool.eq_false_iff.mpr h
    have hne : (!(newEntry.appliesToPrincipal.subset oldEntry.appliesToPrincipal) ||
                !(newEntry.appliesToResource.subset oldEntry.appliesToResource)) = true := by simp [hf]
    have hctx_bne : (oldEntry.context != newEntry.context) = false := by simp [bne, hctx]
    have hmem_out : ActionChange.appliesToExtended action ∈ computeActionChanges oldSchema newSchema := by
      simp only [computeActionChanges, List.mem_filterMap]
      refine ⟨(action, newEntry), hmem_new, ?_⟩
      simp only [hfind_old]; simp_all [bne]
    exact absurd (List.any_eq_true.mpr ⟨_, hmem_out, by simp [ActionChange.action]⟩) hnotinchanges
  exact ⟨hctx, hprincipal, hresource⟩

/--
Specifies the relationship between two schemas that permits incremental
revalidation. Corresponds to `requiresFullRevalidation old new = false`.
-/
structure IncrementallyRevalidatable (schema₁ schema₂ : Schema) : Prop where
  ets_fwd : ∀ ety entry, schema₁.ets.find? ety = some entry → schema₂.ets.find? ety = some entry
  ets_disjoint : ∀ uid, schema₂.acts.contains uid = true → ¬ schema₂.ets.contains uid.ty
  acts_contains_fwd : ∀ action : EntityUID,
    schema₁.acts.contains action = true → schema₂.acts.contains action = true
  same_action_types : ∀ ety : EntityType,
    schema₁.acts.actionType? ety = schema₂.acts.actionType? ety
  same_ancestors : ∀ (action : EntityUID) (entry₁ entry₂ : ActionSchemaEntry),
    schema₁.acts.find? action = some entry₁ →
    schema₂.acts.find? action = some entry₂ →
    entry₁.ancestors = entry₂.ancestors
  same_descendentOf : ∀ uid₁ uid₂ : EntityUID,
    schema₁.acts.descendentOf uid₁ uid₂ = schema₂.acts.descendentOf uid₁ uid₂
  same_maybeDescendentOf : ∀ ety₁ ety₂ : EntityType,
    schema₁.acts.maybeDescendentOf ety₁ ety₂ = schema₂.acts.maybeDescendentOf ety₁ ety₂

/--
Construct `ActsAgreement` between two environments from different schemas when:
- Both environments' ets and acts fields are the schema ets/acts respectively
- The schemas are `IncrementallyRevalidatable`
- The environments have the same `reqty`
-/
theorem mk_envAgreement_from_schemas
    {schema₁ schema₂ : Schema} {env₁ env₂ : TypeEnv}
    (hincr : IncrementallyRevalidatable schema₁ schema₂)
    (henv₁_ets : env₁.ets = schema₁.ets)
    (henv₁_acts : env₁.acts = schema₁.acts)
    (henv₂_ets : env₂.ets = schema₂.ets)
    (henv₂_acts : env₂.acts = schema₂.acts)
    (hreqty : env₁.reqty = env₂.reqty)
    (hwf₁ : env₁.WellFormed) :
    EnvAgreement env₁ env₂ where
  reqty_eq := hreqty
  ets_fwd := fun ety entry hf => by
    rw [henv₁_ets] at hf; rw [henv₂_ets]; exact hincr.ets_fwd ety entry hf
  acts_contains_fwd := fun uid hc => by
    rw [henv₁_acts] at hc; rw [henv₂_acts]; exact hincr.acts_contains_fwd uid hc
  acts_actionType := fun ety => by rw [henv₁_acts, henv₂_acts]; exact hincr.same_action_types ety
  acts_descendentOf := fun u₁ u₂ => by rw [henv₁_acts, henv₂_acts]; exact hincr.same_descendentOf u₁ u₂
  acts_maybeDescendentOf := fun e₁ e₂ => by rw [henv₁_acts, henv₂_acts]; exact hincr.same_maybeDescendentOf e₁ e₂
  disjoint₂ := fun uid hc => by
    rw [henv₂_acts] at hc; rw [henv₂_ets]; exact hincr.ets_disjoint uid hc
  wf₁ := hwf₁

/--
Construct `ActsAgreement` between two environments from different schemas when:
- Both environments' ets and acts fields are the schema ets/acts respectively
- The schemas are `IncrementallyRevalidatable` and have the same entity schema
- The environments have the same `reqty`
Does NOT require `env₁.WellFormed`.
-/
theorem mk_actsAgreement_from_schemas
    {schema₁ schema₂ : Schema} {env₁ env₂ : TypeEnv}
    (hincr : IncrementallyRevalidatable schema₁ schema₂)
    (henv₁_ets : env₁.ets = schema₁.ets)
    (henv₁_acts : env₁.acts = schema₁.acts)
    (henv₂_ets : env₂.ets = schema₂.ets)
    (henv₂_acts : env₂.acts = schema₂.acts)
    (hreqty : env₁.reqty = env₂.reqty)
    (hets_eq : schema₁.ets = schema₂.ets) :
    ActsAgreement env₁ env₂ where
  reqty_eq := hreqty
  ets_eq := by rw [henv₁_ets, henv₂_ets, hets_eq]
  acts_contains_fwd := fun uid hc => by
    rw [henv₁_acts] at hc; rw [henv₂_acts]; exact hincr.acts_contains_fwd uid hc
  acts_actionType := fun ety => by rw [henv₁_acts, henv₂_acts]; exact hincr.same_action_types ety
  acts_descendentOf := fun u₁ u₂ => by rw [henv₁_acts, henv₂_acts]; exact hincr.same_descendentOf u₁ u₂
  acts_maybeDescendentOf := fun e₁ e₂ => by rw [henv₁_acts, henv₂_acts]; exact hincr.same_maybeDescendentOf e₁ e₂
  disjoint₂ := fun uid hc => by
    rw [henv₂_acts] at hc; rw [henv₂_ets]
    have hnotc := hincr.ets_disjoint uid hc
    simp only [EntitySchema.isValidEntityUID]
    cases hf : schema₂.ets.find? uid.ty with
    | none => rfl
    | some _ => exact absurd (by simp [EntitySchema.contains, hf]) hnotc

end Cedar.Thm
