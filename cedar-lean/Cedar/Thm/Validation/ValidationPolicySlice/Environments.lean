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
import Cedar.Thm.Validation.ValidationPolicySlice.TypeOfCongr
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

/--
Specifies the relationship between two schemas that permits incremental
revalidation. Corresponds to `requiresFullRevalidation old new = false`.
-/
structure IncrementallyRevalidatable (schema₁ schema₂ : Schema) : Prop where
  ets_eq : schema₁.ets = schema₂.ets
  same_actions : ∀ action : EntityUID,
    schema₁.acts.contains action = schema₂.acts.contains action
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
Construct `TypeEnvAgreement` between two environments from different schemas when:
- Both environments' ets and acts fields are the schema ets/acts respectively
- The schemas are `IncrementallyRevalidatable`
- The environments have the same `reqty`
-/
theorem mk_typeEnvAgreement_from_schemas
    {schema₁ schema₂ : Schema} {env₁ env₂ : TypeEnv}
    (hincr : IncrementallyRevalidatable schema₁ schema₂)
    (henv₁_ets : env₁.ets = schema₁.ets)
    (henv₁_acts : env₁.acts = schema₁.acts)
    (henv₂_ets : env₂.ets = schema₂.ets)
    (henv₂_acts : env₂.acts = schema₂.acts)
    (hreqty : env₁.reqty = env₂.reqty) :
    TypeEnvAgreement env₁ env₂ where
  ets_eq := by rw [henv₁_ets, henv₂_ets, hincr.ets_eq]
  reqty_eq := hreqty
  acts_contains := fun uid => by rw [henv₁_acts, henv₂_acts]; exact hincr.same_actions uid
  acts_actionType := fun ety => by rw [henv₁_acts, henv₂_acts]; exact hincr.same_action_types ety
  acts_descendentOf := fun u₁ u₂ => by rw [henv₁_acts, henv₂_acts]; exact hincr.same_descendentOf u₁ u₂
  acts_maybeDescendentOf := fun e₁ e₂ => by rw [henv₁_acts, henv₂_acts]; exact hincr.same_maybeDescendentOf e₁ e₂

end Cedar.Thm
