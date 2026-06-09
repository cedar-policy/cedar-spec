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
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Data
import Cedar.Thm.Validation.SubstituteAction
import Cedar.Thm.WellTyped.Expr.Definition
import Cedar.Thm.WellTyped.Expr.Typechecking

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- For a single expression, evaluates to a boolean value (or appropriate error) -/
def EvaluatesToBool (expr : Expr) (request : Request) (entities : Entities) : Prop :=
  ∃ (b : Bool), EvaluatesTo expr request entities b

/-- Every policy as an expression evaluates to a boolean value or appropriate error -/
def AllEvaluateToBool (policies : Policies) (request : Request) (entities : Entities) : Prop :=
  ∀ policy ∈ policies, EvaluatesToBool policy.toExpr request entities

def InstanceOfWellFormedSchema (schema : Schema) (request : Request) (entities : Entities) : Prop :=
  ∃ env ∈ schema.environments,
  InstanceOfWellFormedEnvironment request entities env

theorem action_matches_env {env : TypeEnv} {request : Request} {entities : Entities} :
  InstanceOfWellFormedEnvironment request entities env →
  request.action = env.reqty.action
:= by
  intro h₀
  simp only [InstanceOfWellFormedEnvironment, InstanceOfRequestType] at h₀
  obtain ⟨_, ⟨ _, h₁, _, _ ⟩, _⟩ := h₀
  exact h₁

theorem typecheck_policy_produces_wt {policy : Policy} {Γ : TypeEnv} {tx : TypedExpr} :
  typecheckPolicy policy Γ = .ok tx →
  TypedExpr.WellTyped Γ tx.liftBoolTypes
:= by
  simp [typecheckPolicy]
  intro h₁
  split at h₁
  · split at h₁ <;> simp at h₁
    subst tx
    rename_i tx cp h₁ h₂
    exact typechecked_is_well_typed_after_lifting h₁
  · simp at h₁

theorem typecheck_policy_is_sound {policy : Policy} {env : TypeEnv} {tx : TypedExpr} {request : Request} {entities : Entities} :
  InstanceOfWellFormedEnvironment request entities env →
  typecheckPolicy policy env = .ok tx →
  ∃ b : Bool, EvaluatesTo policy.toExpr request entities b
:= by
  intro h₁ h₂
  simp only [typecheckPolicy] at h₂
  cases h₃ : typeOf (substituteAction env.reqty.action policy.toExpr) [] env <;>
  simp only [List.empty_eq, h₃, reduceCtorEq] at h₂
  split at h₂ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₂
  rename_i cp ht
  have hc := empty_capabilities_invariant request entities
  have ⟨_, v, h₄, h₅⟩ := type_of_is_sound hc h₁ h₃
  have ⟨b, h₆⟩ := instance_of_type_bool_is_bool v cp.fst.typeOf h₅ ht
  subst h₆
  exists b
  rw [←substitute_action_preserves_evaluates_to, action_matches_env h₁]
  exact h₄

theorem typecheck_policy_with_environments_is_sound (policy : Policy) (schema : Schema) (request : Request) (entities : Entities) :
  (∃ env ∈ schema.environments, InstanceOfWellFormedEnvironment request entities env) →
  typecheckPolicyWithEnvironments typecheckPolicy policy schema = .ok () →
  ∃ b : Bool, EvaluatesTo policy.toExpr request entities b
:= by
  intro h₀ h₂
  simp only [typecheckPolicyWithEnvironments, Except.mapError] at h₂
  simp_do_let (checkEntities schema policy.toExpr) as h₄ at h₂
  cases h₃ : List.mapM (typecheckPolicy policy) schema.environments with
  | error => simp only [h₃, Except.bind_err, reduceCtorEq] at h₂
  | ok ts =>
    simp only [h₃, Except.bind_ok, ite_eq_right_iff, allFalse] at h₂
    obtain ⟨env, ⟨h₀, h₁⟩⟩ := h₀
    rw [List.mapM_ok_iff_forall₂] at h₃
    have h₄ := List.forall₂_implies_all_left h₃
    specialize h₄ env h₀
    obtain ⟨tx, ⟨_, h₅⟩⟩ := h₄
    exact typecheck_policy_is_sound h₁ h₅

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
If two schemas have the same `find?` for a given action, then the environments generated
for that action are the same (modulo ets/acts wrapping).
-/
theorem environments_reqty_from_action {schema : Schema} {env : TypeEnv}
    (henv : env ∈ schema.environments) :
    ∃ (action : EntityUID) (entry : ActionSchemaEntry),
      (action, entry) ∈ schema.acts.toList ∧
      env.reqty.action = action := by
  simp only [Schema.environments, List.mem_map, List.mem_flatMap] at henv
  obtain ⟨rt, ⟨⟨action, entry⟩, hmem_acts, hmem_rt⟩, henv_eq⟩ := henv
  have hreqty : env.reqty = rt := congrArg TypeEnv.reqty henv_eq.symm
  simp only [ActionSchemaEntry.requestTypes, List.mem_map] at hmem_rt
  obtain ⟨⟨p, r⟩, _, hrt_eq⟩ := hmem_rt
  exact ⟨action, entry, hmem_acts, by rw [hreqty]; exact congrArg RequestType.action hrt_eq.symm⟩

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

end Cedar.Thm
