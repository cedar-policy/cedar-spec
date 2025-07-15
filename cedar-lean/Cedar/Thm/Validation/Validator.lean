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

theorem typecheck_policy_is_sound (policy : Policy) (env : TypeEnv) (tx : TypedExpr) (request : Request) (entities : Entities) :
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

theorem typecheck_policy_with_environments_is_sound (policy : Policy) (envs : List TypeEnv) (request : Request) (entities : Entities) :
  (∃ env ∈ envs, InstanceOfWellFormedEnvironment request entities env) →
  typecheckPolicyWithEnvironments policy envs = .ok () →
  ∃ b : Bool, EvaluatesTo policy.toExpr request entities b
:= by
  intro h₀ h₂
  simp only [typecheckPolicyWithEnvironments] at h₂
  cases h₃ : List.mapM (typecheckPolicy policy) envs with
  | error => simp only [h₃, Except.bind_err, reduceCtorEq] at h₂
  | ok ts =>
    simp only [h₃, Except.bind_ok, ite_eq_right_iff, imp_false, Bool.not_eq_true, allFalse] at h₂
    obtain ⟨env, ⟨h₀, h₁⟩⟩ := h₀
    rw [List.mapM_ok_iff_forall₂] at h₃
    have h₄ := List.forall₂_implies_all_left h₃
    specialize h₄ env h₀
    obtain ⟨tx, ⟨_, h₅⟩⟩ := h₄
    exact typecheck_policy_is_sound policy env tx request entities h₁ h₅

end Cedar.Thm
