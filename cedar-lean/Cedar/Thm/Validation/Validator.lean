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

def RequestAndEntitiesMatchSchema (schema : Schema) (request : Request) (entities : Entities) (l : Level) :Prop :=
  ∃ env ∈ schema.toEnvironments l,
  RequestAndEntitiesMatchEnvironment env request entities

theorem action_matches_env (env : Environment) (request : Request) (entities : Entities) :
  RequestAndEntitiesMatchEnvironment env request entities →
  request.action = env.reqty.action.fst
:= by
  intro h₀
  simp only [RequestAndEntitiesMatchEnvironment, InstanceOfRequestType] at h₀
  obtain ⟨ ⟨ _, h₁, _, _ ⟩ , _ , _⟩ := h₀
  exact h₁

theorem typecheck_policy_is_sound (policy : Policy) (env : Environment) (ty : CedarType) (request : Request) (entities : Entities) (l : Level) :
  RequestAndEntitiesMatchEnvironment env request entities →
  typecheckPolicy policy l env = .ok ty →
  ∃ b : Bool, EvaluatesTo policy.toExpr request entities b
:= by
  intro h₁ h₂
  simp only [typecheckPolicy] at h₂
  cases h₃ : typeOf (substituteAction env.reqty.action.fst policy.toExpr) [] env (l == .infinite) <;>
  simp only [List.empty_eq, h₃, reduceCtorEq] at h₂
  split at h₂ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₂
  rename_i cp ht
  have hc := empty_capabilities_invariant request entities
  have ⟨_, v, h₄, h₅⟩ := type_of_is_sound hc h₁ h₃
  have ⟨b, h₆⟩ := instance_of_type_bool_is_bool v cp.fst h₅ ht
  subst h₆
  exists b
  simp only [EvaluatesTo] at *
  cases h₄ with
  | inl h₁ =>
    left
    rw [← substitute_action_preserves_evaluation policy.toExpr request entities]
    rw [action_matches_env]
    repeat assumption
  | inr h₁ => cases h₁ with
    | inl h₂ =>
      right
      left
      rw [← substitute_action_preserves_evaluation policy.toExpr request entities]
      rw [action_matches_env]
      repeat assumption
    | inr h₂ => cases h₂ with
      | inl h₃ =>
        right
        right
        left
        rw [← substitute_action_preserves_evaluation policy.toExpr request entities]
        rw [action_matches_env]
        repeat assumption
      | inr h₃ =>
        right
        right
        right
        rw [← substitute_action_preserves_evaluation policy.toExpr request entities]
        rw [action_matches_env]
        repeat assumption

theorem typecheck_policy_with_environments_is_sound (policy : Policy) (envs : List Environment) (request : Request) (entities : Entities) (l : Level) :
  (∃ env ∈ envs, RequestAndEntitiesMatchEnvironment env request entities) →
  typecheckPolicyWithEnvironments l policy envs = .ok () →
  ∃ b : Bool, EvaluatesTo policy.toExpr request entities b
:= by
  intro h₀ h₂
  simp only [typecheckPolicyWithEnvironments] at h₂
  cases h₃ : List.mapM (typecheckPolicy policy l) envs with
  | error => simp only [h₃, Except.bind_err, reduceCtorEq] at h₂
  | ok ts =>
    simp only [h₃, Except.bind_ok, ite_eq_right_iff, imp_false, Bool.not_eq_true, allFalse] at h₂
    obtain ⟨env, ⟨h₀, h₁⟩⟩ := h₀
    rw [List.mapM_ok_iff_forall₂] at h₃
    have h₄ := List.forall₂_implies_all_left h₃
    specialize h₄ env h₀
    obtain ⟨ty, ⟨_, h₅⟩⟩ := h₄
    exact typecheck_policy_is_sound policy env ty request entities l h₁ h₅

end Cedar.Thm
