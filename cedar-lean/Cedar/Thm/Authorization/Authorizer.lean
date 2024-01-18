/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
import Cedar.Thm.Authorization.Evaluator

/-!
This file contains useful lemmas about the `Authorizer` functions.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Data

theorem if_satisfied_then_satisfiedPolicies_non_empty (effect : Effect) (policies : Policies) (request : Request) (entities : Entities) :
  (∃ policy,
    policy ∈ policies ∧
    policy.effect = effect ∧
    satisfied policy request entities) →
  (satisfiedPolicies effect policies request entities).isEmpty = false
:= by
  intro h0
  cases h0
  case intro policy h1 =>
    have ⟨ha, hb, hc⟩ := h1
    unfold satisfiedPolicies
    rw [←Set.make_non_empty]
    apply @List.ne_nil_of_mem _ policy.id
    simp [List.mem_filterMap]
    apply Exists.intro policy
    unfold satisfiedWithEffect
    simp [ha, hb, hc]


theorem if_satisfiedPolicies_non_empty_then_satisfied (effect : Effect) (policies : Policies) (request : Request) (entities : Entities) :
  (satisfiedPolicies effect policies request entities).isEmpty = false →
  ∃ policy,
    policy ∈ policies ∧
    policy.effect = effect ∧
    satisfied policy request entities
:= by
  unfold satisfiedPolicies
  intro h0
  rw [←Set.make_non_empty] at h0
  have ⟨pid, h1⟩ := List.exists_mem_of_ne_nil _ h0
  rw [List.mem_filterMap] at h1
  have ⟨policy, h1, h2⟩ := h1
  unfold satisfiedWithEffect at h2
  apply Exists.intro policy
  simp [h1]
  cases h3 : (policy.effect == effect) <;> simp at h3; simp [h3] at h2
  simp [h3]
  cases h4 : (satisfied policy request entities)
  case _ => simp [h3, h4] at h2
  case _ => rfl

theorem satisfiedPolicies_order_and_dup_independent (effect : Effect) (request : Request) (entities : Entities) (policies₁ policies₂ : Policies) :
  policies₁ ≡ policies₂ →
  satisfiedPolicies effect policies₁ request entities = satisfiedPolicies effect policies₂ request entities
:= by
  intro h₁
  unfold satisfiedPolicies
  apply Set.make_eq_if_eqv
  exact List.filterMap_equiv (satisfiedWithEffect effect · request entities) policies₁ policies₂ h₁

theorem sound_policy_slice_is_equisatisfied (effect : Effect) (request : Request) (entities : Entities) (slice policies : Policies) :
  slice ⊆ policies →
  (∀ policy, policy ∈ policies → policy ∉ slice → ¬ satisfied policy request entities) →
  slice.filterMap (satisfiedWithEffect effect · request entities) ≡
  policies.filterMap (satisfiedWithEffect effect · request entities)
:= by
  intros h₁ h₂
  simp [List.Equiv]
  simp [List.subset_def]
  apply And.intro <;>
  intros pid policy h₃ h₄ <;>
  apply Exists.intro policy <;>
  simp [h₄]
  case _ =>
    simp [List.subset_def] at h₁
    specialize h₁ h₃
    exact h₁
  case _ =>
    by_contra h₅
    specialize h₂ policy h₃ h₅
    unfold satisfiedWithEffect at h₄
    simp [h₂] at h₄

theorem satisfiedPolicies_eq_for_sound_policy_slice (effect : Effect) (request : Request) (entities : Entities) (slice policies : Policies) :
  slice ⊆ policies →
  (∀ policy, policy ∈ policies → policy ∉ slice → ¬ satisfied policy request entities) →
  satisfiedPolicies effect slice request entities = satisfiedPolicies effect policies request entities
:= by
  intro h₁ h₂
  unfold satisfiedPolicies
  apply Set.make_eq_if_eqv
  exact sound_policy_slice_is_equisatisfied effect request entities slice policies h₁ h₂

theorem satisfied_implies_principal_scope {policy : Policy} {request : Request} {entities : Entities} {uid : EntityUID} :
  satisfied policy request entities = true →
  policy.principalScope.scope.bound = .some uid →
  inₑ request.principal uid entities = true
:= by
  intro h₁ h₂
  simp [satisfied] at h₁
  unfold Policy.toExpr at h₁
  have h₃ := and_true_implies_left_true h₁
  clear h₁
  simp [PrincipalScope.toExpr, Scope.toExpr] at h₃
  simp [Scope.bound, PrincipalScope.scope] at h₂
  generalize h₄ : policy.3.1 = x
  simp only [h₄] at h₂ h₃
  cases x <;> simp at h₂ h₃ <;>
  simp only [h₂] at h₃
  case eq =>
    simp [evaluate, Var.eqEntityUID, apply₂] at h₃
    simp [inₑ, h₃]
  case mem =>
    simp [evaluate, Var.inEntityUID, apply₂] at h₃
    exact h₃
  case isMem =>
    have h₅ := and_true_implies_right_true h₃
    simp [evaluate, Var.inEntityUID, apply₂] at h₅
    exact h₅

theorem satisfied_implies_resource_scope {policy : Policy} {request : Request} {entities : Entities} {uid : EntityUID} :
  satisfied policy request entities = true →
  policy.resourceScope.scope.bound = .some uid →
  inₑ request.resource uid entities = true
:= by
  intro h₁ h₂
  simp [satisfied] at h₁
  unfold Policy.toExpr at h₁
  rcases
    (and_true_implies_left_true
      (and_true_implies_right_true
        (and_true_implies_right_true h₁))) with h₃
  clear h₁
  simp [ResourceScope.toExpr, Scope.toExpr] at h₃
  simp [Scope.bound, ResourceScope.scope] at h₂
  generalize h₄ : policy.5.1 = x
  simp only [h₄] at h₂ h₃
  cases x <;> simp at h₂ h₃ <;>
  simp only [h₂] at h₃
  case eq =>
    simp [evaluate, Var.eqEntityUID, apply₂] at h₃
    simp [inₑ, h₃]
  case mem =>
    simp [evaluate, Var.inEntityUID, apply₂] at h₃
    exact h₃
  case isMem =>
    have h₅ := and_true_implies_right_true h₃
    simp [evaluate, Var.inEntityUID, apply₂] at h₅
    exact h₅


end Cedar.Thm
