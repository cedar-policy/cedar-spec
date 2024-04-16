/-
 Copyright Cedar Contributors. All Rights Reserved.

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
import Cedar.Thm.Authorization.Authorizer

/-! This file contains basic theorems about Cedar's authorizer. -/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec

open Decision
open Effect
open Option

/--
Forbid trumps permit: if a `forbid` policy is satisfied, the request is denied.
-/
theorem forbid_trumps_permit
  (request : Request) (entities : Entities) (policies : Policies) :
  (∃ (policy : Policy),
    policy ∈ policies ∧
    policy.effect = forbid ∧
    satisfied policy request entities) →
  (isAuthorized request entities policies).decision = deny
:= by
  intro h
  unfold isAuthorized
  simp [if_satisfied_then_satisfiedPolicies_non_empty forbid policies request entities h]

/--
A request is explicitly permitted when there is at least one satisfied permit policy.
-/
def IsExplicitlyPermitted (request : Request) (entities : Entities) (policies : Policies) : Prop :=
  ∃ (policy : Policy),
    policy ∈ policies ∧
    policy.effect = permit ∧
    satisfied policy request entities

/-- A request is allowed only if it is explicitly permitted. -/
theorem allowed_if_explicitly_permitted (request : Request) (entities : Entities) (policies : Policies) :
  (isAuthorized request entities policies).decision = allow →
  IsExplicitlyPermitted request entities policies
:= by
  unfold isAuthorized
  generalize (satisfiedPolicies forbid policies request entities) = forbids
  generalize hp : (satisfiedPolicies permit policies request entities) = permits
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  cases forbids.isEmpty <;> simp
  cases h0 : permits.isEmpty <;> simp
  unfold IsExplicitlyPermitted
  apply if_satisfiedPolicies_non_empty_then_satisfied permit policies
  simp [hp, h0]

/--
Default deny: if not explicitly permitted, the request is denied.
This is contrapositive of allowed_if_explicitly_permitted.
-/
theorem default_deny (request : Request) (entities : Entities) (policies : Policies) :
  ¬ IsExplicitlyPermitted request entities policies →
  (isAuthorized request entities policies).decision = deny
:= by
  intro h0
  generalize h1 : (isAuthorized request entities policies).decision = dec
  by_contra h2
  cases dec
  case allow =>
    have h3 := allowed_if_explicitly_permitted request entities policies h1
    contradiction
  case deny => contradiction

/--
Order and duplicate independence: isAuthorized produces the same result
regardless of policy order or duplicates.
-/
theorem order_and_dup_independent (request : Request) (entities : Entities) (policies₁ policies₂ : Policies) :
  policies₁ ≡ policies₂ →
  isAuthorized request entities policies₁ = isAuthorized request entities policies₂
:= by
  intro h
  have hf := satisfiedPolicies_order_and_dup_independent forbid request entities policies₁ policies₂ h
  have hp := satisfiedPolicies_order_and_dup_independent permit request entities policies₁ policies₂ h
  have he := errorPolicies_order_and_dup_independent request entities policies₁ policies₂ h
  unfold isAuthorized
  simp [hf, hp, he]

end Cedar.Thm
