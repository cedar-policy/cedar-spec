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
import Cedar.Thm.Authorization.Authorizer

/-! This file contains basic theorems about Cedar's authorizer. -/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec

def HasSatisfiedEffect (effect : Effect) (request : Request) (entities : Entities) (policies : Policies) : Prop :=
  ∃ (policy : Policy),
    policy ∈ policies ∧
    policy.effect = effect ∧
    satisfied policy request entities

theorem satisfied_iff_satisfiedPolicies_non_empty {effect : Effect} {request : Request} {entities : Entities} {policies : Policies} :
  HasSatisfiedEffect effect request entities policies ↔ (satisfiedPolicies effect policies request entities).isEmpty = false
:= by simp [HasSatisfiedEffect, satisfiedPolicies, satisfiedWithEffect, ←Set.make_non_empty]

/--
A request is explicitly forbidden when there is at least one satisfied forbid policy.
-/
def IsExplicitlyForbidden := HasSatisfiedEffect .forbid

theorem explicitly_forbidden_iff_satisfying_forbid :
  IsExplicitlyForbidden req entities policies ↔ (satisfiedPolicies .forbid policies req entities).isEmpty = false
:= satisfied_iff_satisfiedPolicies_non_empty

/--
A request is explicitly permitted when there is at least one satisfied permit policy.
Note that there may still be satisfied forbid policies leading to a deny decisions.
-/
def IsExplicitlyPermitted := HasSatisfiedEffect .permit

theorem explicitly_permitted_iff_satisfying_permit :
  IsExplicitlyPermitted req entities policies ↔ (satisfiedPolicies .permit policies req entities).isEmpty = false
:= satisfied_iff_satisfiedPolicies_non_empty

/--
Forbid trumps permit: if a `forbid` policy is satisfied, the request is denied.
-/
theorem forbid_trumps_permit
  (request : Request) (entities : Entities) (policies : Policies) :
  (IsExplicitlyForbidden request entities policies) →
  (isAuthorized request entities policies).decision = .deny
:= by
  intro h
  unfold isAuthorized
  rw [explicitly_forbidden_iff_satisfying_forbid] at h
  simp [h]

/-- A request is allowed only if it is explicitly permitted. -/
theorem allowed_only_if_explicitly_permitted (request : Request) (entities : Entities) (policies : Policies) :
  (isAuthorized request entities policies).decision = .allow →
  IsExplicitlyPermitted request entities policies
:= by
  unfold isAuthorized
  generalize (satisfiedPolicies .forbid policies request entities) = forbids
  generalize hp : (satisfiedPolicies .permit policies request entities) = permits
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  cases forbids.isEmpty <;> simp
  cases h₁ : permits.isEmpty <;> simp
  subst hp
  exact explicitly_permitted_iff_satisfying_permit.mpr h₁

/--
Default deny: if not explicitly permitted, the request is denied.
This is contrapositive of allowed_only_if_explicitly_permitted.
-/
theorem default_deny (request : Request) (entities : Entities) (policies : Policies) :
  ¬ IsExplicitlyPermitted request entities policies →
  (isAuthorized request entities policies).decision = .deny
:= by
  intro h₀
  generalize h₁ : (isAuthorized request entities policies).decision = dec
  by_contra h₂
  cases dec
  case allow =>
    have h₃ := allowed_only_if_explicitly_permitted request entities policies h₁
    contradiction
  case deny => contradiction

/--
A request is allowed if and only if it is explicitly permitted and is not
explicitly forbidden.
-/
theorem allowed_iff_explicitly_permitted_and_not_denied (request : Request) (entities : Entities) (policies : Policies) :
  (IsExplicitlyPermitted request entities policies ∧ ¬ IsExplicitlyForbidden request entities policies) ↔
  (isAuthorized request entities policies).decision = .allow
:= by
  apply Iff.intro
  · intro ⟨h₁, h₂⟩
    unfold isAuthorized
    rw [explicitly_permitted_iff_satisfying_permit] at h₁
    rw [explicitly_forbidden_iff_satisfying_forbid] at h₂
    simp [h₁, h₂]
  · intro h₁
    have h₁' : ¬ (isAuthorized request entities policies).decision = Decision.deny := by simp [h₁]
    have h₂ := (mt $ forbid_trumps_permit request entities policies) h₁'
    have h₃ := allowed_only_if_explicitly_permitted request entities policies h₁
    exact .intro h₃ h₂

/--
Order and duplicate independence: isAuthorized produces the same result
regardless of policy order or duplicates.
-/
theorem order_and_dup_independent (request : Request) (entities : Entities) (policies₁ policies₂ : Policies) :
  policies₁ ≡ policies₂ →
  isAuthorized request entities policies₁ = isAuthorized request entities policies₂
:= by
  intro h
  have hf := satisfiedPolicies_order_and_dup_independent .forbid request entities h
  have hp := satisfiedPolicies_order_and_dup_independent .permit request entities h
  have he := errorPolicies_order_and_dup_independent request entities h
  simp [isAuthorized, hf, hp, he]

end Cedar.Thm
