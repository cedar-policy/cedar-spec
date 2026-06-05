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
import Cedar.Thm.Authorization

/-!
# Default-Allow Semantics

Cedar uses default-deny semantics: a request is denied unless explicitly
permitted. Users can emulate default-allow semantics by adding a single
`permit(principal, action, resource)` policy (which permits everything), and
then writing all other policies as `forbid` policies.

This file defines `isAuthorizedDefaultAllow`, which prepends such a permit-all
policy and forwards to the standard authorizer, and proves the expected
properties of the resulting system.

Prove the following new theorems specific to default-allow authorization:

- `default_allow`: not forbidden → allow
- `default_allow_iff_not_denied`: allow ↔ ¬ forbidden
- `default_allow_denied_iff`: deny ↔ forbidden
- `default_allow_permit_irrelevant`: additional permit policies have no effect on the decision
- `default_allow_determiningPolicies_of`: determining policies are always non-empty
- `default_allow_determiningPolicies_allow`: the permit-all ID is always determining when allowed
- `default_allow_erroring_eq`: erroring policies are identical to standard authorization

And the following theorems which are trivial correspond exactly to theorems for
the standard `isAuthorized`:

- `default_allow_forbid_trumps_permit`
- `default_allow_unchanged_deny_when_add_forbid`
- `default_allow_unchanged_erroring_when_add_policy`
- `default_allow_determining_erroring_disjoint`
- `default_allow_order_and_dup_independent`
- `default_allow_unchanged_determining_when_add_policy_and_decision_unchanged`
- `default_allow_determiningPolicies_determines_decision`
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.Data

def permitAll (id : PolicyID) : Policy where
  id := id
  effect := .permit
  principalScope := .principalScope .any
  actionScope := .actionScope .any
  resourceScope := .resourceScope .any
  condition := []

def isAuthorizedDefaultAllow (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID := "default-permit") : Response :=
  isAuthorized request entities (permitAll id :: policies)

def DefaultAllowIdsUnique (policies : Policies) (id : PolicyID) : Prop :=
  PolicyIdsUnique policies ∧ ∀ p ∈ policies, p.id ≠ id

private theorem permitAll_satisfied (id : PolicyID) (request : Request) (entities : Entities) :
  satisfied (permitAll id) request entities = true := by
  simp [satisfied, permitAll, Policy.toExpr, PrincipalScope.toExpr, ActionScope.toExpr,
    ResourceScope.toExpr, Scope.toExpr, Conditions.toExpr, evaluate, Result.as, Coe.coe,
    Value.asBool]

private theorem permitAll_explicitly_permitted (id : PolicyID) (request : Request) (entities : Entities) (policies : Policies) :
  IsExplicitlyPermitted request entities (permitAll id :: policies) := by
  unfold IsExplicitlyPermitted HasSatisfiedEffect
  exact ⟨permitAll id, List.mem_cons_self .., rfl, permitAll_satisfied id request entities⟩

/--
Default allow: if no forbid policy is satisfied, the request is allowed.
Analogous to standard `default_deny` theorem, but showing we now have default-allow semantics.
-/
theorem default_allow (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) :
  ¬ IsExplicitlyForbidden request entities policies →
  (isAuthorizedDefaultAllow request entities policies id).decision = .allow := by
  intro h
  have h_not_forbid : ¬ IsExplicitlyForbidden request entities (permitAll id :: policies) := by
    intro ⟨policy, h_mem, h_eff, h_sat⟩
    cases h_mem with
    | head => simp [permitAll] at h_eff
    | tail _ h_mem => exact h ⟨policy, h_mem, h_eff, h_sat⟩
  have h_allow := (allowed_iff_explicitly_permitted_and_not_denied request entities (permitAll id :: policies)).mp
    ⟨permitAll_explicitly_permitted id request entities policies, h_not_forbid⟩
  exact h_allow

/--
Forbid still trumps permit. Exactly the same theorem as the standard `forbid_trumps_permit`.
-/
theorem default_allow_forbid_trumps_permit (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) :
  IsExplicitlyForbidden request entities policies →
  (isAuthorizedDefaultAllow request entities policies id).decision = .deny := by
  intro ⟨policy, h_mem, h_eff, h_sat⟩
  apply forbid_trumps_permit
  exact ⟨policy, List.mem_cons_of_mem _ h_mem, h_eff, h_sat⟩

/--
A request is allowed if and only if it is not explicitly forbidden.  Analog of
`allowed_iff_explicitly_permitted_and_not_denied`, but reduced because
`IsExplicitlyPermitted` in the original is always True.
-/
theorem default_allow_iff_not_denied (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) :
  (isAuthorizedDefaultAllow request entities policies id).decision = .allow ↔
  ¬ IsExplicitlyForbidden request entities policies := by
  constructor
  · intro h_allow h_forbid
    have h_deny := default_allow_forbid_trumps_permit request entities policies id h_forbid
    simp [h_deny] at h_allow
  · exact default_allow request entities policies id

/--
A request is denied if and only if it is explicitly forbidden.  Analog of
`denied_iff_explicitly_denied_or_not_permitted`, but reduced because
`¬IsExplicitlyPermitted` in the original is always False.
-/
theorem default_allow_denied_iff (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) :
  (isAuthorizedDefaultAllow request entities policies id).decision = .deny ↔
  IsExplicitlyForbidden request entities policies := by
  constructor
  · intro h_deny
    by_contra h_not
    have := default_allow request entities policies id h_not
    simp [this] at h_deny
  · exact default_allow_forbid_trumps_permit request entities policies id

/--
Permit irrelevance: adding a permit policy does not change the authorization
decision. Stronger variant of `unchanged_allow_when_add_permit`.  The decision
is unchanged regardless of what it was, not just when it was allow.
-/
theorem default_allow_permit_irrelevant (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) (policy : Policy) :
  policy.effect = .permit →
  (isAuthorizedDefaultAllow request entities (policy :: policies) id).decision =
  (isAuthorizedDefaultAllow request entities policies id).decision := by
  intro h_eff
  have h_forbid_iff : IsExplicitlyForbidden request entities (policy :: policies) ↔
      IsExplicitlyForbidden request entities policies := by
    constructor
    · intro ⟨p, h_mem, h_eff', h_sat⟩
      cases h_mem with
      | head => simp [h_eff] at h_eff'
      | tail _ h_mem => exact ⟨p, h_mem, h_eff', h_sat⟩
    · intro ⟨p, h_mem, h_eff', h_sat⟩
      exact ⟨p, List.mem_cons_of_mem _ h_mem, h_eff', h_sat⟩
  by_cases h : IsExplicitlyForbidden request entities policies
  · rw [default_allow_forbid_trumps_permit _ _ _ id (h_forbid_iff.mpr h),
        default_allow_forbid_trumps_permit _ _ _ id h]
  · rw [default_allow _ _ _ id (mt h_forbid_iff.mp h),
        default_allow _ _ _ id h]

/--
Exactly standard `unchanged_deny_when_add_forbid` theorem.
-/
theorem default_allow_unchanged_deny_when_add_forbid (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) (policy : Policy) :
  policy.effect = .forbid →
  (isAuthorizedDefaultAllow request entities policies id).decision = .deny →
  (isAuthorizedDefaultAllow request entities (policy :: policies) id).decision = .deny := by
  intro _ h_deny
  rw [default_allow_denied_iff] at h_deny ⊢
  obtain ⟨p, h_mem, h_eff, h_sat⟩ := h_deny
  exact ⟨p, List.mem_cons_of_mem _ h_mem, h_eff, h_sat⟩

private theorem permitAll_not_errored (id : PolicyID) (request : Request) (entities : Entities) :
  hasError (permitAll id) request entities = false := by
  simp [hasError, permitAll, Policy.toExpr, PrincipalScope.toExpr, ActionScope.toExpr,
    ResourceScope.toExpr, Scope.toExpr, Conditions.toExpr, evaluate, Result.as, Coe.coe,
    Value.asBool]

/--
Erroring policies in default-allow mode are exactly the same as in standard
authorization.
-/
theorem default_allow_erroring_eq (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) :
  (isAuthorizedDefaultAllow request entities policies id).erroringPolicies =
    (isAuthorized request entities policies).erroringPolicies := by
  unfold isAuthorizedDefaultAllow
  rw [erroringPolicies_of, erroringPolicies_of]
  unfold errorPolicies
  simp [errored, permitAll_not_errored]

/--
Exactly the standard `unchanged_erroring_when_add_policy` theorem.
-/
theorem default_allow_unchanged_erroring_when_add_policy (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) (policy : Policy) :
  (isAuthorizedDefaultAllow request entities policies id).erroringPolicies ⊆
    (isAuthorizedDefaultAllow request entities (policy :: policies) id).erroringPolicies := by
  rw [default_allow_erroring_eq, default_allow_erroring_eq]
  exact unchanged_erroring_when_add_policy request entities policies policy

/--
The determining policies equal the satisfied policies of the appropriate effect,
and they are always non-empty. Direct analog of `determiningPolicies_of`, but
extend to show that determining policies are always non-empty (there is no default-deny).
-/
theorem default_allow_determiningPolicies_of (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) :
  let auth := isAuthorizedDefaultAllow request entities policies id
  auth.determiningPolicies = satisfiedPolicies (if auth.decision = .allow then .permit else .forbid)
    (permitAll id :: policies) request entities ∧
  ¬ auth.determiningPolicies.isEmpty := by
  simp only [isAuthorizedDefaultAllow]
  have hdet := determiningPolicies_of request entities (permitAll id :: policies)
  simp only at hdet
  constructor
  · exact hdet
  · cases h_dec : (isAuthorized request entities (permitAll id :: policies)).decision
    · simp only [h_dec, ↓reduceIte] at hdet
      rw [hdet]
      have h_permitted := permitAll_explicitly_permitted id request entities policies
      rw [explicitly_permitted_iff_satisfying_permit] at h_permitted
      simp [h_permitted]
    · simp only [h_dec, reduceCtorEq, ↓reduceIte] at hdet
      rw [hdet]
      have h_forbid : IsExplicitlyForbidden request entities policies := by
        rw [← default_allow_denied_iff]
        unfold isAuthorizedDefaultAllow
        exact h_dec
      have : IsExplicitlyForbidden request entities (permitAll id :: policies) :=
        ⟨h_forbid.choose, List.mem_cons_of_mem _ h_forbid.choose_spec.1,
         h_forbid.choose_spec.2.1, h_forbid.choose_spec.2.2⟩
      rw [explicitly_forbidden_iff_satisfying_forbid] at this
      simp [this]


/--
When the decision is allow, the determining policies are exactly the satisfied
permit policies, and in particular the permit-all policy ID is always among
them.  This is the standard `determiningPolicies_of` theorem specialized to the
allow case and extended to show that the allow-all policy is always determining.
-/
theorem default_allow_determiningPolicies_allow (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) :
  (isAuthorizedDefaultAllow request entities policies id).decision = .allow →
  (isAuthorizedDefaultAllow request entities policies id).determiningPolicies =
    satisfiedPolicies .permit (permitAll id :: policies) request entities ∧
  id ∈ (isAuthorizedDefaultAllow request entities policies id).determiningPolicies := by
  intro h_allow
  have ⟨h_eq, _⟩ := default_allow_determiningPolicies_of request entities policies id
  simp only [h_allow, ↓reduceIte] at h_eq
  refine ⟨h_eq, ?_⟩
  rw [h_eq]
  apply mem_satisfied_policies.mpr
  exact ⟨permitAll id, rfl, List.mem_cons_self .., rfl, permitAll_satisfied id request entities⟩

private theorem policyIdsUnique_permitAll_cons (policies : Policies) (id : PolicyID)
  (h : DefaultAllowIdsUnique policies id) :
  PolicyIdsUnique (permitAll id :: policies) := by
  obtain ⟨h_uniq, h_fresh⟩ := h
  intro p₁ h_mem₁ p₂ h_mem₂ h_id_eq
  cases h_mem₁ with
  | head =>
    cases h_mem₂ with
    | head => rfl
    | tail _ h_mem₂ =>
      exfalso
      exact h_fresh p₂ h_mem₂ (h_id_eq ▸ rfl)
  | tail _ h_mem₁ =>
    cases h_mem₂ with
    | head =>
      exfalso
      exact h_fresh p₁ h_mem₁ h_id_eq
    | tail _ h_mem₂ =>
      exact h_uniq p₁ h_mem₁ p₂ h_mem₂ h_id_eq

/--
Determining and erroring policies are disjoint, provided
policy IDs are unique and the permit-all ID is fresh.
Analog of `determining_erroring_disjoint_when_unique_ids`. Same statement,
with the uniqueness precondition split into user-facing parts.
-/
theorem default_allow_determining_erroring_disjoint (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) :
  DefaultAllowIdsUnique policies id →
  ((isAuthorizedDefaultAllow request entities policies id).determiningPolicies ∩
   (isAuthorizedDefaultAllow request entities policies id).erroringPolicies).isEmpty := by
  intro h
  apply determining_erroring_disjoint_when_unique_ids
  exact policyIdsUnique_permitAll_cons policies id h

/--
Exactly the standard `order_and_dup_independent` theorem.
-/
theorem default_allow_order_and_dup_independent (request : Request) (entities : Entities) (policies₁ policies₂ : Policies) (id : PolicyID) :
  policies₁ ≡ policies₂ →
  isAuthorizedDefaultAllow request entities policies₁ id = isAuthorizedDefaultAllow request entities policies₂ id := by
  intro h
  unfold isAuthorizedDefaultAllow
  apply order_and_dup_independent
  exact List.cons_equiv_cons _ _ _ h

/--
Exactly the standard `unchanged_determining_when_add_policy_and_decision_unchanged` theorem.
-/
theorem default_allow_unchanged_determining_when_add_policy_and_decision_unchanged (request : Request) (entities : Entities) (policies : Policies) (id : PolicyID) (policy : Policy) :
  (isAuthorizedDefaultAllow request entities policies id).decision =
    (isAuthorizedDefaultAllow request entities (policy :: policies) id).decision →
  (isAuthorizedDefaultAllow request entities policies id).determiningPolicies ⊆
    (isAuthorizedDefaultAllow request entities (policy :: policies) id).determiningPolicies := by
  intro h_dec_eq
  unfold isAuthorizedDefaultAllow at h_dec_eq ⊢
  have h_swap := order_and_dup_independent request entities
    (policy :: permitAll id :: policies) (permitAll id :: policy :: policies)
    (List.swap_cons_cons_equiv ..)
  have h_dec_eq' : (isAuthorized request entities (permitAll id :: policies)).decision =
      (isAuthorized request entities (policy :: permitAll id :: policies)).decision := by
    rw [h_dec_eq]; exact congrArg Response.decision h_swap.symm
  rw [← h_swap]
  exact unchanged_determining_when_add_policy_and_decision_unchanged
    request entities (permitAll id :: policies) policy h_dec_eq'

/--
Exactly the standard of `determiningPolicies_determines_decision` theorem.
-/
theorem default_allow_determiningPolicies_determines_decision (request request' : Request) (entities entities' : Entities) (policies : Policies) (id : PolicyID) :
  DefaultAllowIdsUnique policies id →
  let auth  := isAuthorizedDefaultAllow request entities policies id
  let auth' := isAuthorizedDefaultAllow request' entities' policies id
  auth.determiningPolicies = auth'.determiningPolicies →
  auth.decision = auth'.decision := by
  intro h
  unfold isAuthorizedDefaultAllow
  apply determiningPolicies_determines_decision
  exact policyIdsUnique_permitAll_cons policies id h

end Cedar.Thm
