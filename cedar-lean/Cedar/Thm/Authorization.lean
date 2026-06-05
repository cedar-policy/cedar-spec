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
import Cedar.Thm.Authorization.PolicySlice
import Cedar.Thm.Authorization.Evaluator

/-! This file contains basic theorems about Cedar's authorizer. -/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec

def PolicyIdsUnique (policies : Policies) :=
  ∀ p₁ ∈ policies, ∀ p₂ ∈ policies, p₁.id = p₂.id → p₁ = p₂

def HasSatisfiedEffect (effect : Effect) (request : Request) (entities : Entities) (policies : Policies) : Prop :=
  ∃ (policy : Policy),
    policy ∈ policies ∧
    policy.effect = effect ∧
    satisfied policy request entities

theorem satisfied_iff_satisfiedPolicies_non_empty {effect : Effect} {request : Request} {entities : Entities} {policies : Policies} :
  HasSatisfiedEffect effect request entities policies ↔ (satisfiedPolicies effect policies request entities).isEmpty = false
:= by simp [HasSatisfiedEffect, satisfiedPolicies, satisfiedWithEffect]

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
A request is denied if and only if it is explicitly denied or it is not explicitly permitted.
-/
theorem denied_iff_explicitly_denied_or_not_permitted (request: Request) (entities : Entities) (policies: Policies) :
  (IsExplicitlyForbidden request entities policies ∨ ¬ IsExplicitlyPermitted request entities policies) ↔
    (isAuthorized request entities policies).decision = .deny
  := by
  apply Iff.intro
  · intro h
    cases h
    case inl => rw [forbid_trumps_permit]; assumption
    case inr => rw [default_deny]; assumption
  · intro h
    by_cases h₁ : (IsExplicitlyForbidden request entities policies)
    · exact Or.inl h₁
    · right
      rw [explicitly_forbidden_iff_satisfying_forbid] at h₁
      rw [explicitly_permitted_iff_satisfying_permit]
      unfold isAuthorized at h
      simp [h₁] at h
      split at h
      · simp at h
      · assumption

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

/--
Adding a permit policy won't change an Allow decision.
-/
theorem unchanged_allow_when_add_permit (request: Request) (entities: Entities) (policies: Policies) (policy₂: Policy) :
  policy₂.effect = .permit →
  (isAuthorized request entities policies).decision = .allow →
  (isAuthorized request entities (policy₂ :: policies)).decision = .allow
:= by
  intro h₁ h₂
  rw [← allowed_iff_explicitly_permitted_and_not_denied] at *
  unfold IsExplicitlyPermitted IsExplicitlyForbidden HasSatisfiedEffect at *
  simp [h₂, h₁]

/--
Adding a forbid policy won't change a Deny decision.
-/
theorem unchanged_deny_when_add_forbid (request : Request) (entities: Entities) (policies: Policies) (policy₂: Policy) :
  policy₂.effect = .forbid →
  (isAuthorized request entities policies).decision = .deny →
  (isAuthorized request entities (policy₂ :: policies)).decision = .deny
  := by
  intro h₁ h₂
  rw [← denied_iff_explicitly_denied_or_not_permitted] at *
  unfold IsExplicitlyPermitted IsExplicitlyForbidden HasSatisfiedEffect at *
  simp only [not_exists, not_and, Bool.not_eq_true] at h₂
  simp only [List.mem_cons, exists_eq_or_imp, h₁, true_and, reduceCtorEq, false_and, false_or, not_exists, not_and, Bool.not_eq_true]
  exact h₂.elim (fun hb => Or.inl (Or.inr hb)) Or.inr


/--
The determining policies of a allow/deny decision are exactly the satisfied policies of permit/forbid resp.
-/
theorem determiningPolicies_of (request: Request) (entities: Entities) (policies: Policies) :
  let auth := isAuthorized request entities policies
  auth.determiningPolicies = satisfiedPolicies (if auth.decision = .allow then .permit else .forbid) policies request entities
:= by
  intro auth
  simp only [auth]
  unfold isAuthorized
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  generalize h₁: satisfiedPolicies .forbid policies request entities = forbids
  generalize h₂: satisfiedPolicies .permit policies request entities = permits
  split <;> simp [h₁, h₂]

/--
If P is a determining policy, then adding a new policy resulting in the same decision won't change that.
-/
theorem unchanged_determining_when_add_policy_and_decision_unchanged (request: Request) (entities: Entities) (policies: Policies) (policy₀ : Policy) :
  let auth  := (isAuthorized request entities policies)
  let auth' := (isAuthorized request entities (policy₀ :: policies))
  auth.decision = auth'.decision → auth.determiningPolicies ⊆ auth'.determiningPolicies
  := by
  intro auth auth' h₀
  have subset_lemma : ∀ effect, satisfiedPolicies effect policies request entities ⊆
                                 satisfiedPolicies effect (policy₀ :: policies) request entities := by
    intro effect
    unfold satisfiedPolicies
    rw [List.filterMap_cons]
    cases satisfiedWithEffect effect policy₀ request entities
    · simp only [Set.subset_def, imp_self, implies_true]
    · rw [Set.make_cons_eq_singleton_union, Set.union_comm]; apply Set.subset_union
  rw [determiningPolicies_of request entities policies,
      determiningPolicies_of request entities (policy₀ :: policies)]
  simp only [h₀, auth]
  apply subset_lemma

/--
If P is an erroring policy, then adding another policy won’t change that (even if the decision changes).
-/
theorem unchanged_erroring_when_add_policy (request: Request) (entities: Entities) (policies : Policies) (policy₀ : Policy) :
  (isAuthorized request entities policies).erroringPolicies ⊆ (isAuthorized request entities (policy₀ :: policies)).erroringPolicies
  := by
  unfold isAuthorized
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  split <;> split
  all_goals {
    unfold errorPolicies
    simp only [List.filterMap_cons]
    cases errored policy₀ request entities
    · simp only [Set.subset_def, imp_self, implies_true]
    · rw [Set.make_cons_eq_singleton_union, Set.union_comm]; apply Set.subset_union
  }

/--
Determining policies and erroring policies of an isAuthorized response are disjoint when input policy IDs are unique.
-/
theorem determining_erroring_disjoint_when_unique_ids (request : Request) (entities : Entities) (policies : Policies) :
  PolicyIdsUnique policies →
    ((isAuthorized request entities policies).determiningPolicies ∩ (isAuthorized request entities policies).erroringPolicies).isEmpty
:= by
  intro
  rw [Set.empty_iff_not_exists]
  simp only [Set.mem_inter_iff, not_exists, not_and]
  rw [determiningPolicies_of]
  intro _ h_det h_err
  have ⟨p₁, h_id_p₁, h_mem_p₁, _, h_sat⟩ := mem_satisfied_policies.mp h_det
  rw [erroringPolicies_of] at h_err
  have ⟨p₂, h_id_p₂, h_mem_p₂, h₂⟩ := mem_error_policies.mp h_err
  have heq : p₁ = p₂ := by grind [PolicyIdsUnique]
  subst heq
  have l₁ : ∀ p, hasError p request entities → ¬satisfied p request entities := by
    unfold satisfied hasError
    intro
    split <;> rename_i _ s <;> simp [s]
  have : ¬satisfied _ request entities := l₁ _ h₂
  contradiction

theorem satisfiedPolicies_permit_forbid_disjoint (policies : Policies) (request request' : Request) (entities entities' : Entities)
  (h_uniq : PolicyIdsUnique policies) :
  (satisfiedPolicies .permit policies request entities ∩
   satisfiedPolicies .forbid policies request' entities').isEmpty := by
  rw [Set.disjoint_iff_no_common]
  intro pid h_permit h_forbid
  have ⟨p, h_id_p, h_mem_p, h_eff_p, _⟩ := mem_satisfied_policies.mp h_permit
  have ⟨p', h_id_p', h_mem_p', h_eff_p', _⟩ := mem_satisfied_policies.mp h_forbid
  have h_same_id : p.id = p'.id := by rw [h_id_p, h_id_p']
  have h_eq := h_uniq _ h_mem_p _ h_mem_p' h_same_id
  subst h_eq; simp_all

/--
If the determining policies for two different authorization requests against the
same policy set share a common policy id, then the authorization decisions must
be the same.
-/
theorem determiningPolicies_overlap_implies_same_decision (request request' : Request) (entities entities' : Entities) (policies : Policies) :
  PolicyIdsUnique policies →
  let auth  := isAuthorized request entities policies
  let auth' := isAuthorized request' entities' policies
  ¬ (auth.determiningPolicies ∩ auth'.determiningPolicies).isEmpty →
  auth.decision = auth'.decision := by
  intro h_uniq
  have hdet := determiningPolicies_of request entities policies
  have hdet' := determiningPolicies_of request' entities' policies
  simp only
  intro h_inter
  have ⟨pid, h_mem⟩ := (Set.non_empty_iff_exists _).mp h_inter
  rw [Set.mem_inter_iff] at h_mem
  cases hdec : (isAuthorized request entities policies).decision <;>
  cases hdec' : (isAuthorized request' entities' policies).decision <;>
  simp only [hdec, hdec', reduceCtorEq, ↓reduceIte] at hdet hdet' ⊢ <;> exfalso
  case allow.deny =>
    rw [hdet, hdet'] at h_mem
    have h_disj := (Set.disjoint_iff_no_common ..).mp
      (satisfiedPolicies_permit_forbid_disjoint policies request request' entities entities' h_uniq)
    exact h_disj pid h_mem.1 h_mem.2
  case deny.allow =>
    rw [hdet, hdet'] at h_mem
    have h_disj := (Set.disjoint_iff_no_common ..).mp
      (satisfiedPolicies_permit_forbid_disjoint policies request' request entities' entities h_uniq)
    exact h_disj pid h_mem.2 h_mem.1

/--
If the determining policies are empty, the decision is deny.
-/
theorem deny_of_empty_determining (request : Request) (entities : Entities) (policies : Policies) :
  (isAuthorized request entities policies).determiningPolicies.isEmpty →
  (isAuthorized request entities policies).decision = .deny := by
  intro h
  cases hdec : (isAuthorized request entities policies).decision <;> try rfl
  have hdet := determiningPolicies_of request entities policies
  simp only [hdec, ↓reduceIte] at hdet
  rw [hdet] at h
  have h_permitted := allowed_only_if_explicitly_permitted request entities policies hdec
  rw [explicitly_permitted_iff_satisfying_permit] at h_permitted
  simp [h_permitted] at h

/--
For two authorizations requests against the same policy set, if the determining
policies are the same, then the authorization decisions will also be the same.
This is mostly a specialization of `determiningPolicies_overlap_implies_same_decision`,
but it also needs `deny_of_empty_determining` for the default-deny case where
there are no determining policies.
-/
theorem determiningPolicies_determines_decision (request request' : Request) (entities entities' : Entities) (policies : Policies) :
  PolicyIdsUnique policies →
  let auth  := (isAuthorized request entities policies)
  let auth' := (isAuthorized request' entities' policies)
  auth.determiningPolicies = auth'.determiningPolicies →
  auth.decision = auth'.decision
:= by
  intro h_uniq
  simp only
  intro h_det_eq
  cases h_empty : (isAuthorized request entities policies).determiningPolicies.isEmpty
  · apply determiningPolicies_overlap_implies_same_decision _ _ _ _ _ h_uniq
    rw [h_det_eq, Set.inter_self, ← h_det_eq]
    simp [h_empty]
  · rw [deny_of_empty_determining _ _ _ h_empty,
        deny_of_empty_determining _ _ _ (h_det_eq ▸ h_empty)]

end Cedar.Thm
