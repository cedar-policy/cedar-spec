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

import Cedar.Slice.PolicySlice
import Cedar.Thm.Authorization.Authorizer

/-! This file contains definitions relevant to slicing. -/

namespace Cedar.Thm

open Cedar.Spec Cedar.Slice Cedar.Data

/--
A policy slice is a subset of a collection of policies.  This slice is sound for
a given request and entities if every policy in the collection that is not in
the slice is also not satisfied with respect to the request and entities, and
doesn't produce an error when evaluated.
-/
def IsSoundPolicySlice (req : Request) (entities : Entities) (slice policies : Policies) : Prop :=
  slice ⊆ policies ∧
  ∀ policy ∈ policies,
    policy ∉ slice →
    ¬ satisfied policy req entities ∧ ¬ hasError policy req entities

/--
A bound is sound for a given policy if the bound is satisfied for every request
and entities for which the policy is satisfied or for which the policy produces
an error.
-/
def IsSoundPolicyBound (bound : PolicyBound) (policy : Policy) : Prop :=
  ∀ (request : Request) (entities : Entities),
  (satisfied policy request entities →
  satisfiedBound bound request entities) ∧
  (hasError policy request entities →
  satisfiedBound bound request entities)

/--
A bound analysis is sound if it produces sound bounds for all policies.
-/
def IsSoundBoundAnalysis (ba : BoundAnalysis) : Prop :=
  ∀ (policy : Policy), IsSoundPolicyBound (ba policy) policy

theorem sound_policy_slice_is_equisatisfied (effect : Effect) {request : Request} {entities : Entities} {slice policies : Policies} :
  IsSoundPolicySlice request entities slice policies →
  slice.filterMap (satisfiedWithEffect effect · request entities) ≡
  policies.filterMap (satisfiedWithEffect effect · request entities)
:= by
  intro h
  unfold IsSoundPolicySlice at h
  have ⟨h₁, h₂⟩ := h; clear h
  simp [List.Equiv]
  simp [List.subset_def]
  apply And.intro <;>
  intros pid policy h₃ h₄ <;>
  exists policy <;>
  simp [h₄]
  case left =>
    simp [List.subset_def] at h₁
    specialize h₁ h₃
    exact h₁
  case right =>
    by_contra h₅
    specialize h₂ policy h₃ h₅
    simp [h₂, satisfiedWithEffect] at h₄

theorem satisfiedPolicies_eq_for_sound_policy_slice (effect : Effect) {request : Request} {entities : Entities} {slice policies : Policies} :
  IsSoundPolicySlice request entities slice policies →
  satisfiedPolicies effect slice request entities = satisfiedPolicies effect policies request entities
:= by
  intro h
  unfold satisfiedPolicies
  rw [Set.make_make_eqv]
  exact sound_policy_slice_is_equisatisfied effect h

theorem sound_policy_slice_is_equierror {request : Request} {entities : Entities} {slice policies : Policies} :
  IsSoundPolicySlice request entities slice policies →
  slice.filter (hasError · request entities) ≡ policies.filter (hasError · request entities)
:= by
  intro h
  unfold IsSoundPolicySlice at h
  have ⟨h₁, h₂⟩ := h; clear h
  simp [List.Equiv, List.subset_def]
  rw [List.subset_def] at h₁
  apply And.intro <;>
  intro policy h₄ h₅ <;>
  apply And.intro
  · exact h₁ h₄
  · exact h₅
  · by_contra h₆
    specialize h₂ policy h₄ h₆
    exact h₂.right h₅
  · exact h₅

theorem errorPolicies_eq_for_sound_policy_slice {request : Request} {entities : Entities} {slice policies : Policies} :
  IsSoundPolicySlice request entities slice policies →
  errorPolicies slice request entities = errorPolicies policies request entities
:= by
  intro h
  repeat rw [alternate_errorPolicies_equiv_errorPolicies]
  unfold alternateErrorPolicies
  rw [Set.make_make_eqv]
  apply List.map_equiv
  exact sound_policy_slice_is_equierror h

end Cedar.Thm
