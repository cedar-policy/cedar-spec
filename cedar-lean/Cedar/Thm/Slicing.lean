/-
 Copyright Cedar Contributors

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
import Cedar.Thm.Authorization.Slicing

/-!
This file defines what it means for a policy slice to be sound.

We prove two main theorems:

* Authorization returns the same response for a sound policy slice as for the
  original collection of policies (`isAuthorized_eq_for_sound_policy_slice`).
* It is sound to slice policies based on scope constraints (see
  `isAuthorized_eq_for_scope_based_policy_slice`). The proof is based on a more
  general lemma (`sound_bound_analysis_produces_sound_slices`) that covers all
  forms of slicing that are based on identifying "bound" principal and resource
  entities (if any) for a policy, such that the policy evaluates to true on an
  input only if the request principal and resource are descendents of the
  corresponding bound entities. Currently, we are extracting bounds only from
  the scope constraints. The general lemma also covers more sophisticated
  analyses that can extract bounds from policy conditions as well.
--/

namespace Cedar.Thm

open Cedar.Spec

/--
Policy slicing soundness: `isAuthorized` produces the same result for a sound
slice (subset) of a collection of policies as it does for the original policies.
-/
theorem isAuthorized_eq_for_sound_policy_slice (req : Request) (entities : Entities) (slice policies : Policies) :
  IsSoundPolicySlice req entities slice policies →
  isAuthorized req entities slice = isAuthorized req entities policies
:= by
  intro h₀
  have hf :=
    satisfiedPolicies_eq_for_sound_policy_slice .forbid req entities slice policies h₀
  have hp :=
    satisfiedPolicies_eq_for_sound_policy_slice .permit req entities slice policies h₀
  have he :=
    errorPolicies_eq_for_sound_policy_slice req entities slice policies h₀
  simp [isAuthorized, hf, hp, he]

/--
A sound bound analysis produces sound policy slices.
-/
theorem sound_bound_analysis_produces_sound_slices (ba : BoundAnalysis) (request : Request) (entities : Entities) (policies : Policies) :
  IsSoundBoundAnalysis ba →
  IsSoundPolicySlice request entities (ba.slice request entities policies) policies
:= by
  unfold IsSoundBoundAnalysis
  unfold IsSoundPolicySlice
  intro h₁
  unfold BoundAnalysis.slice
  apply And.intro
  case left =>
    intro p _
    simp_all only [List.mem_filter]
  case right =>
    intro policy
    specialize h₁ policy
    intro h₂ h₃
    rw [List.mem_filter] at h₃
    simp [h₂] at h₃
    by_contra h₄
    simp at h₄
    unfold IsSoundPolicyBound at h₁
    specialize h₁ request entities
    have ⟨h₅, h₆⟩ := h₁; clear h₁
    simp [h₃] at h₅ h₆
    cases h : (satisfied policy request entities)
    case false =>
      simp [h] at h₄
      simp [h₄] at h₆
    case true => exact h₅ h

/--
Scope-based bound analysis extracts the bound from the policy scope.
-/
def scopeAnalysis (policy : Policy) : PolicyBound :=
  {
    principalBound := policy.principalScope.scope.bound,
    resourceBound  := policy.resourceScope.scope.bound,
  }

/--
Scope-based bounds are sound.
-/
theorem scope_bound_is_sound (policy : Policy) :
  IsSoundPolicyBound (scopeAnalysis policy) policy
:= by
  unfold IsSoundPolicyBound
  intro request entities
  unfold scopeAnalysis
  unfold satisfiedBound
  unfold Scope.bound
  unfold inSomeOrNone
  simp only [decide_eq_true_eq]
  apply And.intro <;>
  intro h₁ <;>
  apply And.intro
  case left.left =>
    generalize h₂ : policy.principalScope.scope = s
    cases s <;> simp <;>
    apply satisfied_implies_principal_scope h₁ <;>
    simp only [Scope.bound, h₂]
  case left.right =>
    generalize h₂ : policy.resourceScope.scope = s
    cases s <;> simp <;>
    apply satisfied_implies_resource_scope h₁ <;>
    simp only [Scope.bound, h₂]
  case right.left =>
    generalize h₂ : policy.principalScope.scope = s
    replace ⟨err, h₁⟩ := if_hasError_then_exists_error h₁
    cases s <;> simp <;>
    apply error_implies_principal_scope_in h₁ <;>
    simp only [Scope.bound, h₂]
  case right.right =>
    generalize h₂ : policy.resourceScope.scope = s
    replace ⟨err, h₁⟩ := if_hasError_then_exists_error h₁
    cases s <;> simp <;>
    apply error_implies_resource_scope_in h₁ <;>
    simp only [Scope.bound, h₂]

/--
Scope-based bound analysis is sound.
-/
theorem scope_analysis_is_sound :
  IsSoundBoundAnalysis scopeAnalysis
:= by
  simp [IsSoundBoundAnalysis, scope_bound_is_sound]

/--
Scope-based slicing is sound: `isAuthorized` produces the same result for a
scope-based slice of a collection of policies as it does for the original
policies.
-/
theorem isAuthorized_eq_for_scope_based_policy_slice (request : Request) (entities : Entities) (policies : Policies) :
  isAuthorized request entities (BoundAnalysis.slice scopeAnalysis request entities policies) =
  isAuthorized request entities policies
:= by
  apply isAuthorized_eq_for_sound_policy_slice
  apply sound_bound_analysis_produces_sound_slices
  exact scope_analysis_is_sound

end Cedar.Thm
