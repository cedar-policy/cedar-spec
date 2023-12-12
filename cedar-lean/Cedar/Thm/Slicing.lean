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
import Cedar.Thm.Authorization.Authorizer

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
A policy slice is a subset of a collection of policies.  This slice is sound for
a given request and entities if every policy in the collection that is not in the slice is also
not satisfied with respect to the request and entities.
-/
def IsSoundPolicySlice (req : Request) (entities : Entities) (slice policies : Policies) : Prop :=
  slice ⊆ policies ∧
  ∀ policy,
    policy ∈ policies →
    policy ∉ slice →
    ¬ satisfied policy req entities

/--
Policy slicing soundness: `isAuthorized` produces the same result for a sound
slice (subset) of a collection of policies as it does for the original policies.
-/
theorem isAuthorized_eq_for_sound_policy_slice (req : Request) (entities : Entities) (slice policies : Policies) :
  IsSoundPolicySlice req entities slice policies →
  isAuthorized req entities slice = isAuthorized req entities policies
:= by
  intro h₀
  have hf : satisfiedPolicies .forbid slice req entities = satisfiedPolicies .forbid policies req entities :=
    satisfiedPolicies_eq_for_sound_policy_slice .forbid req entities slice policies h₀.left h₀.right
  have hp : satisfiedPolicies .permit slice req entities = satisfiedPolicies .permit policies req entities :=
    satisfiedPolicies_eq_for_sound_policy_slice .permit req entities slice policies h₀.left h₀.right
  unfold isAuthorized
  simp [hf, hp]

/--
A policy bound consists of optional `principal` and `resource` entities.
-/
structure PolicyBound where
  principalBound : Option EntityUID
  resourceBound  : Option EntityUID

def inSomeOrNone (uid : EntityUID) (opt : Option EntityUID) (entities : Entities) : Bool :=
  match opt with
  | .some uid' => inₑ uid uid' entities
  | .none      => true

/--
A bound is satisfied by a request and store if the request principal and
resource fields are descendents of the corresponding bound fields (or if those
bound fields are `none`).
-/
def satisfiedBound (bound : PolicyBound) (request : Request) (entities : Entities) : Bool :=
  inSomeOrNone request.principal bound.principalBound entities ∧
  inSomeOrNone request.resource bound.resourceBound entities

/--
A bound is sound for a given policy if the bound is satisfied for every
request and entities for which the policy is satisfied.
-/
def IsSoundPolicyBound (bound : PolicyBound) (policy : Policy) : Prop :=
  ∀ (request : Request) (entities : Entities),
  satisfied policy request entities →
  satisfiedBound bound request entities

/--
A bound analysis takes as input a policy and returns a PolicyBound.
-/
abbrev BoundAnalysis := Policy → PolicyBound

def BoundAnalysis.slice (ba : BoundAnalysis) (request : Request) (entities : Entities) (policies : Policies) : Policies :=
  policies.filter (fun policy => satisfiedBound (ba policy) request entities)

/--
A bound analysis is sound if it produces sound bounds for all policies.
-/
def IsSoundBoundAnalysis (ba : BoundAnalysis) : Prop :=
  ∀ (policy : Policy), IsSoundPolicyBound (ba policy) policy

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
    simp [List.subset_def]
    intro p h₂
    rw [List.mem_filter] at h₂
    simp [h₂]
  case right =>
    intro policy
    specialize h₁ policy
    intro h₂ h₃
    rw [List.mem_filter] at h₃
    simp [h₂] at h₃
    by_contra h₄
    unfold IsSoundPolicyBound at h₁
    specialize h₁ request entities h₄
    simp [h₃] at h₁

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
  intro request entities h₁
  unfold scopeAnalysis
  unfold satisfiedBound
  unfold Scope.bound
  unfold inSomeOrNone
  simp only [decide_eq_true_eq]
  apply And.intro
  case left =>
    generalize h₂ : policy.principalScope.scope = s
    cases s <;> simp <;>
    apply satisfied_implies_principal_scope h₁ <;>
    unfold Scope.bound <;> simp [h₂]
  case right =>
    generalize h₂ : policy.resourceScope.scope = s
    cases s <;> simp <;>
    apply satisfied_implies_resource_scope h₁ <;>
    unfold Scope.bound <;> simp [h₂]

/--
Scope-based bound analysis is sound.
-/
theorem scope_analysis_is_sound :
  IsSoundBoundAnalysis scopeAnalysis
:= by
  unfold IsSoundBoundAnalysis
  apply scope_bound_is_sound

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
