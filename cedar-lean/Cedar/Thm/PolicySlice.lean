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
import Cedar.Thm.Authorization.PolicySlice

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

open Cedar.Spec Cedar.Slice

/--
Policy slicing soundness: `isAuthorized` produces the same result for a sound
slice (subset) of a collection of policies as it does for the original policies.
-/
theorem isAuthorized_eq_for_sound_policy_slice (req : Request) (entities : Entities) (slice policies : Policies) :
  IsSoundPolicySlice req entities slice policies →
  isAuthorized req entities slice = isAuthorized req entities policies
:= by
  intro h₀
  have hf := satisfiedPolicies_eq_for_sound_policy_slice .forbid h₀
  have hp := satisfiedPolicies_eq_for_sound_policy_slice .permit h₀
  have he := errorPolicies_eq_for_sound_policy_slice h₀
  simp [isAuthorized, hf, hp, he]

/--
A sound bound analysis produces sound policy slices.
-/
theorem sound_bound_analysis_produces_sound_slices (ba : BoundAnalysis) (request : Request) (entities : Entities) (policies : Policies) :
  IsSoundBoundAnalysis ba →
  IsSoundPolicySlice request entities (ba.slice request entities policies) policies
:= by
  intro h₁
  unfold BoundAnalysis.slice
  exact sound_filter_produces_sound_slice policies
    (fun policy => (h₁ policy request entities).left)
    (fun policy => (h₁ policy request entities).right)

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

/-!
## Action-based slicing

The request action is known exactly, so action scopes admit a more precise
slice than the `inₑ`-based `PolicyBound` above: `isPolicyRelevantForAction` decides the
action scope constraint outright (`action_scope_eval_eq_isPolicyRelevantForAction`).
Concretely, `action == Action::"other"` is irrelevant unless the request action
*is* `Action::"other"`, whereas `action in Action::"other"` is relevant exactly
when `Action::"other"` is the request action or one of its ancestors.
-/

/--
The action scope analysis is monotone in its membership test: weakening the
test can only make more policies relevant. This is what lets an analysis with
incomplete ancestor information — such as the TPE slicer in
`Cedar.Thm.TPE.PolicySlice` — reuse the exact analysis's soundness proof
instead of redoing the case analysis over `ActionScope`.
-/
theorem isPolicyRelevantForActionBy_mono {f g : EntityUID → EntityUID → Bool} {action : EntityUID} {policy : Policy} :
  (∀ uid₁ uid₂, f uid₁ uid₂ = false → g uid₁ uid₂ = false) →
  isPolicyRelevantForActionBy f action policy = false →
  isPolicyRelevantForActionBy g action policy = false
:= by
  intro h_mono h_irr
  cases h₀ : policy.actionScope
  case actionInAny uids =>
    simp only [h₀, isPolicyRelevantForActionBy, List.any_eq_false, Bool.not_eq_true] at h_irr ⊢
    exact fun uid h_mem => h_mono _ _ (h_irr uid h_mem)
  case actionScope scope =>
    cases scope <;>
      simp only [h₀, isPolicyRelevantForActionBy] at h_irr ⊢
    case any => exact absurd h_irr (by simp)
    case eq uid => exact h_irr
    case mem uid => exact h_mono _ _ h_irr
    case is ety => exact h_irr
    case isMem ety uid =>
      simp only [Bool.and_eq_false_iff] at h_irr ⊢
      exact h_irr.imp id (h_mono _ _)

/--
Action-based slicing is sound.
-/
theorem action_slice_is_sound (request : Request) (entities : Entities) (policies : Policies) :
  IsSoundPolicySlice request entities (actionSlice request entities policies) policies
:= by
  unfold actionSlice
  exact sound_filter_produces_sound_slice policies
    (fun _ h => satisfied_implies_policy_relevant_for_action h)
    (fun _ h => error_implies_policy_relevant_for_action (if_hasError_then_exists_error h).choose_spec)

/--
Action-based slicing soundness: `isAuthorized` produces the same result for an
action-based slice of a collection of policies as it does for the original
policies.
-/
theorem isAuthorized_eq_for_action_based_policy_slice (request : Request) (entities : Entities) (policies : Policies) :
  isAuthorized request entities (actionSlice request entities policies) =
  isAuthorized request entities policies
:= by
  apply isAuthorized_eq_for_sound_policy_slice
  exact action_slice_is_sound request entities policies

/-!
### Consequences for the concrete action scope forms

The two cases called out above, stated directly in terms of membership in the
action-based slice.
-/

/--
`action == uid` is irrelevant unless the request action *is* `uid`. In
particular, being a descendent of `uid` does not make the policy relevant.
-/
theorem mem_action_slice_iff_eq_of_action_eq {policy : Policy} {request : Request} {entities : Entities} {policies : Policies} {uid : EntityUID} :
  policy ∈ policies →
  policy.actionScope = .actionScope (.eq uid) →
  (policy ∈ actionSlice request entities policies ↔ request.action = uid)
:= by
  intro h₀ h₁
  simp only [actionSlice, List.mem_filter, h₀, h₁, isPolicyRelevantForAction, isPolicyRelevantForActionBy, beq_iff_eq, true_and]

/--
`action in uid` is relevant exactly when `uid` is the request action or one of
its ancestors.
-/
theorem mem_action_slice_iff_inₑ_of_action_in {policy : Policy} {request : Request} {entities : Entities} {policies : Policies} {uid : EntityUID} :
  policy ∈ policies →
  policy.actionScope = .actionScope (.mem uid) →
  (policy ∈ actionSlice request entities policies ↔ inₑ request.action uid entities = true)
:= by
  intro h₀ h₁
  simp only [actionSlice, List.mem_filter, h₀, h₁, isPolicyRelevantForAction, isPolicyRelevantForActionBy, true_and]

/-!
## The combined slicing algorithm

`scopeSlice` is a single filter that applies both the principal/resource bound
analysis and the action scope analysis. It is exactly the composition of the
two slices above, and is therefore sound.
-/

/--
`scopeSlice` is the composition of the bound-based and action-based slices.
-/
theorem scopeSlice_eq_actionSlice_boundSlice (request : Request) (entities : Entities) (policies : Policies) :
  scopeSlice request entities policies =
  actionSlice request entities (BoundAnalysis.slice scopeAnalysis request entities policies)
:= by
  simp only [scopeSlice, actionSlice, BoundAnalysis.slice, List.filter_filter]
  congr 1
  funext policy
  exact Bool.and_comm _ _

/--
The combined slice is sound.
-/
theorem scope_slice_is_sound (request : Request) (entities : Entities) (policies : Policies) :
  IsSoundPolicySlice request entities (scopeSlice request entities policies) policies
:= by
  unfold scopeSlice
  apply sound_filter_produces_sound_slice policies <;>
  intro policy h <;>
  simp only [Bool.and_eq_true]
  case _ =>
    exact ⟨(scope_bound_is_sound policy request entities).left h,
            satisfied_implies_policy_relevant_for_action h⟩
  case _ =>
    exact ⟨(scope_bound_is_sound policy request entities).right h,
            error_implies_policy_relevant_for_action (if_hasError_then_exists_error h).choose_spec⟩

/--
Combined slicing soundness: `isAuthorized` produces the same result for the
full scope-based slice of a collection of policies as it does for the original
policies.
-/
theorem isAuthorized_eq_for_scope_slice (request : Request) (entities : Entities) (policies : Policies) :
  isAuthorized request entities (scopeSlice request entities policies) =
  isAuthorized request entities policies
:= by
  apply isAuthorized_eq_for_sound_policy_slice
  exact scope_slice_is_sound request entities policies

end Cedar.Thm
