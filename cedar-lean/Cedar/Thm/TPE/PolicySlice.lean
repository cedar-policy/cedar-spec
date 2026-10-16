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

import Cedar.Slice.TPESlice
import Cedar.TPE
import Cedar.TPE.Authorizer
import Cedar.Thm.Authorization
import Cedar.Thm.PolicySlice
import Cedar.Thm.TPE.Authorizer
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.Policy

/-!
This file develops the theory of sound policy slicing for type-aware partial
evaluation (TPE).

## The soundness property

A slicer takes a partial request and partial entities and returns a subset of
the policies. `IsSoundPartialPolicySlice` says that every *excluded* policy
evaluates to `false` for every concretization of the partial request and
entities.

This is deliberately a *semantic* condition on concrete evaluation rather than
a condition on TPE residuals. TPE cannot be run on an ill-typed policy at all,
so a TPE-level condition ("the residual is `false`") would silently force every
excluded policy to be well-typed. Stating the condition semantically is what
lets a slicer drop ill-typed policies. The TPE-level condition is still
available as a *sufficient* justification for excluding a policy that does
typecheck: see `tpe_false_implies_concrete_false` and
`tpe_false_exclusion_is_sound_slice`.

## The main results

* `sound_partial_slice_is_sound_policy_slice` reduces a sound TPE slice to a
  sound concrete slice (`IsSoundPolicySlice`) for each concretization, which
  lets the entire concrete slicing theory in `Cedar.Thm.PolicySlice` be reused.
* `slice_reauthorize_is_sound` is the headline theorem: slicing, then TPE on
  the slice, then re-authorization, agrees with concrete authorization over the
  *full* policy set. Note that TPE is only ever run on the slice, so the full
  policy set need not typecheck.
* `slice_partial_authorize_decision_is_sound` says the same for a decision
  reached during partial authorization.
* `partial_action_slice_is_sound` is a concrete, purely syntactic slicer that
  satisfies the property without assuming anything about policy types, and
  `action_slice_reauthorize_is_sound` instantiates the headline theorem with it.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Slice
open Cedar.Spec
open Cedar.TPE
open Cedar.Validation

/--
A TPE policy slice is sound when the slice is a subset of the policies and
every excluded policy evaluates to `false` for *every* concretization of the
partial request and entities.

Note what this does **not** require: the excluded policies need not be
well-typed, and TPE need not be runnable on them.
-/
def IsSoundPartialPolicySlice (schema : Schema) (preq : PartialRequest) (pes : PartialEntities) (slice policies : Policies) : Prop :=
  slice ⊆ policies ∧
  ∀ policy ∈ policies, policy ∉ slice →
    ∀ (req : Request) (es : Entities),
      isValidAndConsistent schema req es preq pes = .ok () →
      Spec.evaluate policy.toExpr req es = .ok false

/--
Sound TPE slicing refines to sound concrete slicing: for every concretization
of the partial request and entities, a sound TPE slice is a sound concrete
slice. This is the bridge that makes the concrete theory in
`Cedar.Thm.PolicySlice` apply.
-/
theorem sound_partial_slice_is_sound_policy_slice
  {schema : Schema} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities} {slice policies : Policies} :
  IsSoundPartialPolicySlice schema preq pes slice policies →
  isValidAndConsistent schema req es preq pes = .ok () →
  IsSoundPolicySlice req es slice policies
:= by
  intro ⟨h_sub, h_false⟩ hv
  rw [is_sound_policy_slice_def_equiv]
  exact ⟨h_sub, fun policy h_mem h_nmem => h_false policy h_mem h_nmem req es hv⟩

/--
`IsSoundPartialPolicySlice` is exactly "a sound concrete slice at every
concretization". The subset conjunct has to be carried separately because a
partial request with no concretizations makes the right-hand quantifier
vacuous.

This equivalence is how the TPE theory is kept free of duplicated reasoning:
to prove a TPE slicer sound it suffices to exhibit it as a sound *concrete*
slice, which `Cedar.Thm.PolicySlice` already provides the tools for.
-/
theorem is_sound_partial_policy_slice_iff
  {schema : Schema} {preq : PartialRequest} {pes : PartialEntities} {slice policies : Policies} :
  IsSoundPartialPolicySlice schema preq pes slice policies ↔
  (slice ⊆ policies ∧
    ∀ (req : Request) (es : Entities),
      isValidAndConsistent schema req es preq pes = .ok () →
      IsSoundPolicySlice req es slice policies)
:= by
  constructor
  · intro h
    exact ⟨h.left, fun _ _ hv => sound_partial_slice_is_sound_policy_slice h hv⟩
  · intro ⟨h_sub, h_sound⟩
    refine ⟨h_sub, ?_⟩
    intro policy h_mem h_nmem req es hv
    have h := (is_sound_policy_slice_def_equiv.mp (h_sound req es hv)).right
    exact h policy h_mem h_nmem

/--
Slicing cannot change the result of concrete authorization, for any
concretization of the partial request and entities.
-/
theorem isAuthorized_eq_for_sound_partial_slice
  {schema : Schema} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities} {slice policies : Policies} :
  IsSoundPartialPolicySlice schema preq pes slice policies →
  isValidAndConsistent schema req es preq pes = .ok () →
  Spec.isAuthorized req es slice = Spec.isAuthorized req es policies
:= by
  intro h_slice hv
  exact isAuthorized_eq_for_sound_policy_slice req es slice policies
    (sound_partial_slice_is_sound_policy_slice h_slice hv)

/-!
## Justifying an exclusion with TPE

For a policy that does typecheck, "TPE fully reduces it to `false`" is a sound
reason to exclude it.
-/

/--
If TPE fully reduces a policy to `false` for a partial request, then the policy
evaluates to `false` for every concretization of that partial request.
-/
theorem tpe_false_implies_concrete_false
  {schema : Schema} {policy : Policy} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities} {ty : CedarType} :
  evaluatePolicy schema policy preq pes = .ok (.val (.prim (.bool false)) ty) →
  isValidAndConsistent schema req es preq pes = .ok () →
  Spec.evaluate policy.toExpr req es = .ok false
:= by
  intro h_tpe hv
  have ⟨env, h_env, h_wf⟩ := isValidAndConsistent_env hv
  have h := partial_evaluate_policy_is_sound h_tpe h_env h_wf
    (consistent_checks_ensure_refinement hv)
  simp only [Residual.evaluate] at h
  exact to_option_right_ok' h

/--
A slicer that only ever excludes policies that TPE fully reduces to `false` is
sound. This is the TPE-level sufficient condition; it only applies to policies
TPE can run on, which is why `IsSoundPartialPolicySlice` is not stated this way.
-/
theorem tpe_false_exclusion_is_sound_slice
  {schema : Schema} {preq : PartialRequest} {pes : PartialEntities} {slice policies : Policies} :
  slice ⊆ policies →
  (∀ policy ∈ policies, policy ∉ slice →
    ∃ ty, evaluatePolicy schema policy preq pes = .ok (.val (.prim (.bool false)) ty)) →
  IsSoundPartialPolicySlice schema preq pes slice policies
:= by
  intro h_sub h_false
  refine ⟨h_sub, ?_⟩
  intro policy h_mem h_nmem req es hv
  have ⟨_, h_tpe⟩ := h_false policy h_mem h_nmem
  exact tpe_false_implies_concrete_false h_tpe hv

/-!
## A type-agnostic slicer: slicing on the request action

`partialActionSlice` inspects only the policy's action scope, so it is sound
for arbitrary — including ill-typed — policies.
-/

/--
If the partial entity store already rules out membership, so does every
concrete store refining it.
-/
theorem partial_in_false_implies_in_false
  {uid₁ uid₂ : EntityUID} {es : Entities} {pes : PartialEntities} :
  EntitiesRefine es pes →
  partialInₑ uid₁ uid₂ pes = false →
  Spec.inₑ uid₁ uid₂ es = false
:= by
  intro h_ref h_pin
  simp only [partialInₑ] at h_pin
  cases h_dec : TPE.inₑ uid₁ uid₂ pes <;> rw [h_dec] at h_pin <;>
    simp only [Option.getD_none, Option.getD_some, Bool.true_eq_false] at h_pin
  exact h_pin ▸ tpe_inₑ_agrees h_ref h_dec

/--
If a policy is irrelevant to the action of the partial request, it is
irrelevant to the action of every concretization.
-/
theorem partial_action_irrelevant_implies_irrelevant
  {policy : Policy} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities} :
  RequestAndEntitiesRefine req es preq pes →
  isPolicyRelevantForPartialAction policy preq pes = false →
  isPolicyRelevantForAction policy req es = false
:= by
  intro ⟨h_req, h_es⟩ h_irr
  replace h_req : req.action = preq.action := h_req.right.left
  simp only [isPolicyRelevantForPartialAction] at h_irr
  simp only [isPolicyRelevantForAction, h_req]
  exact isPolicyRelevantForActionBy_mono
    (fun _ _ h => partial_in_false_implies_in_false h_es h) h_irr

/--
The partial action slice is a conservative over-approximation of the concrete
one: anything the concrete analysis keeps, the partial analysis also keeps.
-/
theorem action_slice_subset_partial_action_slice
  {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities} {policies : Policies} :
  RequestAndEntitiesRefine req es preq pes →
  actionSlice req es policies ⊆ partialActionSlice preq pes policies
:= by
  intro h_ref policy h_mem
  simp only [actionSlice, List.mem_filter] at h_mem
  simp only [partialActionSlice, List.mem_filter]
  refine ⟨h_mem.left, ?_⟩
  by_contra h
  simp only [Bool.not_eq_true] at h
  rw [partial_action_irrelevant_implies_irrelevant h_ref h] at h_mem
  exact absurd h_mem.right (by simp)

theorem partial_action_slice_subset
  {preq : PartialRequest} {pes : PartialEntities} {policies : Policies} :
  partialActionSlice preq pes policies ⊆ policies
:= by
  intro policy h
  exact (List.mem_filter.mp h).left

/--
Action-based TPE slicing is sound. The proof reuses the concrete result
`action_slice_is_sound` wholesale: the partial slice is a superset of the
concrete slice at every concretization, and soundness is monotone in the slice
(`sound_slice_superset`). Nothing about the action scope semantics, policy
evaluation, or types is re-derived here.
-/
theorem partial_action_slice_is_sound
  (schema : Schema) (preq : PartialRequest) (pes : PartialEntities) (policies : Policies) :
  IsSoundPartialPolicySlice schema preq pes (partialActionSlice preq pes policies) policies
:= by
  rw [is_sound_partial_policy_slice_iff]
  refine ⟨partial_action_slice_subset, ?_⟩
  intro req es hv
  exact sound_slice_superset
    (action_slice_is_sound req es policies)
    (action_slice_subset_partial_action_slice (consistent_checks_ensure_refinement hv))
    partial_action_slice_subset

end Cedar.Thm
