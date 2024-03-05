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

import Cedar.Spec.Response
import Cedar.Spec.Value
import Cedar.Spec.PartialAuthorizer
import Cedar.Spec.PartialResponse
import Cedar.Spec.PartialValue
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.PartialEval
import Cedar.Thm.PartialEval.And
import Cedar.Thm.PartialAuthorization.PartialAuthorization
import Cedar.Thm.PartialAuthorization.PartialResponse
import Cedar.Thm.Utils

/-! This file contains toplevel theorems about Cedar's partial authorizer. -/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Except

/--
  Partial-authorizing with concrete inputs gives the same concrete outputs as
  concrete-authorizing with those inputs.
-/
theorem partial_authz_eqv_authz_on_concrete {policies : Policies} {req : Request} {entities : Entities} {presp : PartialResponse} {resp : Response} :
  isAuthorized req entities policies = resp →
  isAuthorizedPartial req entities policies = presp →
  (resp.decision = .allow ∧ presp.decision = .allow ∨ resp.decision = .deny ∧ presp.decision = .deny) ∧
  presp.overapproximateDeterminingPolicies = resp.determiningPolicies ∧
  presp.underapproximateDeterminingPolicies = resp.determiningPolicies ∧
  Set.make (presp.errors.map Prod.fst) = resp.erroringPolicies
:= by
  intro h₁ h₂
  subst h₁ h₂
  repeat (any_goals (apply And.intro))
  case _ =>
    simp [isAuthorized, PartialResponse.decision]
    simp only [knownForbids_eq_forbids_on_concrete]
    simp only [forbids_empty_iff_no_satisfied_forbids_on_concrete]
    simp only [forbids_nonempty_iff_satisfied_forbids_nonempty_on_concrete]
    cases h₁ : (satisfiedPolicies .forbid policies req entities).isEmpty
    case false => simp
    case true =>
      simp [h₁]
      simp only [permits_empty_iff_no_satisfied_permits_on_concrete]
      simp only [knownPermits_eq_permits_on_concrete]
      cases h₂ : (satisfiedPolicies .permit policies req entities).isEmpty
      case false => simp [h₂, permits_empty_iff_no_satisfied_permits_on_concrete]
      case true => simp [h₁, h₂, permits_nonempty_iff_satisfied_permits_nonempty_on_concrete]
  case _ =>
    -- use overapproximate_determining_iff_determining_after_subst
    sorry
  case _ =>
    -- use underapproximate_determining_iff_determining_after_subst
    sorry
  case _ =>
    -- the RHS of the goal should simplify to `errorPolicies policies req entities`, but `simp` doesn't accomplish that by itself
    sorry

/--
  Corollary to the above: partial-authorizing with concrete inputs gives a
  concrete decision.
-/
theorem partial_authz_on_concrete_gives_concrete {policies : Policies} {req : Request} {entities : Entities} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown
:= by
  intro h₁
  have h₂ := partial_authz_eqv_authz_on_concrete (policies := policies) (req := req) (entities := entities) (presp := isAuthorizedPartial req entities policies) (resp := isAuthorized req entities policies)
  simp at h₂
  replace ⟨h₂, h₃, h₄, h₅⟩ := h₂ ; clear h₃ h₄ h₅
  cases h₃ : (isAuthorized req entities policies).decision
  case allow =>
    simp [h₃] at h₂
    simp [h₂] at h₁
  case deny =>
    simp [h₃] at h₂
    simp [h₂] at h₁

/--
  Partial-authorizing with any partial inputs, then performing any (valid)
  substitution for the unknowns and authorizing using the residuals, gives the
  same result as first performing the substitution and then authorizing using
  the original policies.

  Also implied by this: if a substitution is valid for the PartialRequest, then
  it is valid for `reEvaluateWithSubst`
-/
theorem authz_on_residuals_eqv_substituting_first {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String RestrictedPartialValue} :
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).reEvaluateWithSubst subsmap = isAuthorizedPartial req' (entities.subst subsmap) policies
:= by
  sorry

/--
  If partial authorization returns a concrete decision, then that decision is
  identical to the decision you'd get with any (valid) substitution for the
  unknowns.
-/
theorem partial_authz_decision_concrete_then_unknown_agnostic {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String RestrictedPartialValue} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).decision = (isAuthorizedPartial req' (entities.subst subsmap) policies).decision
:= by
  intro h₁ h₂
  cases h₃ : (isAuthorizedPartial req entities policies).knownForbids.isEmpty
  case false =>
    rw [if_knownForbids_then_deny_after_any_sub (by simp [h₃]) h₂]
    unfold PartialResponse.decision
    simp [h₃]
  case true =>
    unfold PartialResponse.decision
    simp [h₃]
    have h₄ := partial_authz_decision_concrete_no_knownForbids_then_knownPermits_unknown_agnostic h₁ h₂ h₃
    rw [← h₄] ; clear h₄
    cases h₄ : (isAuthorizedPartial req entities policies).permits.isEmpty
    case true =>
      have h₅ := subs_preserves_empty_permits h₂ h₄
      simp [h₅]
    case false =>
      simp [h₄]
      cases h₅ : (isAuthorizedPartial req entities policies).forbids.isEmpty
      case false =>
        exfalso
        apply h₁
        unfold PartialResponse.decision
        simp [*]
      case true =>
        have h₇ := subs_preserves_empty_forbids h₂ h₅
        simp [h₇]
        have h₈ := partial_authz_decision_concrete_no_knownForbids_some_permits_then_must_be_permits_after_any_sub h₁ h₂ h₃ (by simp [h₄])
        simp [h₈]
        have h₉ := partial_authz_decision_concrete_no_knownForbids_some_permits_then_no_knownForbids_after_any_sub h₁ h₂ h₃ (by simp [h₄])
        simp [h₉]

/--
  If partial authorization returns an .unknown decision, then there is some
  substitution for the unknowns under which you get Allow, and some substitution
  for the unknowns under which you get Deny.
-/
theorem partial_authz_decision_unknown_then_allow_deny_possible {policies : Policies} {req : PartialRequest} {entities : PartialEntities} :
  (isAuthorizedPartial req entities policies).decision = .unknown →
  (∃ req' subsmap, req.subst subsmap = some req' ∧ (isAuthorizedPartial req' (entities.subst subsmap) policies).decision = .allow) ∧
  (∃ req' subsmap, req.subst subsmap = some req' ∧ (isAuthorizedPartial req' (entities.subst subsmap) policies).decision = .deny)
:= by
  sorry

/--
  A policy P is included in `overapproximateDeterminingPolicies` iff
  there is some substitution such that P is a determining policy
-/
theorem overapproximate_determining_iff_determining_after_subst {policies : Policies} {req : PartialRequest} {entities : PartialEntities} {pid : PolicyID} :
  pid ∈ (isAuthorizedPartial req entities policies).overapproximateDeterminingPolicies ↔
  ∃ req' entities' subsmap,
    req.fullSubst subsmap = some req' ∧
    entities.fullSubst subsmap = some entities' ∧
    pid ∈ (isAuthorized req' entities' policies).determiningPolicies
:= by
  sorry

/--
  A policy P is included in `underapproximateDeterminingPolicies` iff
  for all substitutions, P is a determining policy
-/
theorem underapproximate_determining_iff_determining_after_subst {policies : Policies} {req : PartialRequest} {entities : PartialEntities} {pid : PolicyID} :
  pid ∈ (isAuthorizedPartial req entities policies).overapproximateDeterminingPolicies ↔
  ∀ req' entities' subsmap,
    req.fullSubst subsmap = some req' →
    entities.fullSubst subsmap = some entities' →
    pid ∈ (isAuthorized req' entities' policies).determiningPolicies
:= by
  sorry
