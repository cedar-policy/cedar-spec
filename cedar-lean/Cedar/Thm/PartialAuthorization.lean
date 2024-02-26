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

import Cedar.Data.List
import Cedar.Data.Set
import Cedar.Spec.Response
import Cedar.Spec.Value
import Cedar.Spec.PartialAuthorizer
import Cedar.Spec.PartialResponse
import Cedar.Thm.PartialEval
import Cedar.Thm.PartialEval.And
import Cedar.Thm.Utils

/-! This file contains theorems about Cedar's partial evaluator. -/

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
  (resp.decision == .allow ∧ presp.decision == .allow ∨ resp.decision == .deny ∧ presp.decision == .deny) ∧
  presp.overapproximateDeterminingPolicies == resp.determiningPolicies ∧
  presp.underapproximateDeterminingPolicies == resp.determiningPolicies ∧
  Set.make (presp.errors.map Prod.fst) == resp.erroringPolicies
:= by
  unfold isAuthorizedPartial isAuthorized
  intro h₁ h₂
  repeat (any_goals (apply And.intro))
  case _ =>
    subst h₁ h₂
    simp [PartialResponse.decision]
    sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

/--
  Corollary to the above: partial-authorizing with concrete inputs gives a
  concrete decision.
-/
theorem partial_authz_on_concrete_gives_concrete {policies : Policies} {req : Request} {entities : Entities} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown
:= by
  intro h₁
  sorry

/--
  helper lemma
-/
theorem subs_doesn't_increase_residuals {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} {r : Residual} :
  req.subst subsmap = some req' →
  r ∈ (isAuthorizedPartial req' (entities.subst subsmap) policies).residuals →
  r ∈ (isAuthorizedPartial req entities policies).residuals
:= by
  intro h₁ h₂
  sorry

/--
  helper lemma
-/
theorem subs_preserves_true_residuals {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} {pid : PolicyID} {effect : Effect} :
  req.subst subsmap = some req' →
  Residual.residual pid effect (.lit (.bool true)) ∈ (isAuthorizedPartial req entities policies).residuals →
  Residual.residual pid effect (.lit (.bool true)) ∈ (isAuthorizedPartial req' (entities.subst subsmap) policies).residuals
:= by
  sorry

/--
  helper lemma
  maybe corollary of above?
-/
theorem subs_preserves_knownPermits {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} {pid : PolicyID} :
  req.subst subsmap = some req' →
  pid ∈ (isAuthorizedPartial req entities policies).knownPermits →
  pid ∈ (isAuthorizedPartial req' (entities.subst subsmap) policies).knownPermits
:= by
  unfold PartialResponse.knownPermits
  intro h₁ h₂
  sorry

/--
  helper lemma
  NOTE: SUSPECT NOT TRUE IN THIS FORMULATION
  substitutions can create new knownPermits or knownForbids, even if the decision was already known
-/
theorem partial_authz_decision_concrete_then_true_residuals_agnostic' {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} {pid : PolicyID} {effect : Effect} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  Residual.residual pid effect (.lit (.bool true)) ∈ (isAuthorizedPartial req' (entities.subst subsmap) policies).residuals →
  Residual.residual pid effect (.lit (.bool true)) ∈ (isAuthorizedPartial req entities policies).residuals
:= by
  sorry

/--
  helper lemma
-/
theorem partial_authz_decision_concrete_then_knownPermits_unknown_agnostic {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).knownPermits.isEmpty = (isAuthorizedPartial req' (entities.subst subsmap) policies).knownPermits.isEmpty
:= by
  intro h₁ h₂
  cases h₃ : (isAuthorizedPartial req entities policies).knownPermits.isEmpty
  case true =>
    unfold PartialResponse.knownPermits at *
    simp at *
    apply Eq.symm
    apply (Set.make_empty _).mp
    rw [← Set.make_empty] at h₃
    simp [List.filterMap_empty_iff_f_returns_none] at *
    intro r
    specialize h₃ r
    intro h₄
    split <;> simp
    rename_i r pid
    replace h₄ := partial_authz_decision_concrete_then_true_residuals_agnostic' h₁ h₂ h₄
    specialize h₃ h₄
    simp at h₃
  case false =>
    unfold PartialResponse.knownPermits at *
    simp at *
    apply Eq.symm
    rw [← Set.make_non_empty] at *
    intro h₄
    simp [List.filterMap_empty_iff_f_returns_none] at h₄
    simp [List.filterMap_nonempty_iff_exists_f_returns_some] at h₃
    replace ⟨r, ⟨h₃, h₅⟩⟩ := h₃
    specialize h₄ r
    simp [Option.isSome] at h₅
    split at h₅ <;> simp at h₅
    clear h₅
    rename_i optid pid h₅
    split at h₅ <;> simp at h₅
    subst h₅
    rename_i r pid
    simp at h₄
    apply h₄ ; clear h₄
    apply subs_preserves_true_residuals h₂ h₃

/--
  helper lemma
-/
theorem partial_authz_decision_concrete_then_knownForbids_unknown_agnostic {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).knownForbids.isEmpty = (isAuthorizedPartial req' (entities.subst subsmap) policies).knownForbids.isEmpty
:= by
  intro h₁ h₂
  cases h₃ : (isAuthorizedPartial req entities policies).knownForbids.isEmpty
  case true =>
    unfold PartialResponse.knownForbids at *
    simp at *
    apply Eq.symm
    apply (Set.make_empty _).mp
    rw [← Set.make_empty] at h₃
    simp [List.filterMap_empty_iff_f_returns_none] at *
    intro r
    specialize h₃ r
    intro h₄
    split <;> simp
    rename_i r pid
    replace h₄ := partial_authz_decision_concrete_then_true_residuals_agnostic' h₁ h₂ h₄
    specialize h₃ h₄
    simp at h₃
  case false =>
    unfold PartialResponse.knownForbids at *
    simp at *
    apply Eq.symm
    rw [← Set.make_non_empty] at *
    intro h₄
    simp [List.filterMap_empty_iff_f_returns_none] at h₄
    simp [List.filterMap_nonempty_iff_exists_f_returns_some] at h₃
    replace ⟨r, ⟨h₃, h₅⟩⟩ := h₃
    specialize h₄ r
    simp [Option.isSome] at h₅
    split at h₅ <;> simp at h₅
    clear h₅
    rename_i optid pid h₅
    split at h₅ <;> simp at h₅
    subst h₅
    rename_i r pid
    simp at h₄
    apply h₄ ; clear h₄
    apply subs_preserves_true_residuals h₂ h₃

/--
  helper lemma
-/
theorem subs_preserves_empty_permits {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).permits.isEmpty →
  (isAuthorizedPartial req' (entities.subst subsmap) policies).permits.isEmpty
:= by
  intro h₁ h₂
  unfold PartialResponse.permits at *
  simp at *
  apply (Set.make_empty _).mp
  rw [← Set.make_empty] at h₂
  simp [List.filterMap_empty_iff_f_returns_none] at *
  intro r
  specialize h₂ r
  intro h₃
  split <;> simp
  rename_i r pid cond
  simp at h₂
  apply h₂ ; clear h₂
  apply subs_doesn't_increase_residuals h₁
  assumption

/--
  helper lemma
-/
theorem subs_preserves_empty_forbids {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).forbids.isEmpty →
  (isAuthorizedPartial req' (entities.subst subsmap) policies).forbids.isEmpty
:= by
  intro h₁ h₂
  unfold PartialResponse.forbids at *
  simp at *
  apply (Set.make_empty _).mp
  rw [← Set.make_empty] at h₂
  simp [List.filterMap_empty_iff_f_returns_none] at *
  intro r
  specialize h₂ r
  intro h₃
  split <;> simp
  rename_i r pid cond
  simp at h₂
  apply h₂ ; clear h₂
  apply subs_doesn't_increase_residuals h₁
  assumption

/--
  helper lemma
  If partial authorization returns a concrete decision, there must be either
  at least one knownForbid, or at least one knownPermit
-/
theorem partial_authz_decision_concrete_then_kf_or_kp {resp : PartialResponse} :
  resp.decision ≠ .unknown →
  ¬ resp.knownForbids.isEmpty ∨ ¬ resp.knownPermits.isEmpty
:= by
  sorry

/--
  helper lemma
-/
theorem in_knownPermits_in_permits {resp : PartialResponse} {id : PolicyID} :
  id ∈ resp.knownPermits → id ∈ resp.permits
:= by
  sorry

/--
  helper lemma
  nearly the inverse of its namesake, but requires an extra condition
-/
theorem partial_authz_decision_concrete_no_known_forbids_then_must_be_permits_after_any_sub {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).knownForbids.isEmpty →
  ¬ (isAuthorizedPartial req' (entities.subst subsmap) policies).permits.isEmpty
:= by
  intro h₁ h₂ h₃
  cases partial_authz_decision_concrete_then_kf_or_kp h₁
  case inl h₄ => contradiction
  case inr h₄ =>
    replace ⟨kp, h₄⟩ := (Set.non_empty_iff_exists _).mp h₄
    apply (Set.non_empty_iff_exists _).mpr
    exists kp
    apply in_knownPermits_in_permits
    apply subs_preserves_knownPermits h₂
    assumption

/--
  If partial authorization returns a concrete decision, then that decision is
  identical to the decision you'd get with any (valid) substitution for the
  unknowns.
-/
theorem partial_authz_decision_concrete_then_unknown_agnostic {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).decision = (isAuthorizedPartial req' (entities.subst subsmap) policies).decision
:= by
  intro h₁ h₂
  have h₃ := partial_authz_decision_concrete_then_knownPermits_unknown_agnostic h₁ h₂
  have h₄ := partial_authz_decision_concrete_then_knownForbids_unknown_agnostic h₁ h₂
  unfold PartialResponse.decision
  rw [← h₃, ← h₄] ; clear h₃ h₄
  simp
  cases h₃ : (isAuthorizedPartial req entities policies).knownForbids.isEmpty
  case false => simp
  case true =>
    simp
    cases h₄ : (isAuthorizedPartial req entities policies).permits.isEmpty
    case true =>
      have h₅ := subs_preserves_empty_permits h₂ h₄
      simp [h₅]
    case false =>
      simp
      cases h₅ : (isAuthorizedPartial req entities policies).forbids.isEmpty
      case false =>
        exfalso
        apply h₁
        unfold PartialResponse.decision
        simp [*]
      case true =>
        have h₇ := subs_preserves_empty_forbids h₂ h₅
        have h₈ := partial_authz_decision_concrete_no_known_forbids_then_must_be_permits_after_any_sub h₁ h₂ h₃
        simp [h₇, h₈]
