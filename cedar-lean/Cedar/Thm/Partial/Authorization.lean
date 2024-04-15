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

import Cedar.Partial.Authorizer
import Cedar.Partial.Response
import Cedar.Partial.Value
import Cedar.Spec.Response
import Cedar.Spec.Value
import Cedar.Thm.Authorization.Authorizer
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation
import Cedar.Thm.Partial.Evaluation.And
import Cedar.Thm.Partial.Authorization.PartialAuthorization
import Cedar.Thm.Partial.Authorization.PartialResponse
import Cedar.Thm.Utils

/-! This file contains toplevel theorems about Cedar's partial authorizer. -/

namespace Cedar.Thm.Partial.Authorization

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec
open Except

/--
  Partial-authorizing with any partial inputs, then performing any (valid)
  substitution for the unknowns and authorizing using the residuals, gives the
  same result as first performing the substitution and then authorizing using
  the original policies.

  Also implied by this: if a substitution is valid for the Partial.Request, then
  it is valid for `reEvaluateWithSubst`
-/
theorem authz_on_residuals_eqv_substituting_first {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} :
  req.subst subsmap = some req' →
  (Partial.isAuthorized req entities policies).reEvaluateWithSubst subsmap = Partial.isAuthorized req' (entities.subst subsmap) policies
:= by
  intro h₁
  unfold Partial.Response.reEvaluateWithSubst Partial.isAuthorized
  simp
  apply And.intro h₁
  rw [List.filterMap_filterMap]
  apply List.filterMap_congr
  intro policy h₂
  have h₃ := Partial.Evaluation.eval_on_residuals_eqv_substituting_first h₁ (expr := policy.toExpr) (entities := entities)
  simp [Option.bind]
  -- TODO: desugar the do-let in h₃ to show its LHS matches the LHS of the goal (which explicitly written with match-on-match and `fun residual`).
  -- or maneuver so the goal is written in do-let form, but that seems harder.
  sorry

/--
  If partial authorization returns a concrete decision, then that decision is
  identical to the decision you'd get with any (valid) substitution for the
  unknowns.
-/
theorem partial_authz_decision_concrete_then_unknown_agnostic {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map String Partial.RestrictedValue} :
  (Partial.isAuthorized req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (Partial.isAuthorized req entities policies).decision = (Partial.isAuthorized req' (entities.subst subsmap) policies).decision
:= by
  intro h₁ h₂
  have wf : entities.AllWellFormed := by sorry -- TODO: can we establish this somehow, or do we need to admit this as a top-level assumption for this theorem?
  have rcu_e : Partial.Entities.ResidualsContainUnknowns entities := by sorry -- TODO: can we establish this somehow, or do we need to admit this as a top-level assumption for this theorem?
  have rcu_r : Partial.Request.ResidualsContainUnknowns req := by sorry -- TODO: can we establish this somehow, or do we need to admit this as a top-level assumption for this theorem?
  cases h₃ : (Partial.isAuthorized req entities policies).knownForbids.isEmpty
  case false =>
    rw [if_knownForbids_then_deny_after_any_sub wf rcu_e rcu_r (by simp [h₃]) h₂]
    unfold Partial.Response.decision
    simp [h₃]
  case true =>
    unfold Partial.Response.decision
    simp [h₃]
    have h₄ := partial_authz_decision_concrete_no_knownForbids_then_knownPermits_unknown_agnostic wf rcu_e rcu_r h₁ h₂ h₃
    rw [← h₄] ; clear h₄
    cases h₄ : (Partial.isAuthorized req entities policies).permits.isEmpty
    case true =>
      have h₅ := subst_preserves_empty_permits h₂ h₄
      simp [h₅]
    case false =>
      simp [h₄]
      cases h₅ : (Partial.isAuthorized req entities policies).forbids.isEmpty
      case false =>
        exfalso
        apply h₁
        unfold Partial.Response.decision
        simp [*]
      case true =>
        have h₇ := subst_preserves_empty_forbids h₂ h₅
        simp [h₇]
        have h₈ := partial_authz_decision_concrete_no_knownForbids_some_permits_then_must_be_permits_after_any_sub wf rcu_e rcu_r h₁ h₂ h₃ (by simp [h₄])
        simp [h₈]
        have h₉ := partial_authz_decision_concrete_no_knownForbids_some_permits_then_no_knownForbids_after_any_sub h₁ h₂ h₃ (by simp [h₄])
        simp [h₉]

/--
  If partial authorization returns an .unknown decision, then there is some
  substitution for the unknowns under which you get Allow, and some substitution
  for the unknowns under which you get Deny.
-/
theorem partial_authz_decision_unknown_then_allow_deny_possible {policies : Policies} {req : Partial.Request} {entities : Partial.Entities} :
  (Partial.isAuthorized req entities policies).decision = .unknown →
  (∃ req' subsmap, req.subst subsmap = some req' ∧ (Partial.isAuthorized req' (entities.subst subsmap) policies).decision = .allow) ∧
  (∃ req' subsmap, req.subst subsmap = some req' ∧ (Partial.isAuthorized req' (entities.subst subsmap) policies).decision = .deny)
:= by
  sorry

/--
  A policy P is included in `overapproximateDeterminingPolicies` iff
  there is some (full) substitution such that P is a determining policy
-/
theorem overapproximate_determining_iff_determining_after_subst {policies : Policies} {req : Partial.Request} {entities : Partial.Entities} {pid : PolicyID} :
  pid ∈ (Partial.isAuthorized req entities policies).overapproximateDeterminingPolicies ↔
  ∃ req' entities' subsmap,
    req.fullSubst subsmap = some req' ∧
    entities.fullSubst subsmap = some entities' ∧
    pid ∈ (isAuthorized req' entities' policies).determiningPolicies
:= by
  sorry

/--
  A policy P is included in `underapproximateDeterminingPolicies` iff
  for all (full) substitutions, P is a determining policy
-/
theorem underapproximate_determining_iff_determining_after_subst {policies : Policies} {req : Partial.Request} {entities : Partial.Entities} {pid : PolicyID} :
  pid ∈ (Partial.isAuthorized req entities policies).underapproximateDeterminingPolicies ↔
  ∀ req' entities' subsmap,
    req.fullSubst subsmap = some req' →
    entities.fullSubst subsmap = some entities' →
    pid ∈ (isAuthorized req' entities' policies).determiningPolicies
:= by
  simp only [Partial.Response.underapproximateDeterminingPolicies, isAuthorized]
  constructor
  case mp =>
    intro h₁ req' entities' subsmap h₂ h₃
    split <;> simp
    case inl h₄ =>
      simp at h₄
      replace ⟨h₄, h₅⟩ := h₄
      -- next step: since there are no forbids after fullSubst (h₄), there are no knownForbids before subst, so that simplifies h₁
      sorry
    case inr h₄ =>
      simp at h₄
      sorry
  case mpr =>
    intro h₁
    sorry

/--
  Partial-authorizing with concrete inputs gives the same concrete outputs as
  concrete-authorizing with those inputs.
-/
theorem partial_authz_eqv_authz_on_concrete {policies : Policies} {req : Request} {entities : Entities} {presp : Partial.Response} {resp : Response}
  (wf : req.WellFormed) :
  isAuthorized req entities policies = resp →
  Partial.isAuthorized req entities policies = presp →
  (resp.decision = .allow ∧ presp.decision = .allow ∨ resp.decision = .deny ∧ presp.decision = .deny) ∧
  presp.overapproximateDeterminingPolicies = resp.determiningPolicies ∧
  presp.underapproximateDeterminingPolicies = resp.determiningPolicies ∧
  Set.make (presp.errors.map Prod.fst) = resp.erroringPolicies
:= by
  intro h₁ h₂
  subst h₁ h₂
  repeat (any_goals (apply And.intro))
  case _ =>
    simp [isAuthorized, Partial.Response.decision]
    simp only [PartialOnConcrete.knownForbids_eq_forbids wf]
    simp only [PartialOnConcrete.forbids_empty_iff_no_satisfied_forbids wf]
    simp only [PartialOnConcrete.forbids_nonempty_iff_satisfied_forbids_nonempty wf]
    cases h₁ : (satisfiedPolicies .forbid policies req entities).isEmpty
    case false => simp
    case true =>
      simp [h₁]
      simp only [PartialOnConcrete.permits_empty_iff_no_satisfied_permits wf]
      simp only [PartialOnConcrete.knownPermits_eq_permits wf]
      cases h₂ : (satisfiedPolicies .permit policies req entities).isEmpty
      case false => simp [h₂, PartialOnConcrete.permits_empty_iff_no_satisfied_permits wf]
      case true => simp [h₁, h₂, PartialOnConcrete.permits_nonempty_iff_satisfied_permits_nonempty wf]
  case _ =>
    rw [← Set.eq_means_eqv Partial.Response.overapproximateDeterminingPolicies_wf determiningPolicies_wf]
    unfold List.Equiv
    simp only [List.subset_def]
    constructor
    case left =>
      intro pid h₁
      rw [Set.in_list_iff_in_set] at *
      rw [overapproximate_determining_iff_determining_after_subst] at h₁
      replace ⟨req', entities', subsmap, h₁, h₂, h₃⟩ := h₁
      sorry
    case right =>
      intro pid h₁
      rw [Set.in_list_iff_in_set] at *
      rw [overapproximate_determining_iff_determining_after_subst]
      sorry
  case _ =>
    -- use underapproximate_determining_iff_determining_after_subst
    sorry
  case _ =>
    simp only [isAuthorized, Bool.and_eq_true, Bool.not_eq_true']
    cases (satisfiedPolicies .forbid policies req entities).isEmpty <;>
    cases (satisfiedPolicies .permit policies req entities).isEmpty <;>
    simp only [and_true, and_false, ite_true, ite_false] <;>
    exact PartialOnConcrete.errors_eq_errorPolicies wf

/--
  Corollary to the above: partial-authorizing with concrete inputs gives a
  concrete decision.
-/
theorem partial_authz_on_concrete_gives_concrete {policies : Policies} {req : Request} {entities : Entities}
  (wf : req.WellFormed) :
  (Partial.isAuthorized req entities policies).decision ≠ .unknown
:= by
  intro h₁
  have h₂ := partial_authz_eqv_authz_on_concrete (policies := policies) (req := req) (entities := entities) (presp := Partial.isAuthorized req entities policies) (resp := isAuthorized req entities policies) wf
  simp at h₂
  replace ⟨h₂, h₃, h₄, h₅⟩ := h₂ ; clear h₃ h₄ h₅
  cases h₃ : (isAuthorized req entities policies).decision
  case allow =>
    simp [h₃] at h₂
    simp [h₂] at h₁
  case deny =>
    simp [h₃] at h₂
    simp [h₂] at h₁