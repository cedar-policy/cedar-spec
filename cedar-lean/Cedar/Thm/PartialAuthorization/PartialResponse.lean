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

import Cedar.Spec.PartialResponse
import Cedar.Thm.Data.Set

namespace Cedar.Thm.PartialResponse

open Cedar.Data
open Cedar.Spec

theorem mayBeSatisfied_wf {resp : PartialResponse} {eff : Effect} :
  (resp.mayBeSatisfied eff).WellFormed
:= by
  unfold Set.WellFormed PartialResponse.mayBeSatisfied Set.toList
  simp only [Set.make_make_eqv]
  apply List.Equiv.symm
  exact Set.elts_make_equiv

theorem mustBeSatisfied_wf {resp : PartialResponse} {eff : Effect} :
  (resp.mustBeSatisfied eff).WellFormed
:= by
  unfold Set.WellFormed PartialResponse.mustBeSatisfied Set.toList
  simp only [Set.make_make_eqv]
  apply List.Equiv.symm
  exact Set.elts_make_equiv

theorem permits_wf {resp : PartialResponse} :
  resp.permits.WellFormed
:= by
  unfold PartialResponse.permits
  apply mayBeSatisfied_wf (eff := .permit)

theorem knownPermits_wf {resp : PartialResponse} :
  resp.knownPermits.WellFormed
:= by
  unfold PartialResponse.knownPermits
  apply mustBeSatisfied_wf (eff := .permit)

theorem forbids_wf {resp : PartialResponse} :
  resp.forbids.WellFormed
:= by
  unfold PartialResponse.forbids
  apply mayBeSatisfied_wf (eff := .forbid)

theorem knownForbids_wf {resp : PartialResponse} :
  resp.knownForbids.WellFormed
:= by
  unfold PartialResponse.knownForbids
  apply mustBeSatisfied_wf (eff := .forbid)

theorem overapproximateDeterminingPolicies_wf {resp : PartialResponse} :
  resp.overapproximateDeterminingPolicies.WellFormed
:= by
  unfold PartialResponse.overapproximateDeterminingPolicies
  cases resp.knownForbids.isEmpty <;> simp
  case false => exact forbids_wf
  case true =>
    cases resp.permits.isEmpty <;> simp
    case true => exact forbids_wf
    case false =>
      cases resp.forbids.isEmpty <;> simp
      case true => exact permits_wf
      case false => apply Set.union_wf (s₁ := resp.permits) (s₂ := resp.forbids)

theorem underapproximateDeterminingPolicies_wf {resp : PartialResponse} :
  resp.underapproximateDeterminingPolicies.WellFormed
:= by
  unfold PartialResponse.underapproximateDeterminingPolicies
  cases resp.knownForbids.isEmpty <;> simp
  case false => exact knownForbids_wf
  case true =>
    cases resp.permits.isEmpty <;> simp
    case true => exact Set.empty_wf
    case false =>
      cases resp.forbids.isEmpty <;> simp
      case true => exact knownPermits_wf
      case false => exact Set.empty_wf

theorem Residual.mustBeSatisfied_then_mayBeSatisfied {res : Residual} {eff : Effect} {id : PolicyID} :
  res.mustBeSatisfied eff = some id → res.mayBeSatisfied eff = some id
:= by
  unfold Residual.mustBeSatisfied Residual.mayBeSatisfied
  intro h₁
  split at h₁ <;> simp at h₁
  simp [h₁]

theorem mustBeSatisfied_subset_mayBeSatisfied {resp : PartialResponse} {eff : Effect} :
  resp.mustBeSatisfied eff ⊆ resp.mayBeSatisfied eff
:= by
  unfold HasSubset.Subset Set.instHasSubsetSet PartialResponse.mustBeSatisfied PartialResponse.mayBeSatisfied
  simp only
  apply Set.elts_subset_then_subset
  apply List.f_implies_g_then_subset
  intro res pid
  apply Residual.mustBeSatisfied_then_mayBeSatisfied

theorem in_knownPermits_in_permits {resp : PartialResponse} {id : PolicyID} :
  id ∈ resp.knownPermits → id ∈ resp.permits
:= by
  unfold PartialResponse.knownPermits PartialResponse.permits
  have h₁ := @mustBeSatisfied_subset_mayBeSatisfied resp .permit
  rw [Set.subset_def] at h₁
  exact h₁ id

theorem empty_permits_empty_knownPermits {resp : PartialResponse} :
  resp.permits.isEmpty → resp.knownPermits.isEmpty
:= by
  unfold PartialResponse.permits PartialResponse.knownPermits
  apply Set.superset_empty_subset_empty
  exact mustBeSatisfied_subset_mayBeSatisfied

theorem empty_forbids_empty_knownForbids {resp : PartialResponse} :
  resp.forbids.isEmpty → resp.knownForbids.isEmpty
:= by
  unfold PartialResponse.forbids PartialResponse.knownForbids
  apply Set.superset_empty_subset_empty
  exact mustBeSatisfied_subset_mayBeSatisfied

/--
  If the decision is concrete, there must be either:
    - at least one knownForbid, or
    - at least one knownPermit and no possible forbids, or
    - no possible permits
-/
theorem decision_concrete_then_kf_or_kp {resp : PartialResponse} :
  resp.decision ≠ .unknown →
  ¬ resp.knownForbids.isEmpty ∨
  (¬ resp.knownPermits.isEmpty ∧ resp.forbids.isEmpty) ∨
  resp.permits.isEmpty
:= by
  unfold PartialResponse.decision
  intro h₁
  cases h₂ : resp.knownForbids.isEmpty
  case false => left ; simp
  case true =>
    right
    simp [h₂] at h₁
    cases h₃ : resp.permits.isEmpty
    case true => right ; simp
    case false =>
      left
      simp [h₃] at h₁
      simp [h₁]
