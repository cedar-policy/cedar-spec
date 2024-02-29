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

theorem in_knownPermits_in_permits {resp : PartialResponse} {id : PolicyID} :
  id ∈ resp.knownPermits → id ∈ resp.permits
:= by
  unfold PartialResponse.knownPermits PartialResponse.permits
  simp only [← Set.make_mem]
  simp only [List.mem_filterMap]
  intro h₁
  replace ⟨r, h₁⟩ := h₁
  exists r
  apply And.intro h₁.left
  replace h₁ := h₁.right
  split at h₁ <;> simp at h₁
  subst h₁ ; simp

theorem empty_permits_empty_knownPermits {resp : PartialResponse} :
  resp.permits.isEmpty → resp.knownPermits.isEmpty
:= by
  unfold PartialResponse.permits PartialResponse.knownPermits
  simp
  repeat rw [Set.empty_iff_not_exists]
  intro h₁ h₂
  simp at h₁
  replace ⟨pid, h₂⟩ := h₂
  specialize h₁ pid
  rw [← Set.make_mem] at *
  rw [List.mem_filterMap] at *
  replace ⟨res, h₂⟩ := h₂
  apply h₁ ; clear h₁
  exists res
  apply And.intro h₂.left
  replace h₂ := h₂.right
  split at h₂ <;> simp at h₂
  subst h₂ ; simp

theorem empty_forbids_empty_knownForbids {resp : PartialResponse} :
  resp.forbids.isEmpty → resp.knownForbids.isEmpty
:= by
  unfold PartialResponse.forbids PartialResponse.knownForbids
  simp
  repeat rw [Set.empty_iff_not_exists]
  intro h₁ h₂
  simp at h₁
  replace ⟨pid, h₂⟩ := h₂
  specialize h₁ pid
  rw [← Set.make_mem] at *
  rw [List.mem_filterMap] at *
  replace ⟨res, h₂⟩ := h₂
  apply h₁ ; clear h₁
  exists res
  apply And.intro h₂.left
  replace h₂ := h₂.right
  split at h₂ <;> simp at h₂
  subst h₂ ; simp

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
