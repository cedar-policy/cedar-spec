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

import Cedar.Data.Set
import Cedar.PQ.ResourceScan
import Cedar.Thm.PQ.ResourceScan.PolicySlice
import Cedar.Thm.PQ.ResourceScan.ResourceCandidates

namespace Cedar.PQ

open Cedar.Data
open Cedar.Spec
open Cedar.Thm
open Cedar.Validation

/-!
Proves correctness of permission queries using a optimized resource-scan algorithm
-/

theorem subset_policies_preserves_valid_with_level :
  ps' ⊆ ps →
  validateWithLevel ps schema level = .ok () →
  validateWithLevel ps' schema level = .ok ()
:= by
  intro hsub hvalid
  replace hvalid : ∀ p ∈ ps', (typecheckPolicyWithEnvironments (typecheckPolicyWithLevel · level) p schema) = .ok () := by
    intro p hp
    replace hp := List.subset_def.mp hsub hp
    exact List.forM_ok_implies_all_ok _ _ hvalid p hp
  exact List.all_ok_implies_forM_ok _ _ hvalid


theorem resource_scan_sound (n : Nat) (schema : Schema) (req : ResourcesForPrincipalRequest) (entities : Entities) (policies : Policies) (r : EntityUID) :
    validateWithLevel policies schema n = .ok () →
    schema.validateWellFormed = .ok () →
    validateRequest schema (Request.mk req.principal req.action r req.context) = .ok () →
    validateEntities schema entities = .ok () →
    r ∈ scanResourcesForPrincipal n schema req entities policies →
    r ∈ entities ∧ r.ty = req.resourceType ∧
    (isAuthorized (req.req r) entities policies).decision = .allow
:= by
  intros h_ps_valid hswf hrv hve h_r_mem_query
  have hwf := request_and_entities_validate_implies_instance_of_wf_schema _  _ _ hswf hrv hve
  unfold scanResourcesForPrincipal at h_r_mem_query

  replace ⟨ h_r_mem_candidates, h_allow ⟩ :
    r ∈ resource_candidates req policies entities  ∧
    (isAuthorized (req.req r) (entities.sliceAtLevel (req.req r) n) (policySliceByResourceType req policies entities schema)).decision = Decision.allow
  := by
    simp only [Set.mem_filter, beq_iff_eq] at h_r_mem_query
    exact h_r_mem_query

  have ⟨h_r_ty, h_r_mem_es⟩  :
    r.ty = req.resourceType ∧
    r ∈ entities
  := resource_candidates_sound h_r_mem_candidates

  have ⟨h_pslice_eq, h_pslice_valid⟩ :
    isAuthorized (req.req r) entities (policySliceByResourceType req policies entities schema) = isAuthorized (req.req r) entities policies ∧
    validateWithLevel (policySliceByResourceType req policies entities schema) schema n = .ok ()
  := by
    have hp := policy_slice_sound (ps := policies) h_r_ty hwf
    and_intros
    · exact isAuthorized_eq_for_sound_policy_slice _ _ _ _ hp
    · exact subset_policies_preserves_valid_with_level hp.left h_ps_valid

  replace h_eslice_eq : isAuthorized (req.req r) entities _ = isAuthorized (req.req r) (entities.sliceAtLevel (req.req r) n) _ :=
    validate_with_level_is_sound_wf hwf h_pslice_valid

  and_intros
  · exact h_r_mem_es
  · exact h_r_ty
  · rw [←h_pslice_eq, h_eslice_eq]
    exact h_allow

theorem resource_scan_complete (n : Nat) (schema : Schema) (req : ResourcesForPrincipalRequest) (entities : Entities) (policies : Policies) (r : EntityUID) :
    validateWithLevel policies schema n = .ok () →
    schema.validateWellFormed = .ok () →
    validateRequest schema (req.req r) = .ok () →
    validateEntities schema entities = .ok () →
    r ∈ entities →
    r.ty = req.resourceType →
    (isAuthorized (req.req r) entities policies).decision = .allow →
    r ∈ scanResourcesForPrincipal n schema req entities policies
:= by
  intros h₃ hswf hrv hve h₇ h₈ h₁₀
  have hwf := request_and_entities_validate_implies_instance_of_wf_schema _ _ _ hswf hrv hve
  unfold scanResourcesForPrincipal
  simp only [Set.mem_filter, beq_iff_eq]
  and_intros
  · exact resource_candidates_complete h₈ h₇ h₁₀
  · have h_p_s := policy_slice_sound (ps := policies) h₈ hwf
    have he := validate_with_level_is_sound_wf hwf (subset_policies_preserves_valid_with_level h_p_s.left h₃)
    replace h_p_s := isAuthorized_eq_for_sound_policy_slice _ _ _ _ h_p_s
    rw [←he, h_p_s]
    exact h₁₀
