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
import Cedar.Thm.PQ.Discretionary.DiscretionaryPolicy
import Cedar.Thm.PQ.Discretionary.PoliciesForPrincipalAndResourceType
import Cedar.Thm.PQ.Discretionary.PoliciesByResource
import Cedar.Thm.PolicySlice
import Cedar.Thm.Authorization

/-!
Proves correctness of permission queries for discretionary policies.
-/

namespace Cedar.PQ

open Cedar.Spec
open Cedar.Data
open Cedar.Thm

section
variable {pq : ResourcesForPrincipalRequest} {es : Entities} {ps : Policies} {r : EntityUID}

theorem discretionary_resource_for_principal_sound :
  arePoliciesDiscretionary ps = true →
  r ∈ discretionaryResourcesForPrincipal pq es ps →
  (r.ty = pq.resourceType ∧ (isAuthorized (pq.req r) es ps).decision = .allow)
:= by
  intro h₁ h₂
  simp only [discretionaryResourcesForPrincipal, Function.comp_apply] at h₂
  rw [Map.in_keys_iff_contains, ←Map.find_matching_iff_filter_contains (policiesByResource_wf _)] at h₂
  replace ⟨rps, h₂, h₃⟩ := h₂
  have h_r_ty : r.ty = pq.resourceType := by
    have h₃ : (policiesByResource (policiesForPrincipalAndResourceType ps pq.principal (es.ancestorsOrEmpty pq.principal) pq.resourceType)).contains r := by
      simp [Map.contains, h₂]
    replace ⟨ rp, h₃, h₄ ⟩ := policiesByResource_keys_from_input h₃
    replace ⟨⟨re, h₃, h₅⟩, _⟩ := policiesForPrincipalAndResourceType_scope_constraint h₃
    grind
  have h_sound_slice := policiesByResource_policiesForPrincipalAndResourceType_composed_sound_slice h_r_ty h₁ h₂
  have h_auth_eq := isAuthorized_eq_for_sound_policy_slice (pq.req r) es rps ps h_sound_slice
  constructor
  · exact h_r_ty
  · simpa [←h_auth_eq] using h₃

theorem discretionary_resource_for_principal_complete :
  arePoliciesDiscretionary ps = true →
  r.ty = pq.resourceType →
  (isAuthorized (pq.req r) es ps).decision = .allow →
  r ∈ discretionaryResourcesForPrincipal pq es ps
:= by
  simp only [discretionaryResourcesForPrincipal, Function.comp_apply]
  intro h₁ h₂ h₃
  rw [Map.in_keys_iff_contains]
  apply Map.filter_contains_if_find_matching
  simp only [beq_iff_eq]
  have h_permit := allowed_only_if_explicitly_permitted (pq.req r) es ps h₃
  simp only [IsExplicitlyPermitted, HasSatisfiedEffect] at h_permit
  have ⟨policy, h_policy_in_ps, h_policy_effect, h_policy_satisfied⟩ := h_permit
  have h_discretionary : isPolicyDiscretionary policy := by
    simp only [arePoliciesDiscretionary, List.all_eq_true] at h₁
    exact h₁ policy h_policy_in_ps
  have ⟨⟨pb, h_principal_scope⟩, h_action_scope, h_resource_scope, h_condition⟩ :=
    discretionary_policy_structure_from_satisfaction h_discretionary h_policy_satisfied
  have h_in_prtp : policy ∈ policiesForPrincipalAndResourceType ps pq.principal (es.ancestorsOrEmpty pq.principal) pq.resourceType := by
    simp only [policiesForPrincipalAndResourceType, List.mem_filter, Bool.and_eq_true]
    apply And.intro h_policy_in_ps
    simp only [ResourcesForPrincipalRequest.req] at h_principal_scope
    simp [h_resource_scope, h_principal_scope, ResourcesForPrincipalRequest.req, h₂]
  have h_map_entry : ∃ rps, (policiesByResource _).find? r = some rps ∧ policy ∈ rps :=
    policiesByResource_contains_policy h_in_prtp h_resource_scope
  have ⟨rps, h_find, h_policy_in_rps⟩ := h_map_entry
  exists rps
  constructor
  · exact h_find
  · have h_sound := policiesByResource_policiesForPrincipalAndResourceType_composed_sound_slice h₂ h₁ h_find
    have h_auth_eq := isAuthorized_eq_for_sound_policy_slice (pq.req r) es rps ps h_sound
    rw [h_auth_eq]
    exact h₃

end
