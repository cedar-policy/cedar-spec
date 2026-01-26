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

import Cedar.Thm.PQ.Discretionary
import Cedar.Thm.PQ.ResourceScan

/-!
Proves correctness of two implementation of "permission queries", algorithms for
listing all resources a principal is authorized to perform an action on.
-/

namespace Cedar.PQ

open Cedar.Spec
open Cedar.Data
open Cedar.Thm
open Cedar.Validation

/--
The first algorithm scans resources in the entity store, evaluating policies for
each resource to see if access is permitted. This algorithm applies optimization
to restrict the sets of policies, entities and candidate resources.  Defined in
Cedar.PQ.ResourceScan with the main correctness theorem in
Cedar.Thm.PQ.ResourceScan.

A resource is returned by `scanResourcesForPrincipal` if and only if it exists
in the entity store, has the requested resource type, and authorization allows
access to the resource for the requested principal and action.
-/
theorem resource_scan_correct (n : Nat) (schema : Schema) (req : ResourcesForPrincipalRequest) (entities : Entities) (policies : Policies) (r : EntityUID) :
    validateWithLevel policies schema n = .ok () →
    schema.validateWellFormed = .ok () →
    validateRequest schema (req.req r) = .ok () →
    validateEntities schema entities = .ok () →
    (r ∈ scanResourcesForPrincipal n schema req entities policies ↔
    (r ∈ entities ∧ r.ty = req.resourceType ∧ (isAuthorized (req.req r) entities policies).decision = .allow))
:= by
  intro h₁ h₂ h₃ h₄
  constructor
  · intro h_mem
    have h_req_eq : Request.mk req.principal req.action r req.context = req.req r := by
      simp only [ResourcesForPrincipalRequest.req]
    have h_sound := resource_scan_sound n schema req entities policies r h₁ h₂ h₃ h₄ h_mem
    simp [h_sound]
  · intro ⟨h₅, h_ty, h_allow⟩
    exact resource_scan_complete n schema req entities policies r h₁ h₂ h₃ h₄ h₅ h_ty h_allow

/--
The second algorithm assumes policies are "discretionary" (have particular
restricted form), and uses this assumption to limit the candidate resources to
only the resources which appear explicitly authorized in a policy's scope.
Defined in Cedar.PQ.Discretionary with the main correctness theorem in
Cedar.Thm.PQ.Discretionary.

Given a discretionary policy set, a resource is returned by
`discretionaryResourcesForPrincipal` if and only if it has the requested
resource type and authorization allows access for the resources with the request
principal and action.

Notably this theorem does not guarantee that the returned resources actually
exist in the set of entities. This is by design as the query algorithm
effectively uses the resource scope conditions in the policy store as the set of
resource entities.
-/
theorem discretionary_resource_for_principal_correct :
  arePoliciesDiscretionary ps = true →
    (r ∈ discretionaryResourcesForPrincipal pq es ps ↔ (r.ty = pq.resourceType ∧ (isAuthorized (pq.req r) es ps).decision = .allow))
:= by
  intro h_discretionary
  constructor
  · exact discretionary_resource_for_principal_sound h_discretionary
  · intro ⟨h_ty, h_auth⟩
    exact discretionary_resource_for_principal_complete h_discretionary h_ty h_auth

end PQ
