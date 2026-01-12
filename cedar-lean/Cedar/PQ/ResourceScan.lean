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

import Cedar.PQ.ResourcesForPrincipal
import Cedar.PQ.ResourceScan.PolicySlice
import Cedar.PQ.ResourceScan.ResourceCandidates

/-!
This file defines a permission query algorithm for Cedar policy by iterating
over the possible resource.

The algorithm includes three optimizations:
1. Policy slicing is used to evaluate only relevant policies given the principal
   and resource type.
2. Resources candidates are selected based on what could possibly be authorized
   given the resources in the policy scopes. This optimization only applies when
   all policy constrain the resource. Otherwise, it fall back to checking every
   resource.
3. Level-based entity slicing to limit the amount of entity data required when
   evaluating the authorization request for each resource.
-/

namespace Cedar.PQ

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

def scanResourcesForPrincipal
  (level : Nat)
  (schema : Schema)
  (pq : ResourcesForPrincipalRequest)
  (entities : Entities)
  (policies : Policies) :
  Set EntityUID
:=
  let policySlice := policySliceByResourceType pq policies entities schema
  let entityScan := resource_candidates pq policies entities
  entityScan.filter λ resource =>
    let entitySlice := entities.sliceAtLevel (pq.req resource) level
    (isAuthorized (pq.req resource) entitySlice policySlice).decision == .allow
