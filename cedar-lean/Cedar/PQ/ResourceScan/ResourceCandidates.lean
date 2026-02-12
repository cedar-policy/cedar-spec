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

import Cedar.Spec.Entities
import Cedar.Spec.Policy
import Cedar.Validation.Validator
import Cedar.PQ.ResourcesForPrincipal

namespace Cedar.PQ

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
  If this policy is a `permit` policy constrains the resource to be `in` or `==`
  to a concrete entity in the policy scope, return a list of entities which it
  could apply to. It may or may not actually apply to those resources depending
  on the policy condition and the exact authorization request made.  If it's a
  `forbid` policy, return an empty list since the policy can never authorize any
  request.  Returns `None` for other policies, indicating that any resources
  might be authorized.
-/
def resource_candidates_for_policy (p : Policy) (es : Entities) : Option (List EntityUID) :=
  match p.effect with
  | .permit =>
    match p.resourceScope.scope with
    | .is _ | .any => none
    | .eq euid => some [euid]
    | .isMem _ euid | .mem euid => some $ euid :: (es.descendantsOrEmpty euid).elts
  | .forbid => some []

/--
  Apply `resource_candidates_for_policy` across all policies in the policy
  store. A resources is returned if access to it might be authorized by any
  policy in the store. If any policy return `None`, indicating that it does not
  constrain the resource, then we assume all resources might be authorized, and
  this function also returns `None`.
-/
def resource_candidates_for_policies (ps : Policies) (es : Entities) : Option (List EntityUID) :=
  ps.mapM (resource_candidates_for_policy · es)|>.map List.flatten

/--
  Computes the resources candidates that must be checked for a
  resources-for-principals permissions query.

  If all policies contains have a resource constraint, this takes the candidates
  as determined by `resources_candidates_for_policies` and additionally filters
  them to include only entities which have the requested resource type and are
  present in the entity store.

  If any policy does not have a resource constraint (`resources_candidates_for_policies` returns `None`),
  this assumes all entities need to be checked, so it only filters candidates
  based on their entity type.
-/
def resource_candidates (pq : ResourcesForPrincipalRequest) (ps : Policies) (es : Entities): Set EntityUID :=
  let candidates := resource_candidates_for_policies ps es
  es.keys.filter λ e =>
    e.ty == pq.resourceType &&
    match candidates with
    | .some candidates => candidates.contains e
    | .none => true
