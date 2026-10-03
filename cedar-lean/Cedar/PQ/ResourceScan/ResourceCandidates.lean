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
  If this is a `permit` policy whose scope constrains the resource to be `in` or
  `==` a concrete entity, return a list of the entities it could apply to. It may
  or may not actually apply to those resources, depending on the policy condition
  and the exact authorization request made. If it is a `forbid` policy, return an
  empty list, since a `forbid` policy can never authorize a request. Returns
  `none` for any other policy, indicating that any resource might be authorized.
-/
def resourceCandidatesForPolicy (p : Policy) (es : Entities) : Option (List EntityUID) :=
  match p.effect with
  | .permit =>
    match p.resourceScope.scope with
    | .is _ | .any => none
    | .eq euid => some [euid]
    | .isMem _ euid | .mem euid => some $ euid :: (es.descendantsOrEmpty euid).elts
  | .forbid => some []

/--
  Apply `resourceCandidatesForPolicy` across all policies in the policy store. A
  resource is returned if access to it might be authorized by any policy in the
  store. If any policy returns `none`, indicating that it does not constrain the
  resource, then any resource might be authorized and this function also returns
  `none`.
-/
def resourceCandidatesForPolicies (ps : Policies) (es : Entities) : Option (List EntityUID) :=
  ps.mapM (resourceCandidatesForPolicy · es)|>.map List.flatten

/--
  Computes the candidate resources that must be checked for a
  resources-for-principal permissions query.

  Candidates are always drawn from the entity store and restricted to the
  requested resource type. When every policy constrains the resource
  (`resourceCandidatesForPolicies` returns `some`), candidates are additionally
  restricted to that list; otherwise every entity of the requested type must be
  checked.
-/
def resourceCandidates (pq : ResourcesForPrincipalRequest) (ps : Policies) (es : Entities): Set EntityUID :=
  let candidates := resourceCandidatesForPolicies ps es
  es.keys.filter λ e =>
    e.ty == pq.resourceType &&
    match candidates with
    | .some candidates => candidates.contains e
    | .none => true
