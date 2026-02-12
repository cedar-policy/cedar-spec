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
import Cedar.Validation

/-!
This file defines a permission query algorithm for "discretionary" Cedar policies.
Discretionary policies are those with specific constraints on principal, action,
and resource scopes, with no additional conditions.
-/

namespace Cedar.PQ

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Filters discretionary policies to those that apply to a specific principal and resource type.
Returns policies where:
- The resource scope matches the given resource type
- The principal scope includes the given principal (directly or through groups)

Note that this function assumes policies are discretionary and will give
incorrect results for policies with a different form. Most obviously, it never
selects policy  with the `.any` constraint on the principal or resource.
-/
def policiesForPrincipalAndResourceType
  (ps : Policies)
  (principal : EntityUID)
  (principal_groups : Set EntityUID)
  (rty : EntityType) :
  Policies
:= ps.filter λ p =>
  (match p.resourceScope.scope with
  | .eq e => e.ty == rty
  | _ => false) &&
  (match p.principalScope.scope.bound with
  | .some b => b == principal || principal_groups.contains b
  | .none => false)

/--
Creates a map from resources to the policies that apply to them.
Only considers policies with concrete resource scopes (eq).
-/
def policiesByResource (ps : Policies) : Map EntityUID Policies :=
  match ps with
  | [] => Map.empty
  | p :: ps' =>
    let m := policiesByResource ps'
    match p.resourceScope.scope with
    | .eq resource =>
      let existing := m.find? resource |>.getD []
      m.filter (λ r _ => r != resource) ++ Map.make [(resource, p :: existing)]
    | _ => m

/--
Assuming that `ps` is a discretionary policy set, computes the set of resources
that a principal can access.

It is the callers responsibility to ensure that `ps` contains only discretionary
policies. Any policies with an unexpected shape will lead to an incorrect
result.

This condition can be checked with `arePoliciesDiscretionary`.
-/
def discretionaryResourcesForPrincipal
  (pq : ResourcesForPrincipalRequest)
  (es : Entities)
  (ps : Policies) :
  Set EntityUID
:=
  let principal_groups := es.ancestorsOrEmpty pq.principal
  let principal_policies := policiesForPrincipalAndResourceType ps pq.principal principal_groups pq.resourceType
  let resource_policy_map := policiesByResource principal_policies
  Map.keys ∘ resource_policy_map.filter $
    λ resource rps => (isAuthorized (pq.req resource) es rps).decision == .allow

/--
Determines if a policy is discretionary. A policy is discretionary if:
- Principal scope is eq, mem, or isMem
- Action scope is eq
- Resource scope is eq
- No `when` or `unless` conditions
-/
def isPolicyDiscretionary (p : Policy) : Bool :=
  (match p.principalScope.scope with
  | .eq _ | .mem _ | .isMem _ _ => true
  | _ => false) &&
  (match p.actionScope with
  | .actionScope (.eq _) => true
  | _ => false) &&
  (match p.resourceScope.scope with
  | .eq _ => true
  | _ => false) &&
  p.condition == []

/-- Checks if all policies in a list are discretionary. -/
def arePoliciesDiscretionary (policies : Policies) : Bool :=
  policies.all isPolicyDiscretionary

end Cedar.PQ
