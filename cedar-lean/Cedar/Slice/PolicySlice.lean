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

import Cedar.Spec

/-!
This file defines a simple policy slicing algorithm that is based
on policy scopes. For proofs of correctness, see Cedar.Thm.PolicySlice.
-/

namespace Cedar.Slice

open Cedar.Spec

/--
A policy bound consists of optional `principal` and `resource` entities.
-/
structure PolicyBound where
  principalBound : Option EntityUID
  resourceBound  : Option EntityUID

def inSomeOrNone (uid : EntityUID) (opt : Option EntityUID) (entities : Entities) : Bool :=
  match opt with
  | .some uid' => inₑ uid uid' entities
  | .none      => true

/--
A bound is satisfied by a request and store if the request principal and
resource fields are descendents of the corresponding bound fields (or if those
bound fields are `none`).
-/
def satisfiedBound (bound : PolicyBound) (request : Request) (entities : Entities) : Bool :=
  inSomeOrNone request.principal bound.principalBound entities ∧
  inSomeOrNone request.resource bound.resourceBound entities


/--
A bound analysis takes as input a policy and returns a PolicyBound.
-/
abbrev BoundAnalysis := Policy → PolicyBound

/--
A bound-based slicing algorithm takes as input a bound analysis, request, entities,
and policies, and filters out the policies whose bound is not satisfied by the
request and entities.
-/
def BoundAnalysis.slice (ba : BoundAnalysis) (request : Request) (entities : Entities) (policies : Policies) : Policies :=
  policies.filter (fun policy => satisfiedBound (ba policy) request entities)


/--
Scope-based bound analysis extracts the bound from the policy scope.
-/
def scopeAnalysis (policy : Policy) : PolicyBound :=
  {
    principalBound := policy.principalScope.scope.bound,
    resourceBound  := policy.resourceScope.scope.bound,
  }

/--
Shared skeleton of the action scope analysis, parameterized by the test used
for group membership: `inTest uid₁ uid₂` decides whether `uid₁` is equal to, or
a descendent of, `uid₂`.

Both the concrete analysis (`isPolicyRelevantForAction`) and the partial one
used for TPE (`Cedar.Slice.isPolicyRelevantForPartialAction`) are instances of
this. Factoring the match out keeps them in sync by construction: they can
differ only in the membership test, which is exactly the invariant their
soundness proofs rely on (see `isPolicyRelevantForActionBy_mono`).
-/
def isPolicyRelevantForActionBy (inTest : EntityUID → EntityUID → Bool) (action : EntityUID) (policy : Policy) : Bool :=
  match policy.actionScope with
  | .actionScope .any             => true
  | .actionScope (.eq uid)        => action == uid
  | .actionScope (.mem uid)       => inTest action uid
  | .actionScope (.is ety)        => ety == action.ty
  | .actionScope (.isMem ety uid) => ety == action.ty && inTest action uid
  | .actionInAny uids             => uids.any (inTest action ·)

/--
Decides whether a policy is *relevant* to the request action: i.e., whether
the policy's action scope constraint is satisfied by the request action.

Unlike the principal and resource scopes, the action of a request is known
exactly, so action scopes can be decided precisely rather than approximated by
an `inₑ`-based bound (cf. `PolicyBound`). In particular, an `== Action::"other"`
scope makes the policy irrelevant unless the request action *is*
`Action::"other"` (being a descendent of it does not suffice), whereas an
`in Action::"other"` scope makes it relevant exactly when `Action::"other"` is
the request action or one of its ancestors.
-/
def isPolicyRelevantForAction (policy : Policy) (request : Request) (entities : Entities) : Bool :=
  isPolicyRelevantForActionBy (inₑ · · entities) request.action policy

/--
Action-based slicing keeps only the policies whose action scope is relevant to
the request action.
-/
def actionSlice (request : Request) (entities : Entities) (policies : Policies) : Policies :=
  policies.filter (fun policy => isPolicyRelevantForAction policy request entities)

/--
Full scope-based slicing: a single pass that keeps a policy only if its
principal and resource bounds are satisfied by the request *and* its action
scope is relevant to the request action. This combines `BoundAnalysis.slice`
with `actionSlice` (see `scopeSlice_eq_actionSlice_boundSlice`).
-/
def scopeSlice (request : Request) (entities : Entities) (policies : Policies) : Policies :=
  policies.filter fun policy =>
    satisfiedBound (scopeAnalysis policy) request entities &&
    isPolicyRelevantForAction policy request entities

end Cedar.Slice
