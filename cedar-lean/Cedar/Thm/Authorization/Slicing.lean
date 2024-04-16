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

/-! This file contains definitions relevant to slicing. -/

namespace Cedar.Thm

open Cedar.Spec

/--
A policy slice is a subset of a collection of policies.  This slice is sound for
a given request and entities if every policy in the collection that is not in
the slice is also not satisfied with respect to the request and entities, and
doesn't produce an error when evaluated.
-/
def IsSoundPolicySlice (req : Request) (entities : Entities) (slice policies : Policies) : Prop :=
  slice ⊆ policies ∧
  ∀ policy ∈ policies,
    policy ∉ slice →
    ¬ satisfied policy req entities ∧ ¬ hasError policy req entities

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
A bound is sound for a given policy if the bound is satisfied for every request
and entities for which the policy is satisfied or for which the policy produces
an error.
-/
def IsSoundPolicyBound (bound : PolicyBound) (policy : Policy) : Prop :=
  ∀ (request : Request) (entities : Entities),
  (satisfied policy request entities →
  satisfiedBound bound request entities) ∧
  (hasError policy request entities →
  satisfiedBound bound request entities)

/--
A bound analysis takes as input a policy and returns a PolicyBound.
-/
abbrev BoundAnalysis := Policy → PolicyBound

def BoundAnalysis.slice (ba : BoundAnalysis) (request : Request) (entities : Entities) (policies : Policies) : Policies :=
  policies.filter (fun policy => satisfiedBound (ba policy) request entities)

/--
A bound analysis is sound if it produces sound bounds for all policies.
-/
def IsSoundBoundAnalysis (ba : BoundAnalysis) : Prop :=
  ∀ (policy : Policy), IsSoundPolicyBound (ba policy) policy


end Cedar.Thm
