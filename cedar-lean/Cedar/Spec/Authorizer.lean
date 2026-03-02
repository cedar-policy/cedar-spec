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

module

public import Cedar.Spec.Evaluator
public import Cedar.Spec.Response

/-! This file defines the Cedar authorizer. -/

namespace Cedar.Spec

open Cedar.Data
open Effect

public def satisfied (policy : Policy) (req : Request) (entities : Entities) : Bool :=
  (evaluate policy.toExpr req entities) = .ok true

public def satisfiedWithEffect (effect : Effect) (policy : Policy) (req : Request) (entities : Entities) : Option PolicyID :=
  if policy.effect == effect && satisfied policy req entities
  then some policy.id
  else none

public def satisfiedPolicies (effect : Effect) (policies : Policies) (req : Request) (entities : Entities) : Set PolicyID :=
  Set.make (policies.filterMap (satisfiedWithEffect effect · req entities))

public def hasError (policy : Policy) (req : Request) (entities : Entities) : Bool :=
  match (evaluate policy.toExpr req entities) with
  | .ok _ => false
  | .error _ => true

/--
  This function is analogous to `satisfiedWithEffect` in that it returns
  `Option PolicyID`, but not analogous to `satisfiedWithEffect` in that it does
  not consider the policy's effect.
-/
public def errored (policy : Policy) (req : Request) (entities : Entities) : Option PolicyID :=
  if hasError policy req entities then some policy.id else none

public def errorPolicies (policies : Policies) (req : Request) (entities : Entities) : Set PolicyID :=
  Set.make (policies.filterMap (errored · req entities))

public def isAuthorized (req : Request) (entities : Entities) (policies : Policies) : Response :=
  let forbids := satisfiedPolicies .forbid policies req entities
  let permits := satisfiedPolicies .permit policies req entities
  let erroringPolicies := errorPolicies policies req entities
  if forbids.isEmpty && !permits.isEmpty
  then { decision := .allow, determiningPolicies := permits, erroringPolicies }
  else { decision := .deny,  determiningPolicies := forbids, erroringPolicies }

public def satisfiedPolicy? (effect : Effect) (policies : Policies) (req : Request) (entities : Entities) : Option PolicyID :=
  policies.findSome? (satisfiedWithEffect effect · req entities)

/--
  An alternative short-circuiting authorization algorithm. While the standard
  authorization algorithm always evaluates all policies to return the complete
  sets of determining and erroring policies, some use cases may only needs the
  `allow` or `deny` decision. In this case we can stop after satisfying a single
  forbid policy, or after ensuring no forbid policies apply and satisfying a
  single permit policy.
-/
public def isAuthorizedShortCircuit (req : Request) (entities : Entities) (policies : Policies) : Decision :=
  let forbid := satisfiedPolicy? .forbid policies req entities
  if forbid.isSome
  then .deny
  else
    let permit := satisfiedPolicy? .permit policies req entities
    if permit.isSome
    then .allow
    else .deny

end Cedar.Spec
