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

public import Cedar.Frontend.Cst.Syntax
public import Cedar.Frontend.Cst.Common
public import Cedar.Frontend.Cst.Semantics
public import Cedar.Spec.Response

namespace Cedar.Frontend.Cst

open Cedar.Data
open Cedar

/- Authorizer -/

public def Policy.id : Policy → Spec.PolicyID
  | .policy p => p.id

public def satisfied (policy : Policy) (req : Spec.Request) (entities : Spec.Entities) : Bool :=
  policy.toExpr.evaluate req entities = .ok true

-- To avoid returning an `Option Bool`, this function returns `false`
-- when the `effect` field of `policy` is not an effect
public def satisfiedWithEffect (effect : Spec.Effect) (policy : Policy) (req : Spec.Request) (entities : Spec.Entities) : Bool :=
  if satisfied policy req entities then
  match policy with
  | .policy p => match Ident.toEffect? p.effect with
    | none => false
    | some eff => eff = effect
  else false

public def satisfiedPolicies (effect : Spec.Effect) (policies : Policies) (req : Spec.Request) (entities : Spec.Entities) : Set Spec.PolicyID :=
  Set.make (List.filterMap
    (fun p => if satisfiedWithEffect effect p req entities then some p.id else none)
    policies.ps)

public def hasError (policy : Policy) (req : Spec.Request) (entities : Spec.Entities) : Bool :=
  match policy.toExpr.evaluate req entities with
  | .ok _ => false
  | .error _ => true

public def errorPolicies (policies : Policies) (req : Spec.Request) (entities : Spec.Entities) : Set Spec.PolicyID :=
  Set.make (List.filterMap
    (fun p => if hasError p req entities then some p.id else none)
    policies.ps)

/--
  This is the definition of `isAuthorized` for the CST.
  In `Cedar.Thm.Frontend.Authorizer`, we prove that this authorizer satisfies the same properties
  as the `Cedar.Spec`'s authorizer.

  One way of understanding `Cedar.Thm.Frontend.translation_is_sound` is that this authorizer agrees
  with the spec when the translation succeeds.
-/
public def isAuthorized (req : Spec.Request) (entities : Spec.Entities) (policies : Policies) : Spec.Response :=
  let forbids := satisfiedPolicies .forbid policies req entities
  let permits := satisfiedPolicies .permit policies req entities
  let erroringPolicies := errorPolicies policies req entities
  if forbids.isEmpty && !permits.isEmpty
  then {decision := .allow, determiningPolicies := permits, erroringPolicies}
  else {decision := .deny, determiningPolicies := forbids, erroringPolicies}

end Cedar.Frontend.Cst
