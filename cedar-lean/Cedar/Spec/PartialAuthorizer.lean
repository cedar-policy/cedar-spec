/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Spec.PartialEvaluator
import Cedar.Spec.PartialResponse

/-! This file defines the Cedar partial authorizer. -/

namespace Cedar.Spec

open Cedar.Data
open Effect

def knownSatisfied (policy : Policy) (req : PartialRequest) (entities : PartialEntities) : Bool :=
  partialEvaluate policy.toExpr req entities = .ok (.value true)

def knownUnsatisfied (policy : Policy) (req : PartialRequest) (entities : PartialEntities) : Bool :=
  partialEvaluate policy.toExpr req entities = .ok (.value false)

def knownSatisfiedWithEffect (effect : Effect) (policy : Policy) (req : PartialRequest) (entities : PartialEntities) : Option PolicyID :=
  if policy.effect == effect && knownSatisfied policy req entities
  then some policy.id
  else none

def knownErroring (policy : Policy) (req : PartialRequest) (entities : PartialEntities) : Bool :=
  match (partialEvaluate policy.toExpr req entities) with
  | .ok _ => false
  | .error _ => true

def knownSatisfiedPolicies (effect : Effect) (policies : Policies) (req : PartialRequest) (entities : PartialEntities) : Set PolicyID :=
  Set.make (policies.filterMap (knownSatisfiedWithEffect effect · req entities))

/--
  This function is analogous to `knownSatisfiedWithEffect` in that it returns
  `Option PolicyID`, but not analogous to `knownSatisfiedWithEffect` in that it does
  not consider the policy's effect.
-/
def knownErroring' (policy : Policy) (req : PartialRequest) (entities : PartialEntities) : Option PolicyID :=
  if knownErroring policy req entities
  then some policy.id
  else none

def knownErroringPolicies (policies : Policies) (req : PartialRequest) (entities : PartialEntities) : Set PolicyID :=
  Set.make (policies.filterMap (knownErroring' · req entities))

/--
  If evaluating the policy with these partial inputs results in a residual, return
  that residual, otherwise None.
  Returns None for any policies that fully evaluate or that definitely result in
  an error.
-/
def residual (policy : Policy) (req : PartialRequest) (entities : PartialEntities) : Option Residual :=
  match partialEvaluate policy.toExpr req entities with
  | .ok (.residual r) => some {
      id := policy.id,
      effect := policy.effect,
      condition := r,
    }
  | _ => none

/--
  Given a set of policies and partial inputs, partial-evaluate and return the
  set of residual policies.
  Ignores any policies that fully evaluate or that definitely result in an error.
-/
def residualPolicies (policies : Policies) (req : PartialRequest) (entities : PartialEntities) : List Residual :=
  policies.filterMap (residual · req entities)

def isAuthorizedPartial (req : PartialRequest) (entities : PartialEntities) (policies : Policies) : PartialResponse :=
  let knownForbids := knownSatisfiedPolicies .forbid policies req entities
  let knownPermits := knownSatisfiedPolicies .permit policies req entities
  let residuals := residualPolicies policies req entities
  let knownErroringPolicies := knownErroringPolicies policies req entities
  if !knownForbids.isEmpty
  then .known { decision := .deny, determiningPolicies := knownForbids, erroringPolicies := knownErroringPolicies } -- TODO this is not correct for determiningPolicies
  else if !residuals.isEmpty
  then .residual {
    residuals,
    determiningPolicies := Set.make (residuals.map Residual.id ++ knownPermits.elts),
    erroringPolicies := knownErroringPolicies,
  }
  else if !knownPermits.isEmpty
  then .known { decision := .allow, determiningPolicies := knownPermits, erroringPolicies := knownErroringPolicies }
  else .known { decision := .deny, determiningPolicies := Set.empty, erroringPolicies := knownErroringPolicies }

end Cedar.Spec
