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

import Cedar.Spec.Evaluator
import Cedar.Spec.Response

/-! This file defines the Cedar authorizer. -/

namespace Cedar.Spec

open Cedar.Data
open Effect

def satisfied (policy : Policy) (req : Request) (entities : Entities) : Bool :=
  (evaluate policy.toExpr req entities) = .ok true

def satisfiedWithEffect (effect : Effect) (policy : Policy) (req : Request) (entities : Entities) : Option PolicyID :=
  if policy.effect == effect && satisfied policy req entities
  then some policy.id
  else none

def satisfiedPolicies (effect : Effect) (policies : Policies) (req : Request) (entities : Entities) : Set PolicyID :=
  Set.make (policies.filterMap (satisfiedWithEffect effect · req entities))

def isAuthorized (req : Request) (entities : Entities) (policies : Policies) : Response :=
  let forbids := satisfiedPolicies .forbid policies req entities
  let permits := satisfiedPolicies .permit policies req entities
  if forbids.isEmpty && !permits.isEmpty
  then { decision := .allow, policies := permits }
  else { decision := .deny,  policies := forbids }

end Cedar.Spec