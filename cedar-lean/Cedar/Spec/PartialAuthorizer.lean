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
import Cedar.Spec.PartialValue

/-! This file defines the Cedar partial authorizer. -/

namespace Cedar.Spec

open Cedar.Data
open Effect

def knownSatisfied (policy : Policy) (req : PartialRequest) (entities : PartialEntities) : Bool :=
  partialEvaluate policy.toExpr req entities = .ok (.value true)

def knownUnsatisfied (policy : Policy) (req : PartialRequest) (entities : PartialEntities) : Bool :=
  partialEvaluate policy.toExpr req entities = .ok (.value false)

def knownErroring (policy : Policy) (req : PartialRequest) (entities : PartialEntities) : Bool :=
  match (partialEvaluate policy.toExpr req entities) with
  | .ok _ => false
  | .error _ => true

def isAuthorizedPartial (req : PartialRequest) (entities : PartialEntities) (policies : Policies) : PartialResponse :=
  {
    residuals := policies.filterMap λ policy => match partialEvaluate policy.toExpr req entities with
      | .ok (.value (.prim (.bool false))) => none
      | .ok (.value v) => some (.residual policy.id policy.effect v.asPartialExpr)
      | .ok (.residual r) => some (.residual policy.id policy.effect r)
      | .error e => some (.error policy.id e)
    req,
    entities,
  }

end Cedar.Spec
