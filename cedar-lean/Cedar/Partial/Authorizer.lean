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

import Cedar.Partial.Evaluator
import Cedar.Partial.Response
import Cedar.Partial.Value

/-! This file defines the Cedar partial authorizer. -/

namespace Cedar.Partial

open Cedar.Data
open Cedar.Partial (Residual)
open Cedar.Spec (Policy Policies)

def knownSatisfied (policy : Policy) (req : Partial.Request) (entities : Partial.Entities) : Bool :=
  Partial.evaluate policy.toExpr req entities = .ok (.value true)

def knownUnsatisfied (policy : Policy) (req : Partial.Request) (entities : Partial.Entities) : Bool :=
  Partial.evaluate policy.toExpr req entities = .ok (.value false)

def knownErroring (policy : Policy) (req : Partial.Request) (entities : Partial.Entities) : Bool :=
  match (Partial.evaluate policy.toExpr req entities) with
  | .ok _ => false
  | .error _ => true

/--
  Not to be confused with `Partial.evaluate`, which evaluates a `Spec.Expr`
  and returns a `Partial.Value`, this function `Partial.evaluatePolicy`
  evaluates a `Policy` and returns a `Residual`, or `none` if the policy is
  definitely not satisfied (residual `false`).
-/
def evaluatePolicy (policy : Policy) (req : Partial.Request) (entities : Partial.Entities) : Option Residual :=
  match Partial.evaluate policy.toExpr req entities with
  | .ok (.value false) => none
  | .ok pv => some (.residual policy.id policy.effect pv)
  | .error _ => some (.error policy.id)

def isAuthorized (req : Partial.Request) (entities : Partial.Entities) (policies : Policies) : Partial.Response :=
  {
    residuals := policies.filterMap (evaluatePolicy · req entities),
    entities,
  }

end Cedar.Partial
