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
import Cedar.Data
import Cedar.TPE.Authorizer
import Cedar.TPE.Residual
import Cedar.TPE.Evaluator
import Cedar.TPE.Input

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation


/--
Loads everything requested by the set of entity ids,
  returning `Option.none` for missing entities.
Loading more entities than requested is okay.
See `EntityLoader.WellBehaved` for a formal definition.
-/
abbrev EntityLoader := Set EntityUID → Map EntityUID MaybeEntityData

/--
The batched evaluation loop for a single residual expression.
  1. Asks for any new entities referenced by the residual
  2. Partially evaluates now that new entities are loaded
  3. Exits if a value has been found or it hits the maximum iteration limit
-/
def batchedEvaluateLoop
  (residual : Residual)
  (req : Request)
  (loader : EntityLoader)
  (store : PartialEntities)
  : Nat → Residual
  | 0 => residual
  | n + 1 =>
    let toLoad := residual.allLiteralUIDs.filter (λ uid => (store.find? uid).isNone)
    let newEntities := ((loader toLoad).mapOnValues MaybeEntityData.asPartial)
    let newStore := newEntities ++ store

    match Cedar.TPE.evaluate residual req.asPartialRequest newStore with
    | .val v _ty => .val v _ty
    | newRes => batchedEvaluateLoop newRes req loader newStore n

/--
Evaluate a single cedar expression using an EntityLoader
instead of a full Entities store.
Performs a maximum of `iter` number of calls to `loader`,
but may perform fewer when a value is found.
-/
def batchedEvaluate
  (x : TypedExpr)
  (req : Request)
  (loader : EntityLoader)
  (iters : Nat)
  : Residual :=
  let residual := Cedar.TPE.evaluate x.toResidual req.asPartialRequest Map.empty
  batchedEvaluateLoop residual req loader Map.empty iters

/--
The batched authorization loop for authorization over a list of policies.
-/
def batchedAuthorizeLoop
  (residuals : List ResidualPolicy) (req : Request) (loader : EntityLoader)
  (store : PartialEntities) (n : Nat)
  : Response
:=
  let resp := isAuthorizedFromResiduals residuals
  if resp.decision.isSome then
    resp
  else match n with
    | 0 => resp
    | n + 1 =>
      let toLoad := residuals.mapUnion (λ rp : ResidualPolicy => rp.residual.allLiteralUIDs)|>.filter (λ uid => (store.find? uid).isNone)
      let newEntities := ((loader toLoad).mapOnValues MaybeEntityData.asPartial)
      let newStore := newEntities ++ store

      let residuals : List ResidualPolicy := residuals.map λ rp =>
        ⟨rp.id, rp.effect, Cedar.TPE.evaluate rp.residual req.asPartialRequest newStore⟩
      batchedAuthorizeLoop residuals req loader newStore n

/--
Evaluate an authorization request using an EntityLoader instead of a full Entities store.

Performs a maximum of `iter` number of calls to `loader`, but may perform fewer when an authorization decisions is reached.
-/
def batchedAuthorize
  (schema : Schema)
  (policies : List Policy)
  (req : Request)
  (loader : EntityLoader)
  (iters : Nat)
  : Except Error Response := do
  let residualPolicies ← policies.mapM (λ p => do
    pure ⟨p.id, p.effect, ← evaluatePolicy schema p req.asPartialRequest Map.empty⟩)
  pure (batchedAuthorizeLoop residualPolicies req loader Map.empty iters)

/--
Create an entity loader for a given entity store.
This is used for testing.
-/
def entityLoaderFor (es: Entities) (uids : Set EntityUID) :=
  Map.make (uids.toList.map (λ uid =>
        match (es.find? uid) with
        | .some data =>
          (uid, Option.some data)
        | .none =>
          (uid, Option.none)))
