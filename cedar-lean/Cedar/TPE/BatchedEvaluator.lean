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
abbrev EntityLoader := Set EntityUID → Map EntityUID (Option EntityData)


/-- subtle: a missing entity is the same as a fresh entity
with attrs, tags, or ancestors.
-/
def EntityDataOption.asPartial :
  Option EntityData → PartialEntityData
| none =>
  { attrs :=  (.some Map.empty)
  , ancestors := (.some Set.empty)
  , tags := (.some Map.empty)}
| some d =>
  d.asPartial

/--
The batched evaluation loop
  1. Asks for any new entities referenced by the residual
  2. Partially evaluates now that new entities are loaded
  3. Exits if a value has been found or it hits the maximum iteration limit
-/
def batchedEvalLoop
  (residual : Residual)
  (req : Request)
  (loader : EntityLoader)
  (store : PartialEntities)
  : Nat → Residual
  | 0 => residual
  | n + 1 =>
    let toLoad := residual.allLiteralUIDs.filter (λ uid => (store.find? uid).isNone)
    let newEntities := ((loader toLoad).mapOnValues EntityDataOption.asPartial)
    let newStore := newEntities ++ store

    match Cedar.TPE.evaluate residual req.asPartialRequest newStore with
    | .val v _ty => .val v _ty
    | newRes => batchedEvalLoop newRes req loader newStore n


/--
Evaluate a cedar expression using an EntityLoader
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
  -- start the batched evaluation loop
  batchedEvalLoop residual req loader Map.empty iters

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
