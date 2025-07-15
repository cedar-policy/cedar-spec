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


def EntityLoader : Type := Set EntityUID → Map EntityUID PartialEntityData

def Residual.allLiteralUIDs (x : Residual) : Set EntityUID :=
  match x with
  | .val v _ty =>
    match v with
    | .prim (.entityUID uid) => Set.singleton uid
    | _ => Set.empty
  | .error _e =>
    Set.empty
  | .var v _ =>
    -- these cases should not happen, since the request was fully concrete
    match v with
    | .principal => Set.empty
    | .resource  => Set.empty
    | .action    => Set.empty
    | .context   => Set.empty
  | .ite c t e _ => Residual.allLiteralUIDs c ∪ Residual.allLiteralUIDs t ∪ Residual.allLiteralUIDs e
  | .and a b _   => Residual.allLiteralUIDs a ∪ Residual.allLiteralUIDs b
  | .or a b _    => Residual.allLiteralUIDs a ∪ Residual.allLiteralUIDs b
  | .unaryApp _ e _ => Residual.allLiteralUIDs e
  | .binaryApp _ a b _ => Residual.allLiteralUIDs a ∪ Residual.allLiteralUIDs b
  | .getAttr e _ _ => Residual.allLiteralUIDs e
  | .hasAttr e _ _ => Residual.allLiteralUIDs e
  | .set ls _ => ls.mapUnion₁ (λ ⟨v, _⟩ => Residual.allLiteralUIDs v)
  | .record m _ => m.mapUnion₂ (λ ⟨⟨_attr, v⟩, _⟩ => Residual.allLiteralUIDs v)
  | .call _ ls _ => ls.mapUnion₁ (λ ⟨v, _⟩ => Residual.allLiteralUIDs v)
termination_by sizeOf x
decreasing_by
  repeat case _ =>
    simp [*]; try omega
  . rename_i h
    let so := List.sizeOf_lt_of_mem h
    simp
    omega
  . rename_i h
    simp at *
    omega
  . rename_i h
    let so := List.sizeOf_lt_of_mem h
    simp at *
    omega


/--
The batched evaluation loop
  1. Asks for any new entities referenced by the residual
  2. Partially evaluates now that new entities are loaded
  3. Exits if a value has been found
-/
partial def batchedEvalLoop
  (residual : Residual)
  (req : Request)
  (loader : EntityLoader)
  (store : PartialEntities)
  : Result Value :=
  let toLoad := (Residual.allLiteralUIDs residual).filter (λ uid => (store.find? uid).isNone)
  let newEntities := loader toLoad
  let newStore := newEntities.kvs.foldl (λ acc ed => acc.insert ed.1 ed.2) store
  let newRes := Cedar.TPE.evaluate residual (Request.asPartialRequest req) newStore

  match newRes with
  | .val v _ty => .ok v
  | _ =>
    batchedEvalLoop newRes req loader newStore


/--
Evaluate a cedar expression using an EntityLoader
instead of a full Entities store.
This algorithm minimizes the number of calls to the EntityLoader using partial evaluation.
-/
def batchedEvaluate
  (x : TypedExpr)
  (req : Request)
  (loader : EntityLoader)
  : Result Value :=
  let emptyStore : PartialEntities := Map.mk []
  let residual := TypedExpr.toResidual x
  -- an initial partial evaluation, removing all variables
  let residual₂ := Cedar.TPE.evaluate residual (Request.asPartialRequest req) emptyStore
  -- start the batched evaluation loop
  batchedEvalLoop residual₂ req loader emptyStore

def entityLoaderFor : (e: Entities) -> EntityLoader :=
  fun e =>
   fun uids =>
    Map.make (uids.toList.map (fun uid =>
      match (e.find? uid) with
      | .some data =>
        (uid, EntityData.asPartial data)
      | .none =>
        (uid, PartialEntityData.MissingEntity)))
