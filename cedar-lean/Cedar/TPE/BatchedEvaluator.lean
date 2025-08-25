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


abbrev EntityLoader := Set EntityUID → Map EntityUID PartialEntityData

def Residual.allLiteralUIDs (x : Residual) : Set EntityUID :=
  match x with
  | .val (.prim (.entityUID uid)) _ty  => Set.singleton uid
  | .val _ _                           => Set.empty
  | .error _e                          => Set.empty
  | .var _ _                           => Set.empty
  | .ite x₁ x₂ x₃ _      =>
    x₁.allLiteralUIDs ∪ x₂.allLiteralUIDs ∪ x₃.allLiteralUIDs
  | .and x₁ x₂ _         =>
    Residual.allLiteralUIDs x₁ ∪ Residual.allLiteralUIDs x₂
  | .or x₁ x₂ _          =>
    Residual.allLiteralUIDs x₁ ∪ Residual.allLiteralUIDs x₂
  | .unaryApp _ x _      =>
    Residual.allLiteralUIDs x
  | .binaryApp _ x₁ x₂ _ =>
    Residual.allLiteralUIDs x₁ ∪ Residual.allLiteralUIDs x₂
  | .getAttr x _ _       => Residual.allLiteralUIDs x
  | .hasAttr x _ _       => Residual.allLiteralUIDs x
  | .set x _             =>
    x.mapUnion₁ (λ ⟨v, _⟩ => Residual.allLiteralUIDs v)
  | .record x _          =>
    x.mapUnion₂ (λ ⟨⟨_attr, v⟩, _⟩ => Residual.allLiteralUIDs v)
  | .call _ x _          =>
    x.mapUnion₁ (λ ⟨v, _⟩ => Residual.allLiteralUIDs v)
termination_by sizeOf x
decreasing_by
  any_goals
    simp
    try simp at *
    try omega
  all_goals
    rename_i h
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
  let newStore := Map.make (newEntities.kvs ++ store.kvs)
  let newRes := Cedar.TPE.evaluate residual req.asPartialRequest newStore

  match newRes with
  | .val v _ty => .ok v
  | _ => batchedEvalLoop newRes req loader newStore


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
  let residual := Cedar.TPE.evaluate x.toResidual req.asPartialRequest Map.empty
  -- start the batched evaluation loop
  batchedEvalLoop residual req loader Map.empty

def entityLoaderFor (es: Entities) (uids : Set EntityUID) :=
  Map.make (uids.toList.map (λ uid =>
        match (es.find? uid) with
        | .some data =>
          (uid, EntityData.asPartial data)
        | .none =>
          (uid, PartialEntityData.absent)))
