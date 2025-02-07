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
import Protobuf.Message
import Protobuf.String

-- Message Dependencies
import CedarProto.ValidatorEntityType
import CedarProto.ValidatorActionId

open Proto

namespace Cedar.Validation.Proto

def EntityTypeWithTypesMap := Proto.Map Spec.EntityTypeProto ValidatorEntityType
  deriving Inhabited, Field

def EntityUidWithActionsIdMap := Proto.Map Spec.EntityUID ValidatorActionId
  deriving Inhabited, Field

structure ValidatorSchema where
  ets : EntityTypeWithTypesMap
  acts : EntityUidWithActionsIdMap
deriving Inhabited

instance : DecidableLT Spec.EntityTypeProto := by
  unfold Spec.EntityTypeProto
  apply inferInstance

/-
The Rust data types store _descendant_ information for the entity type store
and action store, but _ancestor_ information for the entity store. The Lean
formalization standardizes on ancestor information.

The definitions and utility functions below are used to convert the descendant
representation to the ancestor representation.
-/
@[inline]
private def findInMapValues [LT α] [DecidableEq α] [DecidableLT α] (m : Data.Map α (Data.Set α)) (k₁ : α) : Data.Set α :=
  let setOfSets := List.map (λ (k₂,v) => if v.contains k₁ then Data.Set.singleton k₂ else Data.Set.empty) m.toList
  setOfSets.foldl (λ acc v => acc.union v) Data.Set.empty

@[inline]
private def descendantsToAncestors [LT α] [DecidableEq α] [DecidableLT α] (descendants : Data.Map α (Data.Set α)) : Data.Map α (Data.Set α) :=
  Data.Map.make (List.map
    (λ (k,_) => (k, findInMapValues descendants k)) descendants.toList)

end Cedar.Validation.Proto

namespace Cedar.Validation.Proto.EntityTypeWithTypesMap
@[inline]
def toEntitySchema (ets : EntityTypeWithTypesMap) : EntitySchema :=
  let ets := ets.toList
  let descendantMap := Data.Map.make (List.map (λ (k,v) =>
    have descendants := Data.Set.mk v.descendants.toList
    (k, descendants))
  ets)
  let ancestorMap := descendantsToAncestors descendantMap
  Data.Map.make (ets.map
    (λ (k,v) => (k,
      if v.enums.isEmpty then
      {
        ancestors := ancestorMap.find! k,
        attrs := Data.Map.make v.attrs.kvs,
        tags := v.tags,
      }
      else
      {
        ancestors := ancestorMap.find! k,
        attrs := Data.Map.empty,
        tags := none,
      }
      )))
end Cedar.Validation.Proto.EntityTypeWithTypesMap

namespace Cedar.Validation.Proto.EntityUidWithActionsIdMap
-- Needed for panic
deriving instance Inhabited for ActionSchemaEntry

@[inline]
def toActionSchema (acts : EntityUidWithActionsIdMap) : ActionSchema :=
  let acts := acts.toList
  let descendantMap := Data.Map.make (List.map (λ (k,v) =>
    have descendants := Data.Set.make v.descendants.toList
    (k, descendants))
  acts)
  let ancestorMap := descendantsToAncestors descendantMap
  Data.Map.make (List.map (λ (k,v) =>
    match v.context with
      | .record rty =>
        (k, {
          appliesToPrincipal := Data.Set.make v.appliesTo.principalApplySpec.toList,
          appliesToResource := Data.Set.make v.appliesTo.resourceApplySpec.toList,
          ancestors := ancestorMap.find! k,
          context := rty
        })
      | _ =>
        panic!("EntityUidWithActionsIdMap.toActionSchema : context should be record-typed")
    ) acts)
end Cedar.Validation.Proto.EntityUidWithActionsIdMap

namespace Cedar.Validation.Proto.ValidatorSchema
@[inline]
def mergeEntityTypes (result : ValidatorSchema) (x : EntityTypeWithTypesMap) : ValidatorSchema :=
  {result with
    ets := Field.merge result.ets x
  }

@[inline]
def mergeActionIds (result : ValidatorSchema) (x : EntityUidWithActionsIdMap) : ValidatorSchema :=
  {result with
    acts := Field.merge result.acts x
  }

@[inline]
def merge (x y : ValidatorSchema) : ValidatorSchema :=
  {
    ets := Field.merge x.ets y.ets
    acts := Field.merge x.acts y.acts
  }

@[inline]
def parseField (t : Tag) : BParsec (MergeFn ValidatorSchema) := do
  match t.fieldNum with
    | 1 =>
      let x : EntityTypeWithTypesMap ← Field.guardedParse t
      pure (pure $ mergeEntityTypes · x)
    | 2 =>
      let x : EntityUidWithActionsIdMap ← Field.guardedParse t
      pure (pure $ mergeActionIds · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message ValidatorSchema := {
  parseField := parseField
  merge := merge
}

@[inline]
def toSchema (v : ValidatorSchema) : Schema :=
  .mk v.ets.toEntitySchema v.acts.toActionSchema

end Cedar.Validation.Proto.ValidatorSchema


namespace Cedar.Validation.Schema

-- Note that Cedar.Validation.Schema is defined as
-- structure Schema where
--   ets : EntitySchema
--   acts : ActionSchema

@[inline]
private def ES.merge (x1 x2 : EntitySchema) : EntitySchema :=
  have x1 : Data.Map Spec.EntityType EntitySchemaEntry := x1
  have x2 : Data.Map Spec.EntityType EntitySchemaEntry := x2
  match x1.kvs with
    | [] => x2
    | _ => Data.Map.make (x2.kvs ++ x1.kvs)

@[inline]
private def AS.merge (x1 x2 : ActionSchema) : ActionSchema :=
  have x1 : Data.Map Spec.EntityUID ActionSchemaEntry := x1
  have x2 : Data.Map Spec.EntityUID ActionSchemaEntry := x2
  match x1.kvs with
    | [] => x2
    | _ => Data.Map.make (x2.kvs ++ x1.kvs)

@[inline]
def merge (x1 x2 : Schema) : Schema :=
  {
    ets := ES.merge x1.ets x2.ets
    acts := AS.merge x1.acts x2.acts
  }

deriving instance Inhabited for Schema
instance : Field Schema := Field.fromInterField Proto.ValidatorSchema.toSchema merge

end Cedar.Validation.Schema
