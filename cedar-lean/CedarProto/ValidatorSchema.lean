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
import Cedar
import Protobuf.Message
import Protobuf.String

-- Message Dependencies
import CedarProto.ValidatorEntityType
import CedarProto.ValidatorActionId

open Proto

namespace Cedar.Validation.Proto

instance : Data.DecidableLT Spec.EntityTypeProto := by
  unfold Spec.EntityTypeProto
  apply inferInstance

/-
The Rust data types store _descendant_ information for the entity type store
and action store, but _ancestor_ information for the entity store. The Lean
formalization standardizes on ancestor information.

The definitions and utility functions below are used to convert the descendant
representation to the ancestor representation.
-/
private def findInMapValues [LT α] [DecidableEq α] [Data.DecidableLT α] (m : Data.Map α (Data.Set α)) (k₁ : α) : Data.Set α :=
  let setOfSets := List.map (λ (k₂,v) => if v.contains k₁ then Data.Set.singleton k₂ else Data.Set.empty) m.toList
  setOfSets.foldl (λ acc v => acc.union v) Data.Set.empty

private def descendantsToAncestors [LT α] [DecidableEq α] [Data.DecidableLT α] (descendants : Data.Map α (Data.Set α)) : Data.Map α (Data.Set α) :=
  Data.Map.make (List.map
    (λ (k,_) => (k, findInMapValues descendants k)) descendants.toList)

-- Add special "unspecified" entity type with no attributes or ancestors
private def addUnspecifiedEntityType (ets : EntitySchema) : EntitySchema :=
  let unspecifiedEntry : EntitySchemaEntry :=
  {
    ancestors := Data.Set.empty
    attrs := Data.Map.empty
  }
  Data.Map.make (ets.toList ++ [({id := "<Unspecified>", path := []}, unspecifiedEntry)])


def EntityTypeWithTypesMap := Array (Spec.EntityTypeProto × ValidatorEntityType)
  deriving Inhabited, Field

def EntityUidWithActionsIdMap := Array (Spec.EntityUID × ValidatorActionId)
  deriving Inhabited, Field
end Cedar.Validation.Proto

namespace Cedar.Validation.Proto.EntityTypeWithTypesMap
def toEntitySchema (ets : EntityTypeWithTypesMap) : EntitySchema :=
  let ets := ets.toList
  let descendantMap := Data.Map.make (List.map (λ (k,v) =>
    have descendants := Data.Set.mk v.descendants.toList
    (k, descendants))
  ets)
  let ancestorMap := descendantsToAncestors descendantMap
  addUnspecifiedEntityType (Data.Map.make (List.map
    (λ (k,v) => (k,
      {
        ancestors := ancestorMap.find! k,
        attrs := v.attrs
      })) ets))
end Cedar.Validation.Proto.EntityTypeWithTypesMap

namespace Cedar.Validation.EntitySchema
def merge (x1 x2: EntitySchema) : EntitySchema :=
  have x1 : Data.Map Spec.EntityType EntitySchemaEntry := x1
  have x2 : Data.Map Spec.EntityType EntitySchemaEntry := x2
  match x1.kvs with
    | [] => x2
    | _ => Data.Map.make (x2.kvs ++ x1.kvs)

instance : Field EntitySchema :=
  Field.fromInterField Proto.EntityTypeWithTypesMap.toEntitySchema merge
end Cedar.Validation.EntitySchema

namespace Cedar.Validation.Proto.EntityUidWithActionsIdMap
-- Needed for panic
deriving instance Inhabited for ActionSchemaEntry

def toActionSchema (acts: EntityUidWithActionsIdMap): ActionSchema :=
  let acts := acts.toList
  let descendantMap := Data.Map.make (List.map (λ (k,v) =>
    have descendants := Data.Set.mk v.descendants.toList
    (k, descendants))
  acts)
  let ancestorMap := descendantsToAncestors descendantMap
  Data.Map.make (List.map (λ (k,v) =>
    match v.context with
      | .record rty =>
        (k, {
          appliesToPrincipal := Data.Set.mk v.appliesTo.principalApplySpec.toList,
          appliesToResource := Data.Set.mk v.appliesTo.resourceApplySpec.toList,
          ancestors := ancestorMap.find! k,
          context := rty
        })
      | _ =>
        panic!("EntityUidWithActionsIdMap.toActionSchema: context should be record-typed")
    ) acts)
end Cedar.Validation.Proto.EntityUidWithActionsIdMap

namespace Cedar.Validation.ActionSchema
def merge (x1 x2: ActionSchema) : ActionSchema :=
  have x1 : Data.Map Spec.EntityUID ActionSchemaEntry := x1
  have x2 : Data.Map Spec.EntityUID ActionSchemaEntry := x2
  match x1.kvs with
    | [] => x2
    | _ => Data.Map.make (x2.kvs ++ x1.kvs)

instance : Field ActionSchema :=
  Field.fromInterField Proto.EntityUidWithActionsIdMap.toActionSchema merge
end Cedar.Validation.ActionSchema

namespace Cedar.Validation.Schema

-- Already defined
-- structure Schema where
--   ets : EntitySchema
--   acts : ActionSchema

@[inline]
def mergeEntityTypes (result: Schema) (x: EntitySchema) : Schema :=
  {result with
    ets := Field.merge result.ets x
  }

@[inline]
def mergeActionIds (result: Schema) (x: ActionSchema): Schema :=
  {result with
    acts := Field.merge result.acts x
  }

@[inline]
def merge (x y: Schema) : Schema :=
  {x with
    ets := Field.merge x.ets y.ets
    acts := Field.merge x.acts y.acts
  }

def parseField (t: Tag) : BParsec (StateM Schema Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntitySchema) t.wireType
      let x: EntitySchema ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEntityTypes s x))
    | 2 =>
      (@Field.guardWireType ActionSchema) t.wireType
      let x: ActionSchema ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeActionIds s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

deriving instance Inhabited for Schema
instance : Message Schema := {
  parseField := parseField
  merge := merge
}

end Cedar.Validation.Schema
