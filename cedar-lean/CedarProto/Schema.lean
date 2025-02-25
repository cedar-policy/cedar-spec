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
import CedarProto.ActionDecl
import CedarProto.EntityDecl

open Proto

namespace Cedar.Validation.Proto

def EntityTypeToEntityDeclMap := Proto.Map Spec.Name EntityDecl
  deriving Inhabited, Field

def EntityUidToActionDeclMap := Proto.Map Spec.EntityUID ActionDecl
  deriving Inhabited, Field

structure Schema where
  ets : EntityTypeToEntityDeclMap
  acts : EntityUidToActionDeclMap
deriving Inhabited

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

namespace Cedar.Validation.Proto.EntityTypeToEntityDeclMap
@[inline]
def toEntitySchema (ets : EntityTypeToEntityDeclMap) : EntitySchema :=
  let ets := ets.toList
  let descendantMap := Data.Map.make $
    ets.map λ (k,v) => (k, Data.Set.mk v.descendants.toList)
  let ancestorMap := descendantsToAncestors descendantMap
  Data.Map.make $ ets.map λ (k,v) =>
    (k,
      if v.enums.isEmpty then
      .standard {
        ancestors := ancestorMap.find! k
        attrs := Data.Map.make v.attrs.toList
        tags := v.tags
      }
      else
      .enum $ Cedar.Data.Set.mk v.enums.toList
    )
end Cedar.Validation.Proto.EntityTypeToEntityDeclMap

namespace Cedar.Validation.Proto.EntityUidToActionDeclMap
-- Needed for panic
deriving instance Inhabited for ActionSchemaEntry

@[inline]
def toActionSchema (acts : EntityUidToActionDeclMap) : ActionSchema :=
  let acts := acts.toList
  let descendantMap := Data.Map.make $
    acts.map λ (k,v) => (k, Data.Set.make v.descendants.toList)
  let ancestorMap := descendantsToAncestors descendantMap
  Data.Map.make $ acts.map λ (k,v) =>
    match v.context with
      | .record rty =>
        (k, {
          appliesToPrincipal := Data.Set.make v.principal_types.toList,
          appliesToResource := Data.Set.make v.resource_types.toList,
          ancestors := ancestorMap.find! k,
          context := rty
        })
      | _ => panic!("EntityUidWithActionsIdMap.toActionSchema : context should be record-typed")
end Cedar.Validation.Proto.EntityUidToActionDeclMap

namespace Cedar.Validation.Proto.Schema
@[inline]
def mergeEntityTypes (result : Schema) (x : EntityTypeToEntityDeclMap) : Schema :=
  {result with
    ets := Field.merge result.ets x
  }

@[inline]
def mergeActionIds (result : Schema) (x : EntityUidToActionDeclMap) : Schema :=
  {result with
    acts := Field.merge result.acts x
  }

@[inline]
def merge (x y : Schema) : Schema :=
  {
    ets := Field.merge x.ets y.ets
    acts := Field.merge x.acts y.acts
  }

@[inline]
def parseField (t : Tag) : BParsec (MergeFn Schema) := do
  match t.fieldNum with
    | 1 =>
      let x : EntityTypeToEntityDeclMap ← Field.guardedParse t
      pure (pure $ mergeEntityTypes · x)
    | 2 =>
      let x : EntityUidToActionDeclMap ← Field.guardedParse t
      pure (pure $ mergeActionIds · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message Schema := {
  parseField := parseField
  merge := merge
}

@[inline]
def toSchema (v : Schema) : Validation.Schema :=
  .mk v.ets.toEntitySchema v.acts.toActionSchema

end Cedar.Validation.Proto.Schema


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
instance : Field Schema := Field.fromInterField Proto.Schema.toSchema merge

end Cedar.Validation.Schema
