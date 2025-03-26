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

structure Schema where
  ets : Repeated EntityDecl
  acts : Repeated ActionDecl
deriving Repr, Inhabited

/-
The Rust data types store _descendant_ information for the entity type store
and action store, but _ancestor_ information for the entity store. The Lean
formalization standardizes on ancestor information.

The definitions and utility functions below are used to convert the descendant
representation to the ancestor representation.
-/
@[inline]
private def findInMapValues [LT α] [DecidableEq α] [DecidableLT α] (m : List (α × (Data.Set α))) (k₁ : α) : Data.Set α :=
  let setOfSets := m.map λ (k₂,v) => if v.contains k₁ then Data.Set.singleton k₂ else Data.Set.empty
  setOfSets.foldl Data.Set.union Data.Set.empty

@[inline]
private def descendantsToAncestors [LT α] [DecidableEq α] [DecidableLT α] (descendants : List (α × (Data.Set α))) : Data.Map α (Data.Set α) :=
  Data.Map.make (descendants.map λ (k,_) => (k, findInMapValues descendants k))

namespace Schema

instance : Message Schema := {
  parseField (t : Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t ets (update ets)
    | 2 => parseFieldElement t acts (update acts)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    ets  := Field.merge x.ets  y.ets
    acts := Field.merge x.acts y.acts
  }
}

/-- was surprised this isn't in the stdlib -/
def option_transpose : Option (Except ε α) → Except ε (Option α)
  | none => .ok none
  | some (.ok a) => .ok (some a)
  | some (.error e) => .error e

private def attrsToCedarType (attrs : Proto.Map String (Qualified ProtoType)) : Except String (Data.Map Spec.Attr (Qualified CedarType)) := do
  let attrs ← attrs.toList.mapM λ (k,v) => do
    let v ← v.map ProtoType.toCedarType |>.transpose
    .ok (k, v)
  .ok $ Data.Map.make attrs

def toSchema (schema : Schema) : Except String Validation.Schema := do
  let ets := schema.ets.toList
  let descendantMap := ets.map λ decl => (decl.name.toName, Data.Set.make $ decl.descendants.toList.map Spec.Proto.Name.toName)
  let ancestorMap := descendantsToAncestors descendantMap
  let ets ← ets.mapM λ decl => do
    let name := decl.name.toName
    let ese : EntitySchemaEntry ←
      if decl.enums.isEmpty then .ok $ .standard {
        ancestors := ancestorMap.find! name
        attrs := ← attrsToCedarType decl.attrs
        tags := ← option_transpose $ decl.tags.map ProtoType.toCedarType
      }
      else .ok $ .enum $ Cedar.Data.Set.make decl.enums.toList
    .ok (name, ese)
  let acts := schema.acts.toList
  let descendantMap := acts.map λ decl => (decl.name, Data.Set.make decl.descendants.toList)
  let ancestorMap := descendantsToAncestors descendantMap
  let acts ← acts.mapM λ decl => do
    .ok (decl.name, {
      appliesToPrincipal := Data.Set.make $ decl.principalTypes.toList.map Spec.Proto.Name.toName
      appliesToResource := Data.Set.make $ decl.resourceTypes.toList.map Spec.Proto.Name.toName
      ancestors := ancestorMap.find! decl.name
      context := ← attrsToCedarType decl.context
    })
  .ok { ets := Data.Map.make ets, acts := Data.Map.make acts }

end Cedar.Validation.Proto.Schema


namespace Cedar.Validation.Schema

-- Note that Cedar.Validation.Schema is defined as
-- structure Schema where
--   ets : EntitySchema
--   acts : ActionSchema

@[inline]
private def ES.merge (x1 x2 : EntitySchema) : EntitySchema :=
  match x1.kvs with
  | [] => x2
  | _  => Data.Map.make (x2.kvs ++ x1.kvs)

@[inline]
private def AS.merge (x1 x2 : ActionSchema) : ActionSchema :=
  match x1.kvs with
  | [] => x2
  | _  => Data.Map.make (x2.kvs ++ x1.kvs)

@[inline]
def merge (x1 x2 : Schema) : Schema :=
  {
    ets  := ES.merge x1.ets x2.ets
    acts := AS.merge x1.acts x2.acts
  }

deriving instance Inhabited for Schema
instance : Field Schema := Field.fromInterFieldFallible Proto.Schema.toSchema merge

end Cedar.Validation.Schema
