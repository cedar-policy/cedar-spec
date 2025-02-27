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
  ets : Array EntityDecl
  acts : Array ActionDecl
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

private def attrsToCedarType (attrs : Proto.Map String (Qualified ProtoType)) : Except String (Data.Map Spec.Attr (Qualified CedarType)) := do
  let attrs ← attrs.toList.mapM λ (k,v) => do
    let v ← v.map ProtoType.toCedarType |>.transpose
    .ok (k, v)
  .ok $ Data.Map.make attrs

/-- was surprised this isn't in the stdlib -/
def option_transpose : Option (Except ε α) → Except ε (Option α)
  | none => .ok none
  | some (.ok a) => .ok (some a)
  | some (.error e) => .error e

def toSchema (schema : Schema) : Except String Validation.Schema := do
  let ets := schema.ets.toList
  let descendantMap := ets.map λ decl => (decl.name, Data.Set.make decl.descendants.toList)
  let ancestorMap := descendantsToAncestors descendantMap
  let ets ← ets.mapM λ decl => do
    let ese : EntitySchemaEntry ←
      if decl.enums.isEmpty then .ok $ .standard {
        ancestors := ancestorMap.find! decl.name
        attrs := ← attrsToCedarType decl.attrs
        tags := ← option_transpose $ decl.tags.map ProtoType.toCedarType
      }
      else .ok $ .enum $ Cedar.Data.Set.make decl.enums.toList
    .ok (decl.name, ese)
  let acts := schema.acts.toList
  let descendantMap := acts.map λ decl => (decl.name, Data.Set.make decl.descendants.toList)
  let ancestorMap := descendantsToAncestors descendantMap
  let acts ← acts.mapM λ decl => do
    .ok (decl.name, {
      appliesToPrincipal := Data.Set.make decl.principalTypes.toList
      appliesToResource := Data.Set.make decl.resourceTypes.toList
      ancestors := ancestorMap.find! decl.name
      context := ← attrsToCedarType decl.context
    })
  .ok { ets := Data.Map.make ets, acts := Data.Map.make acts }

@[inline]
def mergeEntityDecls (result : Schema) (x : Array EntityDecl) : Schema :=
  {result with
    ets := result.ets ++ x
  }

@[inline]
def mergeActionDecls (result : Schema) (x : Array ActionDecl) : Schema :=
  {result with
    acts := result.acts ++ x
  }

@[inline]
def merge (x y : Schema) : Schema :=
  {
    ets := x.ets ++ y.ets
    acts := x.acts ++ y.acts
  }

@[inline]
def parseField (t : Tag) : BParsec (MergeFn Schema) := do
  match t.fieldNum with
    | 1 =>
      let x : Repeated EntityDecl ← Field.guardedParse t
      pure (pure $ mergeEntityDecls · x)
    | 2 =>
      let x : Repeated ActionDecl ← Field.guardedParse t
      pure (pure $ mergeActionDecls · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message Schema := {
  parseField := parseField
  merge := merge
}

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
    | _ => Data.Map.make (x2.kvs ++ x1.kvs)

@[inline]
private def AS.merge (x1 x2 : ActionSchema) : ActionSchema :=
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
instance : Field Schema := Field.fromInterFieldFallible Proto.Schema.toSchema merge

end Cedar.Validation.Schema
