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
import Cedar.Validation.PartialRequestEntityValidator
import Protobuf.Message
import Protobuf.String

-- Message Dependencies
import CedarProto.ActionDecl
import CedarProto.EntityDecl
import CedarProto.Data

open Proto

namespace Cedar.Validation.Proto

structure Schema where
  ets : Repeated EntityDecl
  acts : Repeated ActionDecl
deriving Repr, Inhabited

deriving instance Hashable for Spec.Name
deriving instance Hashable for Spec.EntityType
deriving instance Hashable for Spec.EntityUID

/-
Faster Variant of `Set.make`, assuming we have hash set without duplicates but
with elements in arbitrary order. Not proven equivalent.
-/
private def setOfHashSet [BEq α] [Hashable α] [LT α] [DecidableLT α] (set : Std.HashSet α) : Data.Set α :=
  Data.Set.mk (set.toList.mergeSort (· < ·))

/-
The Rust data types store _descendant_ information for the entity type store
and action store, but _ancestor_ information for the entity store. The Lean
formalization standardizes on ancestor information.

The definitions and utility functions below are used to convert the descendant
representation to the ancestor representation.
-/
@[inline]
private def descendantsToAncestors [BEq α] [Hashable α] (descendants : Std.HashMap α (Std.HashSet α)) : Std.HashMap α (Std.HashSet α) :=
  descendants.fold (fun acc anc ds =>
    ds.fold (fun acc d => acc.alter d (some ∘ (·.getD Std.HashSet.emptyWithCapacity |>.insert anc))) acc)
    Std.HashMap.emptyWithCapacity

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
  let attrs ← attrs.mapM λ (k,v) => do
    let v ← v.map ProtoType.toCedarType |>.transpose
    .ok (k, v)
  .ok $ Data.mapOfArray attrs

/-- Decode definitions and `external` declarations. -/
def toPartialSchema (schema : Schema) : Except String Validation.PartialSchema := do
  let descendantMap := Std.HashMap.emptyWithCapacity.insertMany $ schema.ets.map λ decl => (decl.name.toName, Std.HashSet.ofArray $ decl.descendants.map Spec.Proto.Name.toName)
  let ancestorMap := descendantsToAncestors descendantMap
  let ets ← schema.ets.mapM λ decl => do
    let name := decl.name.toName
    let ancestors := setOfHashSet (ancestorMap.getD name (Std.HashSet.emptyWithCapacity 0))
    let pese : PartialEntitySchemaEntry ←
      if decl.external then .ok $ .external ancestors
      else if decl.enums.isEmpty then .ok $ .defined $ .standard {
        ancestors
        attrs := ← attrsToCedarType decl.attrs
        tags := ← option_transpose $ decl.tags.map ProtoType.toCedarType
      }
      else .ok $ .defined $ .enum $ Data.setOfArray decl.enums
    .ok (name, pese)
  let descendantMap := Std.HashMap.emptyWithCapacity.insertMany $ schema.acts.map λ decl => (decl.name, Std.HashSet.ofArray decl.descendants)
  let ancestorMap := descendantsToAncestors descendantMap
  let acts ← schema.acts.mapM λ decl => do
    let ancestors := setOfHashSet (ancestorMap.getD decl.name (Std.HashSet.emptyWithCapacity 0))
    let pase : PartialActionSchemaEntry ←
      if decl.external then .ok $ .external ancestors
      else .ok $ .defined {
        appliesToPrincipal := Data.setOfArray $ decl.principalTypes.map Spec.Proto.Name.toName
        appliesToResource := Data.setOfArray $ decl.resourceTypes.map Spec.Proto.Name.toName
        ancestors
        context := ← attrsToCedarType decl.context
      }
    .ok (decl.name, pase)
  .ok { ets := Data.mapOfArray ets, acts := Data.mapOfArray acts }

/-- Errors on any `external` declaration (RFC 116): every caller of this
requires a complete schema. -/
def toSchema (schema : Schema) : Except String Validation.Schema := do
  let ps ← toPartialSchema schema
  match ps.asSchema? with
  | some s => .ok s
  | none   => .error "schema declares entity types or actions `external` (RFC 116), but a complete schema is required here"

end Cedar.Validation.Proto.Schema


namespace Cedar.Validation.Schema

-- Note that Cedar.Validation.Schema is defined as
-- structure Schema where
--   ets : EntitySchema
--   acts : ActionSchema

def mergeMaps {α β} [LT α] [DecidableLT α] [BEq α] (x1 x2 : Data.Map α β) : Data.Map α β :=
  match x1.toList, x2.toList with
  | [], _      => x2
  | _, []      => x1
  | kvs1, kvs2 => Data.Map.mk $ (List.merge kvs1 kvs2 (·.1 == ·.1)).eraseRepsBy (·.1 == ·.1)

@[inline]
def merge (x1 x2 : Schema) : Schema :=
  {
    ets  := mergeMaps x1.ets x2.ets
    acts := mergeMaps x1.acts x2.acts
  }

deriving instance Inhabited for Schema
instance : Field Schema := Field.fromInterFieldFallible Proto.Schema.toSchema merge

end Cedar.Validation.Schema

namespace Cedar.Validation.PartialSchema

-- Same format as `Schema`, but keeps `external` declarations

@[inline]
def merge (x1 x2 : PartialSchema) : PartialSchema :=
  {
    ets  := Schema.mergeMaps x1.ets x2.ets
    acts := Schema.mergeMaps x1.acts x2.acts
  }

deriving instance Inhabited for PartialSchema
instance : Field PartialSchema := Field.fromInterFieldFallible Proto.Schema.toPartialSchema merge

end Cedar.Validation.PartialSchema
