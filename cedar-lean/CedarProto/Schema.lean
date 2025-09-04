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

deriving instance Hashable for Spec.Name
deriving instance Hashable for Spec.EntityType
deriving instance Hashable for Spec.EntityUID

/-
Fast variant of `Set.make`, assuming we start with starting with an array we can
sort in place. Not proven equivalent.
-/
private def setOfArray {α} [LT α] [DecidableLT α] [BEq α] (elts : Array α) : Data.Set α :=
  Data.Set.mk (elts.qsort (· < ·)).eraseReps.toList

/-
Faster Variant of `Set.make`, assuming we have hash set without duplicates but
with elements in arbitrary order. Not proven equivalent.
-/
private def setOfHashSet [BEq α] [Hashable α] [LT α] [DecidableLT α] (set : Std.HashSet α) : Data.Set α :=
  Data.Set.mk (set.toList.mergeSort (· < ·))

/-
Faster variant of `Map.make`, assuming we start with an array we can sort in
place. Not proven equivalent.
-/
private def mapOfArray {α β} [LT α] [DecidableLT α] [BEq α] (kvs : Array (α × β)) : Data.Map α β :=
  Data.Map.mk ((kvs.qsort (·.1 < ·.1)).toList.eraseRepsBy (·.1 == ·.1))

/-
The Rust data types store _descendant_ information for the entity type store
and action store, but _ancestor_ information for the entity store. The Lean
formalization standardizes on ancestor information.

The definitions and utility functions below are used to convert the descendant
representation to the ancestor representation.
-/
@[inline]
private def descendantsToAncestors [BEq α] [Hashable α] (descendants : Std.HashMap α (Std.HashSet α)) : Std.HashMap α (Std.HashSet α) :=
  descendants.fold (fun acc k _ => acc.insert k (findInMapValues k)) Std.HashMap.emptyWithCapacity
where
  findInMapValues (k₁ : α) : Std.HashSet α :=
    descendants.fold (fun acc k₂ v => if v.contains k₁ then acc.insert k₂ else acc) Std.HashSet.emptyWithCapacity

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
  .ok $ mapOfArray attrs

def toSchema (schema : Schema) : Except String Validation.Schema := do
  let descendantMap := Std.HashMap.emptyWithCapacity.insertMany $ schema.ets.map λ decl => (decl.name.toName, Std.HashSet.ofArray $ decl.descendants.map Spec.Proto.Name.toName)
  let ancestorMap := descendantsToAncestors descendantMap
  let ets ← schema.ets.mapM λ decl => do
    let name := decl.name.toName
    let ese : EntitySchemaEntry ←
      if decl.enums.isEmpty then .ok $ .standard {
        ancestors := setOfHashSet (ancestorMap.getD name (Std.HashSet.emptyWithCapacity 0))
        attrs := ← attrsToCedarType decl.attrs
        tags := ← option_transpose $ decl.tags.map ProtoType.toCedarType
      }
      else .ok $ .enum $ setOfArray decl.enums
    .ok (name, ese)
  let descendantMap := Std.HashMap.emptyWithCapacity.insertMany $ schema.acts.map λ decl => (decl.name, Std.HashSet.ofArray decl.descendants)
  let ancestorMap := descendantsToAncestors descendantMap
  let acts ← schema.acts.mapM λ decl => do
    .ok (decl.name, {
      appliesToPrincipal := setOfArray $ decl.principalTypes.map Spec.Proto.Name.toName
      appliesToResource := setOfArray $ decl.resourceTypes.map Spec.Proto.Name.toName
      ancestors := setOfHashSet (ancestorMap.getD decl.name (Std.HashSet.emptyWithCapacity 0))
      context := ← attrsToCedarType decl.context
    })
  .ok { ets := mapOfArray ets, acts := mapOfArray acts }

end Cedar.Validation.Proto.Schema


namespace Cedar.Validation.Schema

-- Note that Cedar.Validation.Schema is defined as
-- structure Schema where
--   ets : EntitySchema
--   acts : ActionSchema

private def mergeMaps {α β} [LT α] [DecidableLT α] [BEq α] (x1 x2 : Data.Map α β) : Data.Map α β :=
  match x1.kvs, x2.kvs with
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
