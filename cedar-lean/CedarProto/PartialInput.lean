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
import Cedar.TPE.Input
import Protobuf.Message
import Protobuf.Structure

-- Message Dependencies
import CedarProto.EntityUID
import CedarProto.Expr
import CedarProto.Value



open Proto

namespace Cedar.TPE.Proto

open Cedar.Data
open Cedar.Spec

/-! ### PartialEntityUID -/

structure PartialEntityUID where
  ty : EntityType
  id : Option String := none
deriving Inhabited

namespace PartialEntityUID

instance : Message PartialEntityUID where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t ty (update ty)
    | 2 => parseFieldElement t id (update id)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    ty := Field.merge x.ty y.ty
    id := Field.merge x.id y.id
  }

def toPartialEntityUID (p : PartialEntityUID) : TPE.PartialEntityUID :=
  { ty := p.ty, id := p.id }

end PartialEntityUID

/-! ### PartialRequest -/

structure PartialRequest where
  principal : PartialEntityUID
  action : EntityUID
  resource : PartialEntityUID
  context : Proto.Map String Expr := default
  hasContext : Bool := false
deriving Inhabited

namespace PartialRequest

instance : Message PartialRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t principal (update principal)
    | 2 => parseFieldElement t action (update action)
    | 3 => parseFieldElement t resource (update resource)
    | 4 => parseFieldElement t context (update context)
    | 5 => parseFieldElement t hasContext (update hasContext)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    principal  := Field.merge x.principal  y.principal
    action     := Field.merge x.action     y.action
    resource   := Field.merge x.resource   y.resource
    context    := Field.merge x.context    y.context
    hasContext  := Field.merge x.hasContext  y.hasContext
  }

def toPartialRequest (p : PartialRequest) : Except String TPE.PartialRequest := do
  let context ← if p.hasContext then do
      let pairs ← p.context.mapM fun (k, v) => do .ok (k, ← Spec.Value.exprToValue v)
      .ok (some (Data.Map.make pairs.toList))
    else .ok none
  .ok {
    principal := p.principal.toPartialEntityUID
    action    := p.action
    resource  := p.resource.toPartialEntityUID
    context   := context
  }

end PartialRequest

/-! ### PartialEntityData -/

structure PartialEntity where
  uid : EntityUID
  attrs : Proto.Map String Expr := default
  ancestors : Repeated EntityUID := default
  tags : Proto.Map String Expr := default
  hasAttrs : Bool := false
  hasAncestors : Bool := false
  hasTags : Bool := false
deriving Inhabited

namespace PartialEntity

instance : Message PartialEntity where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t uid (update uid)
    | 2 => parseFieldElement t attrs (update attrs)
    | 3 => parseFieldElement t ancestors (update ancestors)
    | 4 => parseFieldElement t tags (update tags)
    | 5 => parseFieldElement t hasAttrs (update hasAttrs)
    | 6 => parseFieldElement t hasAncestors (update hasAncestors)
    | 7 => parseFieldElement t hasTags (update hasTags)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    uid          := Field.merge x.uid          y.uid
    attrs        := Field.merge x.attrs        y.attrs
    ancestors    := Field.merge x.ancestors    y.ancestors
    tags         := Field.merge x.tags         y.tags
    hasAttrs     := Field.merge x.hasAttrs     y.hasAttrs
    hasAncestors := Field.merge x.hasAncestors y.hasAncestors
    hasTags      := Field.merge x.hasTags      y.hasTags
  }

end PartialEntity

/-! ### PartialEntities -/

structure PartialEntities where
  entities : Repeated PartialEntity
deriving Inhabited

instance : HAppend PartialEntities PartialEntities PartialEntities where
  hAppend x y := { entities := x.entities ++ y.entities }

namespace PartialEntities

instance : Message PartialEntities where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t entities (update entities)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge := (· ++ ·)

private def convertMap (has : Bool) (m : Proto.Map String Expr) : Except String (Option (Data.Map Attr Value)) :=
  if has then do
    let pairs ← m.mapM fun (k, v) => do .ok (k, ← Spec.Value.exprToValue v)
    .ok (some (Data.Map.make pairs.toList))
  else .ok none

def toPartialEntities (e : PartialEntities) : Except String TPE.PartialEntities := do
  let pairs ← e.entities.toList.mapM fun pe => do
    let attrs ← convertMap pe.hasAttrs pe.attrs
    let ancestors := if pe.hasAncestors then some (Data.Set.make pe.ancestors.toList) else none
    let tags ← convertMap pe.hasTags pe.tags
    .ok (pe.uid, TPE.PartialEntityData.mk attrs ancestors tags)
  .ok (Data.Map.make pairs)

end PartialEntities

end Cedar.TPE.Proto

/-! ### Field instances -/

namespace Cedar.TPE

open Cedar.Data

def PartialRequest.merge (x y : PartialRequest) : PartialRequest := {
  principal := { ty := Proto.Field.merge x.principal.ty y.principal.ty, id := y.principal.id <|> x.principal.id }
  action    := Proto.Field.merge x.action y.action
  resource  := { ty := Proto.Field.merge x.resource.ty y.resource.ty, id := y.resource.id <|> x.resource.id }
  context   := y.context <|> x.context
}

instance : Proto.Field PartialRequest :=
  Proto.Field.fromInterFieldFallible Proto.PartialRequest.toPartialRequest PartialRequest.merge

def PartialEntities.merge (x y : PartialEntities) : PartialEntities :=
  match x.toList, y.toList with
  | [], _ => y
  | _, [] => x
  | _, _  => Data.Map.make (x.toList ++ y.toList)

instance : Proto.Field PartialEntities :=
  Proto.Field.fromInterFieldFallible Proto.PartialEntities.toPartialEntities PartialEntities.merge

end Cedar.TPE
