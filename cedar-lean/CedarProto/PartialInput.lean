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

/-! ### Explicit recursive partial records -/

inductive AttrStateKind where
  | unknown
  | value
  | present
  | absent
  | partialRecord
deriving Inhabited, Repr, DecidableEq

namespace AttrStateKind
@[inline]
def fromInt (n : Int) : Except String AttrStateKind :=
  match n with
  | 0 => .ok .unknown
  | 1 => .ok .value
  | 2 => .ok .present
  | 3 => .ok .absent
  | 4 => .ok .partialRecord
  | n => .error s!"Field {n} does not exist in enum AttrStateKind"

instance : ProtoEnum AttrStateKind := { fromInt := fromInt }
end AttrStateKind

mutual

/-- The wire form of one attribute's state. -/
inductive AttrState where
  | mk (kind : AttrStateKind) (value : Option Expr) (record : List AttrStateEntry)

/-- The wire form of one entry in a partial record. -/
inductive AttrStateEntry where
  | mk (key : String) (state : Option AttrState)

end

instance : Inhabited AttrState where
  default := .mk .unknown .none []

instance : Inhabited AttrStateEntry where
  default := .mk "" .none

namespace AttrState
def kind : AttrState → AttrStateKind | .mk k _ _ => k
def value : AttrState → Option Expr | .mk _ v _ => v
def record : AttrState → List AttrStateEntry | .mk _ _ r => r

def mergeKind (s : AttrState) (k : AttrStateKind) : AttrState := .mk k s.value s.record
def mergeValue (s : AttrState) (v : Expr) : AttrState := .mk s.kind (.some v) s.record
def mergeRecord (s : AttrState) (r : Array AttrStateEntry) : AttrState :=
  .mk s.kind s.value (s.record ++ r.toList)

def merge (x y : AttrState) : AttrState :=
  .mk (if y.kind == .unknown then x.kind else y.kind)
      (y.value <|> x.value)
      (x.record ++ y.record)
end AttrState

namespace AttrStateEntry
def key : AttrStateEntry → String | .mk k _ => k
def state : AttrStateEntry → Option AttrState | .mk _ s => s

def mergeKey (e : AttrStateEntry) (k : String) : AttrStateEntry := .mk k e.state
def mergeState (e : AttrStateEntry) (s : AttrState) : AttrStateEntry := .mk e.key (.some s)

def merge (x y : AttrStateEntry) : AttrStateEntry :=
  .mk (if y.key == "" then x.key else y.key) (y.state <|> x.state)
end AttrStateEntry

mutual

partial def AttrState.parseField (t : Proto.Tag) : BParsec (MergeFn AttrState) := do
  have : Message AttrStateEntry :=
    { parseField := AttrStateEntry.parseField, merge := AttrStateEntry.merge }
  match t.fieldNum with
  | 1 =>
    let x : AttrStateKind ← Field.guardedParse t
    pureMergeFn (AttrState.mergeKind · x)
  | 2 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (AttrState.mergeValue · x)
  | 3 =>
    let x : Repeated AttrStateEntry ← Field.guardedParse t
    pureMergeFn (AttrState.mergeRecord · x)
  | _ =>
    t.wireType.skip
    pure ignore

partial def AttrStateEntry.parseField (t : Proto.Tag) : BParsec (MergeFn AttrStateEntry) := do
  have : Message AttrState := { parseField := AttrState.parseField, merge := AttrState.merge }
  match t.fieldNum with
  | 1 =>
    let x : String ← Field.guardedParse t
    pureMergeFn (AttrStateEntry.mergeKey · x)
  | 2 =>
    let x : AttrState ← Field.guardedParse t
    pureMergeFn (AttrStateEntry.mergeState · x)
  | _ =>
    t.wireType.skip
    pure ignore

end

instance : Message AttrState :=
  { parseField := AttrState.parseField, merge := AttrState.merge }
instance : Message AttrStateEntry :=
  { parseField := AttrStateEntry.parseField, merge := AttrStateEntry.merge }

partial def AttrState.toAttrState : AttrState → Except String TPE.AttrState
  | .mk kind value record =>
    match kind with
    | .unknown => .ok .unknown
    | .present => .ok .present
    | .absent  => .ok .absent
    | .value =>
      match value with
      | .some e => do .ok (TPE.AttrState.value (← Spec.Value.exprToValue e))
      | .none   => .error "AttrState of kind VALUE carries no value"
    | .partialRecord => do
      let pairs ← record.mapM λ e =>
        match e with
        | .mk k (.some st) => do .ok (k, ← AttrState.toAttrState st)
        | .mk k .none      => .error s!"AttrState record entry {k} carries no state"
      .ok (TPE.AttrState.partialRecord (Data.Map.make pairs))

/-! ### PartialRecord -/

structure PartialRecord where
  entries : Repeated AttrStateEntry
deriving Inhabited

namespace PartialRecord

instance : Message PartialRecord where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t entries (update entries)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := { entries := Field.merge x.entries y.entries }

def toPartialRecord (r : PartialRecord) : Except String TPE.PartialRecord := do
  let pairs ← r.entries.toList.mapM λ e =>
    match e with
    | .mk k (.some st) => do .ok (k, ← AttrState.toAttrState st)
    | .mk k .none      => .error s!"PartialRecord entry {k} carries no state"
  .ok (Data.Map.make pairs)

end PartialRecord

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
  context : Option PartialRecord := none
deriving Inhabited

namespace PartialRequest

instance : Message PartialRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t principal (update principal)
    | 2 => parseFieldElement t action (update action)
    | 3 => parseFieldElement t resource (update resource)
    | 4 => parseFieldElement t context (update context)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    principal := Field.merge x.principal y.principal
    action := Field.merge x.action y.action
    resource := Field.merge x.resource y.resource
    context := Field.merge x.context y.context
  }

def toPartialRequest (p : PartialRequest) : Except String TPE.PartialRequest := do
  let context ← p.context.mapM PartialRecord.toPartialRecord
  .ok {
    principal := p.principal.toPartialEntityUID
    action := p.action
    resource := p.resource.toPartialEntityUID
    context
  }

end PartialRequest

/-! ### PartialEntity -/

structure EntityUidSet where
  uids : Repeated EntityUID
deriving Inhabited

namespace EntityUidSet

instance : Message EntityUidSet where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t uids (update uids)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := { uids := Field.merge x.uids y.uids }

end EntityUidSet

structure PartialEntity where
  uid : EntityUID
  attrs : Option PartialRecord := none
  ancestors : Option EntityUidSet := none
  tags : Option PartialRecord := none
deriving Inhabited

namespace PartialEntity

instance : Message PartialEntity where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t uid (update uid)
    | 2 => parseFieldElement t attrs (update attrs)
    | 3 => parseFieldElement t ancestors (update ancestors)
    | 4 => parseFieldElement t tags (update tags)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    uid := Field.merge x.uid y.uid
    attrs := Field.merge x.attrs y.attrs
    ancestors := Field.merge x.ancestors y.ancestors
    tags := Field.merge x.tags y.tags
  }

def toPartialEntity (p : PartialEntity) : Except String (EntityUID × TPE.PartialEntityData) := do
  let attrs ← p.attrs.mapM PartialRecord.toPartialRecord
  let tags ← p.tags.mapM PartialRecord.toPartialRecord
  let ancestors := p.ancestors.map (Data.Set.make ·.uids.toList)
  .ok (p.uid, TPE.PartialEntityData.mk attrs ancestors tags)

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

def toPartialEntities (e : PartialEntities) : Except String TPE.PartialEntities := do
  let pairs ← e.entities.toList.mapM PartialEntity.toPartialEntity
  .ok (Data.Map.make pairs)

end PartialEntities

end Cedar.TPE.Proto
