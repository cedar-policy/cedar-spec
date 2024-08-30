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
import Protobuf.Enum
import Protobuf.Message
import Protobuf.Map
import Protobuf.String

-- Message Dependencies
import CedarProto.Name
import CedarProto.EntityType

open Proto

namespace Cedar.Validation

namespace Proto
-- AttributeType <-> QualifiedType
-- Attributes <-> RecordType
def EntityRecordKind := CedarType
  deriving Inhabited

-- We create a type for every constructor, as we'll go
-- about parsing the message differently for each
def EntityRecordKind.Record := EntityRecordKind
instance : Inhabited EntityRecordKind.Record where
  default := .record default

def EntityRecordKind.Entity := EntityRecordKind
instance : Inhabited EntityRecordKind.Entity where
  default := .entity default

def EntityRecordKind.ActionEntity := EntityRecordKind
instance : Inhabited EntityRecordKind.ActionEntity where
  default := .entity default
end Proto

namespace RecordType
def mergeAttrs (result: RecordType) (x: Array (String × QualifiedType)) : RecordType :=
  Cedar.Data.Map.mk (result.kvs ++ x.toList)

def merge (x1 x2: RecordType) : RecordType :=
  Cedar.Data.Map.mk (x1.kvs ++ x2.kvs)

end RecordType

namespace QualifiedType
def mergeType (result: QualifiedType) (x: CedarType) : QualifiedType :=
  -- Replace the type information, keep the qualified constructor
  match result with
    | .required _ => .required x
    | .optional _ => .optional x

def mergeIsRequired (result: QualifiedType) (x: Bool) : QualifiedType :=
  -- Replace constructor, keep data
  if x then
    .required result.getType
  else
    .optional result.getType

-- NOTE: parseField and merge both require mutual recursion and can be found
-- at the end of this file.
end QualifiedType

namespace Proto.EntityRecordKind

inductive Ty where
  | AnyEntity

namespace Ty
def fromInt (n: Int) : Except String Ty :=
  match n with
    | 0 => .ok .AnyEntity
    | n => .error s!"Field {n} does not exist in enum"
instance : ProtoEnum Ty where
  fromInt := fromInt
end Ty

namespace Record
@[inline]
def mergeAttributes (result: Record) (m2: RecordType): Record :=
  have m2 : Cedar.Data.Map Cedar.Spec.Attr (Qualified CedarType) := m2
  match result with
    | .record m1 => .record (Cedar.Data.Map.make (m2.kvs ++ m1.kvs))
    | _ => panic!("EntityRecordKind.Record is not set to the CedarType.record constructor")

@[inline]
def merge (x1 x2: Record): Record :=
  match x1, x2 with
    | .record m1, .record m2 => match m1.kvs with
      | [] => .record m2
      | _ => .record (Cedar.Data.Map.make (m2.kvs ++ m1.kvs))
    | _, _ => panic!("EntityRecordKind.Record is not set to the CedarType.record constructor")

-- parseField requires mutual recursion and can be found at the end of the file
end Record

namespace Entity
def mergeE (result: Entity) (e2: Spec.EntityTypeProto): Entity :=
  match result with
    | .entity e1 => .entity (Field.merge e1 e2)
    | _ => panic!("Entity expected CedarType constructor to be .entity")

def merge (x1 x2: Entity): Entity :=
  match x1, x2 with
    | .entity e1, .entity e2 => .entity (Field.merge e1 e2)
    | _, _ => panic!("Entity expected CedarType constructor to be .entity")

def parseField (t: Tag) : BParsec (StateM Entity Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Spec.EntityTypeProto) t.wireType
      let x: Spec.EntityTypeProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeE s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message Entity := {
  parseField := parseField
  merge := merge
}
end Entity

namespace ActionEntity
-- Note: Ignore the Attributes in the ActionEntity message
-- since this isn't represented in the formal model

def mergeName (result: ActionEntity) (e2: Spec.EntityTypeProto) : ActionEntity :=
  match result with
    | .entity e1 => .entity (Field.merge e1 e2)
    | _ => panic!("ActionEntity expected CedarType constructor to be .entity")

def merge (x1 x2: ActionEntity) : ActionEntity :=
  match x1, x2 with
    | .entity e1, .entity e2 => .entity (Field.merge e1 e2)
    | _, _ => panic!("ActionEntity expected CedarType constructor to be .entity")

def parseField (t: Tag) : BParsec (StateM ActionEntity Unit) :=
do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Spec.EntityTypeProto) t.wireType
      let x: Spec.EntityTypeProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeName s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ActionEntity := {
  parseField := parseField
  merge := merge
}
end ActionEntity

@[inline]
def mergeTy (_: EntityRecordKind) (x: Ty) : EntityRecordKind :=
  match x with
   | .AnyEntity => panic!("Not Implemented")

@[inline]
def mergeRecord (result: EntityRecordKind) (x: Record): EntityRecordKind :=
  have m2 := match x with
      | .record m => m
      | _ => panic!("EntityRecordKind.Record is not set to the CedarType.record constructor")
  match result with
    | .record m1 => match m1.kvs with
      | [] => .record m2
      | _ => .record (Cedar.Data.Map.make (m2.kvs ++ m1.kvs))
    | _ => .record m2

@[inline]
def mergeEntity (result: EntityRecordKind) (x: Entity): EntityRecordKind :=
  have e2 := match x with
    | .entity e => e
    | _ => panic!("EntityRecordKind.Entity is not set to the CedarType.entity constructor")
  match result with
    | .entity e1 => .entity (Field.merge e1 e2)
    | _ => .entity e2

@[inline]
def mergeActionEntity (result: EntityRecordKind) (x: ActionEntity) : EntityRecordKind :=
  have e2 := match x with
    | .entity e => e
    | _ => panic!("EntityRecordKind.ActionEntity is not set to the CedarType.entity constructor")
  match result with
    | .entity e1 => .entity (Field.merge e1 e2)
    | _ => .entity e2

@[inline]
def merge (x1 x2 : EntityRecordKind): EntityRecordKind :=
  match x2 with
  | .entity e2 => match x1 with
    | .entity e1 => .entity (Field.merge e1 e2)
    | .record _ => x2
    | _ => panic!("Expected EntityRecordKind to be CedarType.record or CedarType.entity")
  | .record m2 => match x1 with
    | .record m1 => match m1.kvs with
      | [] => .record m2
      | _ => .record (Cedar.Data.Map.make (m2.kvs ++ m1.kvs))
    | .entity _ => x2
    | _ => panic!("Expected EntityRecordKind to be CedarType.record or CedarType.entity")
  | _ => panic!("Expected EntityRecordKind to be CedarType.record or CedarType.entity")

-- NOTE: parseField requires mutual recursion and can be found at the end of the file
end Proto.EntityRecordKind

namespace CedarType

-- Already defined in Cedar.Validation
-- inductive CedarType where
--   | bool (bty : BoolType)
--   | int
--   | string
--   | entity (ety : EntityType)
--   | set (ty : CedarType)
--   | record (rty : Map Attr (Qualified CedarType))
--   | ext (xty : ExtType)\

inductive Ty where
  | never
  | true
  | false
  | emptySetType
  | bool
  | string
  | long
deriving Inhabited

namespace Ty
def fromInt(n: Int): Except String Ty :=
  match n with
  | 0 => .ok .never
  | 1 => .ok .true
  | 2 => .ok .false
  | 3 => .ok .emptySetType
  | 4 => .ok .bool
  | 5 => .ok .string
  | 6 => .ok .long
  | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum Ty := {
  fromInt := fromInt
}
end Ty

@[inline]
def mergeTy (_: CedarType) (x: Ty): CedarType :=
  match x with
    | .never => panic!("Unexpected never type")
    | .true => .bool .tt
    | .false => .bool .ff
    | .emptySetType => panic!("Expected type of set elements to be specified")
    | .bool => .bool .anyBool
    | .string => .string
    | .long => .int


partial def merge (x1 x2 : CedarType) : CedarType :=
  match x2 with
  | .entity e2 => match x1 with
    | .entity e1 => .entity (Field.merge e1 e2)
    | _ => x2
  | .record m2 => match x1 with
    | .record m1 => match m1.kvs with
      | [] => .record m2
      | _ => .record (Data.Map.make (m2.kvs ++ m1.kvs))
    | _ => x2
  | .set t2 => match x1 with
    | .set t1 => .set (merge t1 t2)
    | _ => x2
  -- For the rest of the fields, replace
  | _ => x2

@[inline]
def mergeType (result: CedarType) (x2: CedarType): CedarType :=
  match result with
    | .set x1 => .set (merge x1 x2)
    | _ => .set x2

@[inline]
def mergeEr (result: CedarType) (x: Proto.EntityRecordKind): CedarType :=
  match x with
  | .entity e2 => match result with
    | .entity e1 => .entity (Field.merge e1 e2)
    | _ => x
  | .record m2 => match result with
    | .record m1 => match m1.kvs with
      | [] => .record m2
      | _ => .record (Data.Map.make (m2.kvs ++ m1.kvs))
    | _ => x
  | _ => panic!("Expected EntityRecordKind to be CedarType.record or CedarType.entity")

-- Is this supposed to be an extension type?
@[inline]
def mergeName (_: CedarType) (_: Cedar.Spec.Name): CedarType :=
  panic!("Not Implemented")

end CedarType

def QualifiedType.merge (x1 x2: QualifiedType) : QualifiedType :=
  match x2 with
    | .required t2 => match x1 with
      | .required t1 => .required (CedarType.merge t1 t2)
      | .optional _ => x2
    | .optional t2 => match x1 with
      | .optional t1 => .optional (CedarType.merge t1 t2)
      | .required _ => x2


mutual
partial def RecordType.parseField (t: Tag) : BParsec (StateM RecordType Unit) := do
  have : Message QualifiedType := { parseField := QualifiedType.parseField, merge := QualifiedType.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType (Array (String × QualifiedType))) t.wireType
      let x: Array (String × QualifiedType) ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (RecordType.mergeAttrs s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def QualifiedType.parseField (t: Tag) : BParsec (StateM QualifiedType Unit) := do
  have : Message CedarType := { parseField := CedarType.parseField, merge := CedarType.merge}
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType CedarType) t.wireType
      let x: CedarType ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (QualifiedType.mergeType s x))
    | 2 =>
      (@Field.guardWireType Bool) t.wireType
      let x: Bool ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (QualifiedType.mergeIsRequired s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.EntityRecordKind.parseField (t: Tag) : BParsec (StateM Proto.EntityRecordKind Unit) := do
  have : Message Proto.EntityRecordKind.Record := { parseField := Proto.EntityRecordKind.Record.parseField, merge := Proto.EntityRecordKind.Record.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Proto.EntityRecordKind.Ty) t.wireType
      let x: Proto.EntityRecordKind.Ty ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.EntityRecordKind.mergeTy s x))
    | 2 =>
      (@Field.guardWireType Proto.EntityRecordKind.Record) t.wireType
      let x: Proto.EntityRecordKind.Record ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.EntityRecordKind.mergeRecord s x))
    | 3 =>
      (@Field.guardWireType Proto.EntityRecordKind.Entity) t.wireType
      let x : Proto.EntityRecordKind.Entity ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.EntityRecordKind.mergeEntity s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.EntityRecordKind.Record.parseField (t: Tag) : BParsec (StateM Proto.EntityRecordKind.Record Unit) := do
  have : Message RecordType := { parseField := RecordType.parseField, merge := RecordType.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType RecordType) t.wireType
      let x: RecordType ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.EntityRecordKind.Record.mergeAttributes s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def CedarType.parseField (t: Tag) : BParsec (StateM CedarType Unit) := do
  have : Message CedarType := {parseField := CedarType.parseField, merge := CedarType.merge }
  have : Message Proto.EntityRecordKind := {parseField := Proto.EntityRecordKind.parseField, merge := Proto.EntityRecordKind.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType CedarType.Ty) t.wireType
      let x: CedarType.Ty ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (CedarType.mergeTy s x))
    | 2 =>
      (@Field.guardWireType CedarType) t.wireType
      let x: CedarType ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (CedarType.mergeType s x))
    | 3 =>
      (@Field.guardWireType Proto.EntityRecordKind) t.wireType
      let x: Proto.EntityRecordKind ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (CedarType.mergeEr s x))
    | 4 =>
      (@Field.guardWireType Cedar.Spec.Name) t.wireType
      let x: Cedar.Spec.Name ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (CedarType.mergeName s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)
end

namespace RecordType
instance : Message RecordType := {
  parseField := parseField
  merge := merge
}
end RecordType

namespace QualifiedType
instance : Message QualifiedType := {
  parseField := parseField, merge := merge
}
end QualifiedType

namespace Proto.EntityRecordKind
instance : Message Proto.EntityRecordKind := {
  parseField := parseField, merge := merge
}
end Proto.EntityRecordKind

namespace Proto.EntityRecordKind.Record
instance : Message Proto.EntityRecordKind.Record := {
  parseField := parseField
  merge := merge
}
end Proto.EntityRecordKind.Record

namespace CedarType
instance : Message CedarType := {
  parseField := parseField
  merge := merge
}
end CedarType

end Cedar.Validation
