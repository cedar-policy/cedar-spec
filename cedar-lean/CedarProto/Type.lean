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
def mergeAttrs (result : RecordType) (x : Array (String × QualifiedType)) : RecordType :=
  Cedar.Data.Map.mk (result.kvs ++ x.toList)

def merge (x1 x2 : RecordType) : RecordType :=
  Cedar.Data.Map.mk (x1.kvs ++ x2.kvs)

end RecordType

namespace QualifiedType

@[inline]
def mergeType (result : QualifiedType) (x : CedarType) : QualifiedType :=
  -- Replace the type information, keep the qualified constructor
  match result with
    | .required _ => .required x
    | .optional _ => .optional x

@[inline]
def mergeIsRequired (result : QualifiedType) (required : Bool) : QualifiedType :=
  -- Replace constructor, keep data
  if required then
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
@[inline]
def fromInt (n : Int) : Except String Ty :=
  match n with
    | 0 => .ok .AnyEntity
    | n => .error s!"Field {n} does not exist in enum"
instance : ProtoEnum Ty where
  fromInt := fromInt
end Ty

namespace Record
@[inline]
def mergeAttributes (result : Record) (m2 : RecordType) : Record :=
  have m2 : Cedar.Data.Map Cedar.Spec.Attr (Qualified CedarType) := m2
  match result with
    | .record m1 => .record (Cedar.Data.Map.make (m2.kvs ++ m1.kvs))
    | _ => panic!("EntityRecordKind.Record is not set to the CedarType.record constructor")

@[inline]
def merge (x1 x2 : Record) : Record :=
  match x1, x2 with
    | .record m1, .record m2 => match m1.kvs with
      | [] => .record m2
      | _ => .record (Cedar.Data.Map.make (m2.kvs ++ m1.kvs))
    | _, _ => panic!("EntityRecordKind.Record is not set to the CedarType.record constructor")

-- parseField requires mutual recursion and can be found at the end of the file
end Record

namespace Entity
@[inline]
def mergeE (result : Entity) (e2 : Spec.EntityTypeProto) : Entity :=
  match result with
    | .entity e1 => .entity (Field.merge e1 e2)
    | _ => panic!("Entity expected CedarType constructor to be .entity")

@[inline]
def merge (x1 x2 : Entity) : Entity :=
  match x1, x2 with
    | .entity e1, .entity e2 => .entity (Field.merge e1 e2)
    | _, _ => panic!("Entity expected CedarType constructor to be .entity")

@[inline]
def parseField (t : Tag) : BParsec (MergeFn Entity) := do
  match t.fieldNum with
    | 1 =>
      let x : Spec.EntityTypeProto ← Field.guardedParse t
      pure (mergeE · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message Entity := {
  parseField := parseField
  merge := merge
}
end Entity

namespace ActionEntity
-- Note: Ignore the Attributes in the ActionEntity message
-- since this isn't represented in the formal model

@[inline]
def mergeName (result : ActionEntity) (e2 : Spec.EntityTypeProto) : ActionEntity :=
  match result with
    | .entity e1 => .entity (Field.merge e1 e2)
    | _ => panic!("ActionEntity expected CedarType constructor to be .entity")

@[inline]
def merge (x1 x2 : ActionEntity) : ActionEntity :=
  match x1, x2 with
    | .entity e1, .entity e2 => .entity (Field.merge e1 e2)
    | _, _ => panic!("ActionEntity expected CedarType constructor to be .entity")

@[inline]
def parseField (t : Tag) : BParsec (MergeFn ActionEntity) := do
  match t.fieldNum with
    | 1 =>
      let x : Spec.EntityTypeProto ← Field.guardedParse t
      pure (mergeName · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message ActionEntity := {
  parseField := parseField
  merge := merge
}
end ActionEntity

@[inline]
def mergeTy (_ : EntityRecordKind) (x : Ty) : EntityRecordKind :=
  match x with
   | .AnyEntity => panic!("Not Implemented")

@[inline]
def mergeRecord (result : EntityRecordKind) (x : Record) : EntityRecordKind :=
  have m2 := match x with
    | .record m => m
    | _ => panic!("EntityRecordKind.Record is not set to the CedarType.record constructor")
  match result with
    | .record m1 => match m1.kvs with
      | [] => .record m2
      | _ => .record (Cedar.Data.Map.make (m2.kvs ++ m1.kvs))
    | _ => .record m2

@[inline]
def mergeEntity (result : EntityRecordKind) (x : Entity) : EntityRecordKind :=
  have e2 := match x with
    | .entity e => e
    | _ => panic!("EntityRecordKind.Entity is not set to the CedarType.entity constructor")
  match result with
    | .entity e1 => .entity (Field.merge e1 e2)
    | _ => .entity e2

@[inline]
def mergeActionEntity (result : EntityRecordKind) (x : ActionEntity) : EntityRecordKind :=
  have e2 := match x with
    | .entity e => e
    | _ => panic!("EntityRecordKind.ActionEntity is not set to the CedarType.entity constructor")
  match result with
    | .entity e1 => .entity (Field.merge e1 e2)
    | _ => .entity e2

@[inline]
def merge (x1 x2 : EntityRecordKind) : EntityRecordKind :=
  match x1, x2 with
  | .entity e1, .entity e2 => .entity (Field.merge e1 e2)
  | .record m1, .record m2 => .record (Cedar.Data.Map.make (m2.kvs ++ m1.kvs))
  | .entity _, .record _ => x2
  | .record _, .entity _ => x2
  | _, _ => panic!("Expected EntityRecordKind to be CedarType.record or CedarType.entity")

-- NOTE: parseField requires mutual recursion and can be found at the end of the file
end Proto.EntityRecordKind

namespace CedarType

-- Note that Cedar.Validation.CedarType is defined as
-- inductive CedarType where
--   | bool (bty : BoolType)
--   | int
--   | string
--   | entity (ety : EntityType)
--   | set (ty : CedarType)
--   | record (rty : Map Attr (Qualified CedarType))
--   | ext (xty : ExtType)

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
@[inline]
def fromInt(n : Int) : Except String Ty :=
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
def mergeTy (_ : CedarType) (x : Ty) : CedarType :=
  match x with
    | .never => panic!("Unexpected never type")
    | .true => .bool .tt
    | .false => .bool .ff
    | .emptySetType => panic!("Expected type of set elements to be specified")
    | .bool => .bool .anyBool
    | .string => .string
    | .long => .int


partial def merge (x1 x2 : CedarType) : CedarType :=
  match x1, x2 with
  | .entity e1, .entity e2 => .entity (Field.merge e1 e2)
  | .record m1, .record m2 => match m1.kvs with
    | [] => .record m2
    | _ => .record (Data.Map.make (m2.kvs ++ m1.kvs))
  | .set t1, .set t2 => .set (merge t1 t2)
  -- For the rest of the fields, replace
  | _, _ => x2

@[inline]
def mergeType (result : CedarType) (x2 : CedarType) : CedarType :=
  match result with
    | .set x1 => .set (merge x1 x2)
    | _ => .set x2

@[inline]
def mergeEr (result : CedarType) (x : Proto.EntityRecordKind) : CedarType :=
  match result, x with
  | .entity e1, .entity e2 => .entity (Field.merge e1 e2)
  | .record m1, .record m2 => match m1.kvs with
    | [] => .record m2
    | _ => .record (Data.Map.make (m2.kvs ++ m1.kvs))
  | _, .record _ => x
  | _, .entity _ => x
  | _, _ => panic!("Expected EntityRecordKind to be CedarType.record or CedarType.entity")

@[inline]
def mergeName (_ : CedarType) (xty : Cedar.Spec.Name) : CedarType :=
  match xty.id with
  | "ipaddr" => .ext .ipAddr
  | "decimal" => .ext .decimal
  | xty => panic! s!"mergeName: unknown extension type {xty}"


end CedarType

@[inline]
def QualifiedType.merge (x1 x2 : QualifiedType) : QualifiedType :=
  match x1, x2 with
  | .required t1, .required t2 => .required (CedarType.merge t1 t2)
  | .optional t1, .optional t2 => .optional (CedarType.merge t1 t2)
  | .optional _, .required _ => x2
  | .required _, .optional _ => x2


mutual
partial def RecordType.parseField (t : Tag) : BParsec (RecordType → RecordType) := do
  have : Message QualifiedType := { parseField := QualifiedType.parseField, merge := QualifiedType.merge }
  match t.fieldNum with
    | 1 =>
      let x : Proto.Map String QualifiedType ← Field.guardedParse t
      pure (RecordType.mergeAttrs · x)
    | _ =>
      t.wireType.skip
      pure ignore

partial def QualifiedType.parseField (t : Tag) : BParsec (QualifiedType → QualifiedType) := do
  have : Message CedarType := { parseField := CedarType.parseField, merge := CedarType.merge}
  match t.fieldNum with
    | 1 =>
      let x : CedarType ← Field.guardedParse t
      pure (QualifiedType.mergeType · x)
    | 2 =>
      let x : Bool ← Field.guardedParse t
      pure (QualifiedType.mergeIsRequired · x)
    | _ =>
      t.wireType.skip
      pure ignore

partial def Proto.EntityRecordKind.parseField (t : Tag) : BParsec (Proto.EntityRecordKind → Proto.EntityRecordKind) := do
  have : Message Proto.EntityRecordKind.Record := { parseField := Proto.EntityRecordKind.Record.parseField, merge := Proto.EntityRecordKind.Record.merge }
  match t.fieldNum with
    | 1 =>
      let x : Proto.EntityRecordKind.Ty ← Field.guardedParse t
      pure (Proto.EntityRecordKind.mergeTy · x)
    | 2 =>
      let x : Proto.EntityRecordKind.Record ← Field.guardedParse t
      pure (Proto.EntityRecordKind.mergeRecord · x)
    | 3 =>
      let x : Proto.EntityRecordKind.Entity ← Field.guardedParse t
      pure (Proto.EntityRecordKind.mergeEntity · x)
    | _ =>
      t.wireType.skip
      pure ignore

partial def Proto.EntityRecordKind.Record.parseField (t : Tag) : BParsec (Proto.EntityRecordKind.Record → Proto.EntityRecordKind.Record) := do
  have : Message RecordType := { parseField := RecordType.parseField, merge := RecordType.merge }
  match t.fieldNum with
    | 1 =>
      let x : RecordType ← Field.guardedParse t
      pure (Proto.EntityRecordKind.Record.mergeAttributes · x)
    | _ =>
      t.wireType.skip
      pure ignore

partial def CedarType.parseField (t : Tag) : BParsec (CedarType → CedarType) := do
  have : Message CedarType := {parseField := CedarType.parseField, merge := CedarType.merge }
  have : Message Proto.EntityRecordKind := {parseField := Proto.EntityRecordKind.parseField, merge := Proto.EntityRecordKind.merge }
  match t.fieldNum with
    | 1 =>
      let x : CedarType.Ty ← Field.guardedParse t
      pure (CedarType.mergeTy · x)
    | 2 =>
      let x : CedarType ← Field.guardedParse t
      pure (CedarType.mergeType · x)
    | 3 =>
      let x : Proto.EntityRecordKind ← Field.guardedParse t
      pure (CedarType.mergeEr · x)
    | 4 =>
      let x : Cedar.Spec.Name ← Field.guardedParse t
      pure (CedarType.mergeName · x)
    | _ =>
      t.wireType.skip
      pure ignore
end

namespace RecordType
instance : Message RecordType := {
  parseField := parseField
  merge := merge
}
end RecordType

namespace QualifiedType
instance : Message QualifiedType := {
  parseField := parseField
  merge := merge
}
end QualifiedType

namespace Proto.EntityRecordKind
instance : Message Proto.EntityRecordKind := {
  parseField := parseField
  merge := merge
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
