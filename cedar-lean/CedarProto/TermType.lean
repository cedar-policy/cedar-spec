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
import Cedar.SymCC
import Cedar.Validation
import Protobuf.Enum
import Protobuf.Message
import Protobuf.Packed
import Protobuf.String

-- Message Dependencies
import CedarProto.Name

open Proto

namespace Cedar.SymCC.Proto

inductive ExtType where
  | ipAddr
  | decimal
  | datetime
  | duration
deriving Repr, Inhabited

namespace ExtType
  @[inline]
  def fromInt(n : Int) : Except String ExtType :=
    match n with
    | 0 => .ok .ipAddr
    | 1 => .ok .decimal
    | 2 => .ok .datetime
    | 3 => .ok .duration
    | _ => .error s!"Field {n} does not exist in enum"

  @[inline]
  def merge (xty1: ExtType) (xty2 : ExtType) : ExtType :=
    match xty1, xty2 with
    | .ipAddr, .ipAddr => .ipAddr
    | .decimal, .decimal => .decimal
    | .datetime, .datetime => .datetime
    | .duration, .duration => .duration
    | _, _ => xty2

  instance : ProtoEnum ExtType := {
    fromInt := fromInt
  }

  def toCedarExtType (ext: ExtType) : Cedar.Validation.ExtType :=
    match ext with
    | .ipAddr => .ipAddr
    | .decimal => .decimal
    | .datetime => .datetime
    | .duration => .duration
end ExtType

inductive PrimType where
  | bool
  | string
deriving Repr, Inhabited

namespace PrimType
  @[inline]
  def fromInt(n : Int) : Except String PrimType :=
    match n with
    | 0 => .ok .bool
    | 1 => .ok .string
    | _ => .error s!"Field {n} does not exist in enum"

  @[inline]
  def merge (p1: PrimType) (p2: PrimType) : PrimType :=
    match p1, p2 with
    | .bool, .bool => .bool
    | .string, .string => .string
    | _, _ => p2

  instance : ProtoEnum PrimType := {
    fromInt := fromInt
  }
end PrimType

inductive TermPrimType where
  | prim : PrimType -> TermPrimType
  | bitvec : Nat -> TermPrimType
  | entity : Spec.Proto.Name -> TermPrimType
  | ext : ExtType -> TermPrimType
deriving Repr, Inhabited

namespace TermPrimType
  @[inline]
  def merge (p1: TermPrimType) (p2: TermPrimType) : TermPrimType :=
    match p1, p2 with
    | .prim p1, .prim p2 => .prim (p1.merge p2)
    | .bitvec _, .bitvec n => .bitvec n
    | .entity ety1, .entity ety2 => .entity (Field.merge ety1 ety2)
    | .ext xty1, .ext xty2 => .ext (xty1.merge xty2)
    | _, _ => p2

  def parseField (t : Tag) : BParsec (MergeFn TermPrimType) := do
    match t.fieldNum with
    | 1 =>
      let x : PrimType ← Field.guardedParse t
      pureMergeFn (merge · (.prim x))
    | 2 =>
      let x : UInt32 ← Field.guardedParse t
      pureMergeFn (merge · (.bitvec x.toNat))
    | 3 =>
      let x : Spec.Proto.Name ← Field.guardedParse t
      pureMergeFn (merge · (.entity x))
    | 4 =>
      let x : ExtType ← Field.guardedParse t
      pureMergeFn (merge · (.ext x))
    | _ =>
      t.wireType.skip
      pure ignore

  instance : Message TermPrimType := {
    parseField := parseField
    merge := merge
  }

  def toCedarTermPrimType (pty : TermPrimType) : Cedar.SymCC.TermPrimType :=
    match pty with
    | .prim .bool => .bool
    | .prim .string => .string
    | .bitvec n => .bitvec n
    | .entity ety => .entity ety.toName
    | .ext xty => .ext xty.toCedarExtType
end TermPrimType

mutual
  inductive TermType where
    | prim : TermPrimType -> TermType
    | option : TermType -> TermType
    | set : TermType -> TermType
    | record : RecordType -> TermType
  deriving Repr, Inhabited

  structure RecordFieldType where
    attr : String
    ty : TermType
  deriving Repr, Inhabited

  structure RecordType where
    fields : List RecordFieldType
  deriving Repr, Inhabited
end

mutual
  def RecordFieldType.merge (rf1: RecordFieldType) (rf2: RecordFieldType) : RecordFieldType :=
    RecordFieldType.mk (Field.merge rf1.attr rf2.attr) (TermType.merge rf1.ty rf2.ty)

  def RecordType.merge (rty1: RecordType) (rty2: RecordType) : RecordType :=
    RecordType.mk (rty1.fields ++ rty2.fields)

  def TermType.merge (ty1: TermType) (ty2: TermType) : TermType :=
    match ty1, ty2 with
    | .prim p1, .prim p2 => .prim (Field.merge p1 p2)
    | .option ty1, .option ty2 => .option (TermType.merge ty1 ty2)
    | .set ty1, .set ty2 => .option (TermType.merge ty1 ty2)
    | .record rty1, .record rty2 => .record (RecordType.merge rty1 rty2)
    | _, _ => ty2
end

mutual
  partial def RecordFieldType.parseField (t : Tag) : BParsec (MergeFn RecordFieldType) := do
    have : Message TermType := { parseField := TermType.parseField, merge := TermType.merge }
    match t.fieldNum with
    | 1 => parseFieldElement t RecordFieldType.attr (update attr)
    | 2 => parseFieldElement t RecordFieldType.ty (update ty)
    | _ => let _ ← t.wireType.skip ; pure ignore

  partial def RecordType.parseField (t : Tag) : BParsec (MergeFn RecordType) := do
    have : Message RecordFieldType := { parseField := RecordFieldType.parseField, merge := RecordFieldType.merge }
    match t.fieldNum with
    | 1 =>
      let x : Proto.Packed RecordFieldType ← Field.guardedParse t
      pureMergeFn (RecordType.merge · (RecordType.mk x.toList))
    | _ => let _ ← t.wireType.skip ; pure ignore

  partial def TermType.parseField (t : Tag) : BParsec (MergeFn TermType) := do
    have : Message TermType := { parseField := TermType.parseField, merge := TermType.merge }
    have : Message RecordType := { parseField := RecordType.parseField, merge := RecordType.merge }
    match t.fieldNum with
    | 1 =>
      let x : TermPrimType ← Field.guardedParse t
      pureMergeFn (TermType.merge · (.prim x))
    | 2 =>
      let x : TermType ← Field.guardedParse t
      pureMergeFn (TermType.merge · (.option x))
    | 3 =>
      let x : TermType ← Field.guardedParse t
      pureMergeFn (TermType.merge · (.set x))
    | 4 =>
      let x : RecordType ← Field.guardedParse t
      pureMergeFn (TermType.merge · (.record x))
    | _ => let _ ← t.wireType.skip ; pure ignore
end

namespace RecordFieldType
  instance : Message RecordFieldType := {
    parseField := parseField
    merge := merge
  }
end RecordFieldType

namespace RecordType
  instance : Message RecordType := {
    parseField := parseField
    merge := merge
  }
end RecordType

namespace TermType
  instance : Message TermType := {
    parseField := parseField
    merge := merge
  }
end TermType

mutual
  partial def RecordType.toCedarMap (rty : RecordType) : Cedar.Data.Map Cedar.Spec.Attr Cedar.SymCC.TermType :=
    Cedar.Data.Map.mk (rty.fields.map (λ rf => (rf.attr, TermType.toCedarTermType rf.ty)))

  partial def TermType.toCedarTermType (ty: TermType) : Cedar.SymCC.TermType :=
    match ty with
    | .prim pty => .prim pty.toCedarTermPrimType
    | .option ty => .option ty.toCedarTermType
    | .set ty => .set ty.toCedarTermType
    | .record rty => .record rty.toCedarMap
end

end Cedar.SymCC.Proto
