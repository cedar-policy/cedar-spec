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
import Cedar.Validation
import Protobuf.Enum
import Protobuf.Message
import Protobuf.Map
import Protobuf.String

-- Message Dependencies
import CedarProto.Name

open Proto

namespace Cedar.Validation.Proto

mutual
inductive PrimType where
  | string
  | bool
  | long
deriving Repr, Inhabited

structure RecordType where
  attrs : List (String × (Qualified ProtoType))
deriving Repr, Inhabited

inductive ProtoType where
  | prim (p : PrimType)
  | set (elTy : ProtoType)
  | entity (ety : Spec.Proto.Name)
  | record (rty : RecordType)
  | ext (extTy : Spec.Proto.Name)
deriving Repr, Inhabited
end

namespace PrimType
@[inline]
def fromInt(n : Int) : Except String PrimType :=
  match n with
  | 0 => .ok .string
  | 1 => .ok .bool
  | 2 => .ok .long
  | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum PrimType := {
  fromInt := fromInt
}
end PrimType

namespace Qualified

@[inline]
def mergeType (result : Qualified α) (x : α) : Qualified α :=
  -- Replace the type information, keep the qualified constructor
  match result with
    | .required _ => .required x
    | .optional _ => .optional x

@[inline]
def mergeIsRequired (result : Qualified α) (required : Bool) : Qualified α :=
  -- Replace constructor, keep data
  if required then
    .required result.getType
  else
    .optional result.getType

@[inline]
def merge [Field α] (x1 x2 : Qualified α) : Qualified α :=
  match x1, x2 with
  | .required t1, .required t2 => .required (Field.merge t1 t2)
  | .optional t1, .optional t2 => .optional (Field.merge t1 t2)
  | _, _ => x2

-- parseField requires mutual recursion and can be found at the end of this
-- file.
end Qualified

namespace RecordType

@[inline]
def mergeAttrs (result : RecordType) (x : List (String × (Qualified ProtoType))) : RecordType :=
  { attrs := result.attrs ++ x }

@[inline]
def merge (x1 x2 : RecordType) : RecordType :=
  match x1.attrs with
    | [] => { attrs := x2.attrs }
    | _ => { attrs := x1.attrs ++ x2.attrs }

-- parseField requires mutual recursion and can be found at the end of the file
end RecordType

namespace ProtoType

@[inline]
def mergePrim (result : ProtoType) (x : PrimType) : ProtoType :=
  match result with
  | .prim p => .prim (Field.merge p x)
  | _ => .prim x

@[inline]
def mergeEntity (result : ProtoType) (x : Spec.Proto.Name) : ProtoType :=
  match result with
  | .entity n => .entity (Field.merge n x)
  | _ => .entity x

@[inline]
def mergeExt (result : ProtoType) (x : Spec.Proto.Name) : ProtoType :=
  match result with
  | .ext n => .ext (Field.merge n x)
  | _ => .ext x

mutual
@[inline]
partial def mergeSet (result : ProtoType) (x : ProtoType) : ProtoType :=
  match result with
  | .set elty => .set (ProtoType.merge elty x)
  | _ => .set x

@[inline]
partial def mergeRecord (result : ProtoType) (x : RecordType) : ProtoType :=
  match result with
  | .record m => .record (RecordType.merge m x)
  | _ => .record x

@[inline]
partial def merge (x1 x2 : ProtoType) : ProtoType :=
  match x1, x2 with
  | .prim p1, .prim p2 => .prim (Field.merge p1 p2)
  | .set el1, .set el2 => .set (merge el1 el2)
  | .entity e1, .entity e2 => .entity (Field.merge e1 e2)
  | .record m1, .record m2 => .record (RecordType.merge m1 m2)
  | .ext x1, .ext x2 => .ext (Field.merge x1 x2)
  -- For the rest of the fields, replace
  | _, _ => x2
end

partial def toCedarType : ProtoType → Except String CedarType
  | .prim .bool => .ok (.bool .anyBool)
  | .prim .long => .ok .int
  | .prim .string => .ok .string
  | .set t => do .ok (.set (← t.toCedarType))
  | .entity e => .ok (.entity e.toName)
  | .record r => do
    let attrs ← r.attrs.mapM λ (k,v) => do .ok (k, ← v.map toCedarType |>.transpose)
    .ok (.record $ Data.Map.make attrs)
  | .ext n => match n.id with -- ignoring n.path because currently no extension types have nonempty namespaces
    | "ipaddr" => .ok (.ext .ipAddr)
    | "decimal" => .ok (.ext .decimal)
    | _ => .error s!"unknown extension type name: {n.toName}"

end ProtoType

mutual

partial def QualifiedProtoType.parseField (t : Tag) : BParsec (MergeFn (Qualified ProtoType)) := do
  have : Message ProtoType := { parseField := ProtoType.parseField, merge := ProtoType.merge}
  match t.fieldNum with
    | 1 =>
      let x : ProtoType ← Field.guardedParse t
      pure (pure $ Qualified.mergeType · x)
    | 2 =>
      let x : Bool ← Field.guardedParse t
      pure (pure $ Qualified.mergeIsRequired · x)
    | _ =>
      t.wireType.skip
      pure ignore

partial def RecordType.parseField (t : Tag) : BParsec (MergeFn RecordType) := do
  have : Message ProtoType := { parseField := ProtoType.parseField, merge := ProtoType.merge }
  have : Message (Qualified ProtoType) := { parseField := QualifiedProtoType.parseField, merge := Qualified.merge }
  match t.fieldNum with
    | 1 =>
      let x : Proto.Map String (Qualified ProtoType) ← Field.guardedParse t
      pure (pure $ RecordType.mergeAttrs · x.toList)
    | _ =>
      t.wireType.skip
      pure ignore

partial def ProtoType.parseField (t : Tag) : BParsec (MergeFn ProtoType) := do
  have : Message ProtoType := { parseField := ProtoType.parseField, merge := ProtoType.merge }
  have : Message RecordType := { parseField := RecordType.parseField, merge := RecordType.merge }
  match t.fieldNum with
    | 1 =>
      let x : PrimType ← Field.guardedParse t
      pure (pure $ ProtoType.mergePrim · x)
    | 2 =>
      let x : ProtoType ← Field.guardedParse t
      pure (pure $ ProtoType.mergeSet · x)
    | 3 =>
      let x : Spec.Proto.Name ← Field.guardedParse t
      pure (pure $ ProtoType.mergeEntity · x)
    | 4 =>
      let x : RecordType ← Field.guardedParse t
      pure (pure $ ProtoType.mergeRecord · x)
    | 5 =>
      let x : Spec.Proto.Name ← Field.guardedParse t
      pure (pure $ ProtoType.mergeExt · x)
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

namespace ProtoType
instance : Message ProtoType := {
  parseField := parseField
  merge := merge
}
end ProtoType

instance : Message (Qualified ProtoType) := {
  parseField := QualifiedProtoType.parseField
  merge := Qualified.merge
}

end Cedar.Validation.Proto
