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
import Protobuf.BParsec
import Protobuf.Message
import Protobuf.String
import Protobuf.Enum
import Protobuf.Map

import Cedar

import CedarProto.EntityUID

open Cedar.Spec
open Proto

-- NOTE: We don't handle extensions in this version

inductive LiteralType where
 | TBool
 | TLong
 | TString
 | TEntityUID
 deriving Repr, Inhabited, DecidableEq

namespace LiteralType
def get? (n: Int) : Except String LiteralType :=
  match n with
    | 0 => .ok LiteralType.TBool
    | 1 => .ok LiteralType.TLong
    | 2 => .ok LiteralType.TString
    | 3 => .ok LiteralType.TEntityUID
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum LiteralType where
  fromInt := get?

end LiteralType


-- Already defined in Cedar.Spec.Name
-- inductive Prim where
--   | bool (b : Bool)
--   | int (i : Int64)
--   | string (s : String)
--   | entityUID (uid : EntityUID)
-- Note: This is the same as Literal in the proto file

namespace Cedar.Spec.Prim

def merge_bool (p: Prim) (b2: Bool) : Prim :=
  match p with
    | .bool b1 => Prim.bool (Field.merge b1 b2)
    | _ => Prim.bool b2

def merge_int (_: Prim) (i: Proto.Int64) : Prim :=
  if H1: i < Cedar.Data.INT64_MIN then
    panic!("Integer less than INT64_MIN")
  else if H2: i > Cedar.Data.INT64_MAX then
    panic!("Integer greater than INT64_MAX")
  else
    have h1 : Cedar.Data.INT64_MIN ≤ i ∧ i ≤ Cedar.Data.INT64_MAX := by
      unfold Proto.Int64 at *
      omega

    -- Override semantics
    Prim.int (Cedar.Data.Int64.mk i h1)

def merge_string (p: Prim) (s2: String) : Prim :=
  match p with
    | .string s1 => Prim.string (Field.merge s1 s2)
    | _ => Prim.string s2

def merge_euid (p: Prim) (euid2: EntityUID): Prim :=
  match p with
    | .entityUID euid1 => Prim.entityUID (Field.merge euid1 euid2)
    | _ => Prim.entityUID euid2

def merge (p1: Prim) (p2: Prim) : Prim :=
  match p2 with
    | .bool b2 => merge_bool p1 b2
    | .int i2 => merge_int p1 i2
    | .string s2 => merge_string p1 s2
    | .entityUID e2 => merge_euid p1 e2

def parseField (t: Tag) : BParsec (MessageM Prim) := do
  match t.fieldNum with
    -- Skipping parsing 1 for now since I may make this a oneof
    | 2 =>
      (@Field.guardWireType Bool) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec Bool))
      pure (MessageM.modifyGet fun s => s.merge_bool x)
    | 3 =>
      (@Field.guardWireType Int64) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec Int64))
      pure (MessageM.modifyGet fun s => s.merge_int x)
    | 4 =>
      (@Field.guardWireType String) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec String))
      pure (MessageM.modifyGet fun s => s.merge_string x)
    | 5 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec EntityUID))
      pure (MessageM.modifyGet fun s => s.merge_euid x)
    | _ =>
      t.wireType.skip
      pure MessageM.pure

instance : Message Prim := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.Prim

-- Already defined in Cedar.Spec.Name
-- abbrev Attr := String
-- inductive Value where
--   | prim (p : Prim)
--   | set (s : Set Value)
--   | record (m : Map Attr Value)
--   | ext (x : Ext)

namespace Cedar.Spec.Value

def mergePrim (v: Value) (p2: Prim) : Value :=
  match v with
    | .prim p1 => Value.prim (Field.merge p1 p2)
    | _ => Value.prim p2

-- Concatenates both sets
def mergeSet (v1: Value) (v2: Array Value) : Value :=
  match v1 with
  | set s => Value.set (Data.Set.make (s.elts ++ v2.toList))
  | _ => Value.set (Data.Set.make v2.toList)

-- Concatenate both maps
def mergeRecord (v: Value) (m: (Array (String × Value))) : Value :=
  match v with
  | record m2 => Value.record (Data.Map.make (m2.kvs ++ m.toList))
  | _ => Value.record (Data.Map.make m.toList)

def merge (v1: Value) (v2: Value) : Value :=
  match v2 with
    | .prim p2 => mergePrim v1 p2
    | .set s2 => mergeSet v1 s2.elts.toArray
    | .record m2 => mergeRecord v1 m2.kvs.toArray
    | .ext _ => panic!("Not implemented")

partial def parseField (t: Tag) : BParsec (MessageM Value) := do
  have : Message Value := { parseField := parseField, merge := merge}
  have : Field Value := by apply inferInstance

  match t.fieldNum with
    | 2 =>
      (@Field.guardWireType Prim) t.wireType
      let x: Prim ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => s.mergePrim x)
    | 17 =>
      (@Field.guardWireType Value) t.wireType
      let x: Repeated Value ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => s.mergeSet x)
    | 22 =>
      (@Field.guardWireType (Array (String × Value))) t.wireType
      let x: Array (String × Value) ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => s.mergeRecord x)
    | _ =>
      t.wireType.skip
      pure MessageM.pure

instance : Message Value := {
  parseField := parseField
  merge := merge
}


end Cedar.Spec.Value
