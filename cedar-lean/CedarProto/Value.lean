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

-- Already defined in Cedar.Spec.Name
-- inductive Prim where
--   | bool (b : Bool)
--   | int (i : Int64)
--   | string (s : String)
--   | entityUID (uid : EntityUID)
-- Note: This is the same as Literal in the proto file

namespace Cedar.Spec.Prim

@[inline]
def merge_bool (p: Prim) (b2: Bool) : Prim :=
  match p with
    | .bool b1 => Prim.bool (Field.merge b1 b2)
    | _ => Prim.bool b2

@[inline]
def merge_int (_: Prim) (pi: Proto.Int64) : Prim :=
  have i : Int := pi
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

@[inline]
def merge_string (p: Prim) (s2: String) : Prim :=
  match p with
    | .string s1 => Prim.string (Field.merge s1 s2)
    | _ => Prim.string s2

@[inline]
def merge_euid (p: Prim) (euid2: EntityUID): Prim :=
  match p with
    | .entityUID euid1 => Prim.entityUID (Field.merge euid1 euid2)
    | _ => Prim.entityUID euid2

@[inline]
def merge (p1: Prim) (p2: Prim) : Prim :=
  match p2 with
    | .bool b2 => merge_bool p1 b2
    | .int i2 =>
      let i2_1 : Int := i2
      let i2_2 : Proto.Int64 := i2_1
      merge_int p1 i2_2
    | .string s2 => merge_string p1 s2
    | .entityUID e2 => merge_euid p1 e2

def parseField (t: Tag) : BParsec (StateM Prim Unit) := do
  match t.fieldNum with
    -- Skipping parsing 1 for now since I may make this a oneof
    | 2 =>
      (@Field.guardWireType Bool) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec Bool))
      pure (modifyGet fun s => Prod.mk () (s.merge_bool x))
    | 3 =>
      (@Field.guardWireType Int64) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec Int64))
      pure (modifyGet fun s => Prod.mk () (s.merge_int x))
    | 4 =>
      (@Field.guardWireType String) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec String))
      pure (modifyGet fun s => Prod.mk () (s.merge_string x))
    | 5 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec EntityUID))
      pure (modifyGet fun s => Prod.mk () (s.merge_euid x))
    | _ =>
      t.wireType.skip
      pure (pure ())

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

-- Actual Value data in Protobuf is stored in ValueKind message
namespace Cedar.Spec
def ValueKind := Value
deriving instance Inhabited for ValueKind
end Cedar.Spec
namespace Cedar.Spec.ValueKind

@[inline]
def mergePrim (v: ValueKind) (p2: Prim) : ValueKind :=
  match v with
    | .prim p1 => .prim (Field.merge p1 p2)
    | _ => .prim p2

-- Concatenates both sets
@[inline]
def mergeSet (v1: ValueKind) (v2: Array ValueKind) : ValueKind :=
  match v1 with
  | .set s =>
    let s1: List ValueKind := s.elts
    let s2: List ValueKind := v2.toList
    .set (Data.Set.mk (s1 ++ s2))
  | _ => .set (Data.Set.mk v2.toList)

-- Concatenate both maps
@[inline]
def mergeRecord (v: ValueKind) (m: (Array (String × ValueKind))) : ValueKind :=
  match v with
  | .record m2 =>
    let mm1: List (String × ValueKind) := m2.kvs
    let mm2: List (String × ValueKind) := m.toList
    .record (Data.Map.mk (mm1 ++ mm2))
  | _ =>
    .record (Data.Map.mk m.toList)

@[inline]
def merge (v1: ValueKind) (v2: ValueKind) : ValueKind :=
  match v2 with
    | .prim p2 => mergePrim v1 p2
    | .set s2 => mergeSet v1 s2.elts.toArray
    | .record m2 => mergeRecord v1 m2.kvs.toArray
    | .ext _ => panic!("Not implemented")

end Cedar.Spec.ValueKind

-- There's one additinoal message wrapped around ValueKind
-- that we need to parse
namespace Cedar.Spec.Value

@[inline]
def mergeValueKind (x1: Value) (x2: ValueKind) : Value :=
  ValueKind.merge x1 x2

@[inline]
def merge (x1: Value) (x2: Value) : Value :=
  ValueKind.merge x1 x2

end Cedar.Spec.Value

-- The Value message depends on ValueKind
-- and the recursive components of ValueKind
-- depends on Value
mutual
partial def parseFieldValueKind (t: Tag) : BParsec (StateM ValueKind Unit) := do
  have : Message ValueKind := {parseField := parseFieldValueKind, merge := ValueKind.merge}
  have : Message Value := { parseField := parseFieldValue, merge := Value.merge}

  match t.fieldNum with
    | 2 =>
      (@Field.guardWireType Prim) t.wireType
      let x: Prim ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergePrim x))
    | 17 =>
      (@Field.guardWireType ValueKind) t.wireType
      let x: Repeated ValueKind ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeSet x))
    | 22 =>
      (@Field.guardWireType (Array (String × ValueKind))) t.wireType
      let x: Array (String × ValueKind) ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeRecord x))
    | _ =>
      t.wireType.skip
      pure (pure ())


partial def parseFieldValue (t: Tag) : BParsec (StateM Value Unit) := do
  have : Message ValueKind := {parseField := parseFieldValueKind, merge := ValueKind.merge}
  have : Message Value := { parseField := parseFieldValue, merge := Value.merge}
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType ValueKind) t.wireType
      let x: ValueKind ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (Value.mergeValueKind s x))
    | _ =>
      t.wireType.skip
      pure (pure ())

end

instance : Message ValueKind := {
  parseField := parseFieldValueKind
  merge := ValueKind.merge
}

instance : Message Value := {
  parseField := parseFieldValue
  merge := Value.merge
}

namespace Cedar.Spec
partial def Value.makeWf (v: Value) : Value :=
  match v with
    | .set s => Cedar.Data.Set.make (s.elts.map makeWf)
    | .record m => Cedar.Data.Map.make (m.kvs.map (fun ⟨attr, vi⟩ => ⟨ attr, vi.makeWf ⟩))
    | _ => v
end Cedar.Spec
