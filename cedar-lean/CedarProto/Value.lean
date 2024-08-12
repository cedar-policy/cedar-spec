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

namespace Cedar.Spec.Prim

-- Already defined in Cedar.Spec.Name
-- inductive Prim where
--   | bool (b : Bool)
--   | int (i : Int64)
--   | string (s : String)
--   | entityUID (uid : EntityUID)
-- Note: This is the same as Literal in the proto file

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
    -- NOTE: Skipping parsing 1 for now since I may make this a oneof
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

namespace Cedar.Spec
-- Already defined in Cedar.Spec.Name
-- abbrev Attr := String
-- inductive Value where
--   | prim (p : Prim)
--   | set (s : Set Value)
--   | record (m : Map Attr Value)
--   | ext (x : Ext)

mutual
inductive ValueProto where
  | mk (v : ValueKindProto)

inductive ValueKindProto where
  | prim (p : Prim)
  | set (s: Array ValueProto)
  | record (m: Array (Attr × ValueProto))
  | ext (x: Ext)
end

deriving instance Inhabited for ValueKindProto
deriving instance Inhabited for ValueProto
end Cedar.Spec

namespace Cedar.Spec.ValueKindProto

@[inline]
def mergePrim (v: ValueKindProto) (p2: Prim) : ValueKindProto :=
  match v with
    | .prim p1 => .prim (Field.merge p1 p2)
    | _ => .prim p2

-- Concatenates both sets
@[inline]
def mergeSet (v1: ValueKindProto) (s2: Array ValueProto) : ValueKindProto :=
  match v1 with
  | .set s1 => .set (s2 ++ s1)
  | _ => .set s2

-- Concatenate both maps
@[inline]
def mergeRecord (v: ValueKindProto) (m2: (Array (String × ValueProto))) : ValueKindProto :=
  match v with
  | .record m1 => .record (m2 ++ m1)
  | _ => .record m2

@[inline]
def merge (v1: ValueKindProto) (v2: ValueKindProto) : ValueKindProto :=
  match v2 with
    | .prim p2 => mergePrim v1 p2
    | .set s2 => mergeSet v1 s2
    | .record m2 => mergeRecord v1 m2
    | .ext _ => panic!("Not implemented")

end Cedar.Spec.ValueKindProto

-- There's one additinoal message wrapped around ValueKind
-- that we need to parse
namespace Cedar.Spec.ValueProto

@[inline]
def mergeValueKind (x1: ValueProto) (v2: ValueKindProto) : ValueProto :=
  let ⟨ v1 ⟩ := x1
  .mk (ValueKindProto.merge v1 v2)

@[inline]
def merge (x1: ValueProto) (x2: ValueProto) : ValueProto :=
  let ⟨ v1 ⟩ := x1
  let ⟨ v2 ⟩ := x2
  .mk (ValueKindProto.merge v1 v2)

partial def toValue (v: ValueProto) : Value :=
  let ⟨vi⟩ := v
  match vi with
    | .prim p => .prim p
    | .set s => .set (Cedar.Data.Set.make (s.map toValue).toList)
    | .record m => .record (Cedar.Data.Map.make (m.map (fun ⟨attr, vi⟩ => ⟨ attr, vi.toValue ⟩)).toList)
    | .ext e => .ext e

end Cedar.Spec.ValueProto

-- The Value message depends on ValueKind
-- and the recursive components of ValueKind
-- depends on Value
mutual
partial def parseFieldValueKindProto (t: Tag) : BParsec (StateM ValueKindProto Unit) := do
  have : Message ValueKindProto := {parseField := parseFieldValueKindProto, merge := ValueKindProto.merge}
  have : Message ValueProto := { parseField := parseFieldValueProto, merge := ValueProto.merge}

  match t.fieldNum with
    | 2 =>
      (@Field.guardWireType Prim) t.wireType
      let x: Prim ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergePrim x))
    | 17 =>
      (@Field.guardWireType (Repeated ValueProto)) t.wireType
      let x: Repeated ValueProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeSet x))
    | 22 =>
      (@Field.guardWireType (Array (String × ValueProto))) t.wireType
      let x: Array (String × ValueProto) ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeRecord x))
    | _ =>
      t.wireType.skip
      pure (pure ())


partial def parseFieldValueProto (t: Tag) : BParsec (StateM ValueProto Unit) := do
  have : Message ValueKindProto := {parseField := parseFieldValueKindProto, merge := ValueKindProto.merge}
  have : Message ValueProto := { parseField := parseFieldValueProto, merge := ValueProto.merge}
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType ValueKindProto) t.wireType
      let x: ValueKindProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (ValueProto.mergeValueKind s x))
    | _ =>
      t.wireType.skip
      pure (pure ())

end

instance : Message ValueKindProto := {
  parseField := parseFieldValueKindProto
  merge := ValueKindProto.merge
}

instance : Message ValueProto := {
  parseField := parseFieldValueProto
  merge := ValueProto.merge
}

namespace Cedar.Spec.Value
@[inline]
def merge (v1: Value) (v2: Value) : Value :=
  match v2 with
    | .prim _ => v2
    | .set s2 => match v1 with
      | .set s1 => Cedar.Data.Set.make (s1.elts ++ s2.elts)
      | _ => v2
    | .record m2 => match v1 with
      | .record m1 => Cedar.Data.Map.make (m1.kvs ++ m2.kvs)
      | _ => v2
    | .ext _ => v2

instance : Field Value := Field.fromIntMessage ValueProto.toValue merge
end Cedar.Spec.Value
