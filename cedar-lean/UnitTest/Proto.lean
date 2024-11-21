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

import Protobuf.Structures
import Protobuf.String
import Protobuf.Map
import Protobuf.Field
import Protobuf.Message
import Protobuf.Enum
import Protobuf.Varint
import Protobuf.Packed
import UnitTest.Run

/-! Test Cases for Protobuffer functions -/

open Proto

-- Show DecidableEq of Except for unit tests
namespace Except
instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := by
  unfold DecidableEq
  intro a b
  cases a <;> cases b <;> simp only [reduceCtorEq, ok.injEq, error.injEq]
  case ok.error | error.ok => exact instDecidableFalse
  case error.error c d => exact decEq c d
  case ok.ok c d => exact decEq c d
end Except

namespace Proto

/-!
Struct with array of UInt32 for testing purposes
-/
private structure HardCodeStruct where
  f6 : Array UInt32 -- Field 6
deriving Inhabited, Repr, DecidableEq

namespace HardCodeStruct

def merge_6 (result : HardCodeStruct) (x : Array UInt32) : HardCodeStruct :=
  {
    f6 := Field.merge (α := Packed UInt32) result.f6 x
  }

def merge (x : HardCodeStruct) (y : HardCodeStruct) : HardCodeStruct :=
  {
    f6 := Field.merge (α := Packed UInt32) x.f6 y.f6
  }

def parseField (t : Tag) : BParsec (MergeFn HardCodeStruct) := do
  match t.fieldNum with
    | 6 =>
      let x : Packed UInt32 ← Field.guardedParse t
      pure (merge_6 · x)
    | _ =>
      t.wireType.skip
      pure id

instance : Message HardCodeStruct := {
  parseField := parseField
  merge := merge
}

end HardCodeStruct

private inductive A where
  | Monday
  | Tuesday
deriving Repr, Inhabited, DecidableEq

namespace A
def get? (n: Int) : Except String A :=
  match n with
    | 1 => .ok A.Monday
    | 2 => .ok A.Tuesday
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum A where
  fromInt := get?
end A


def tests := [
  UnitTest.suite "General protobuf deserialization tests" ([
    UnitTest.test "false" ⟨λ () => UnitTest.checkEq
      (Field.interpret? (α := Bool) (ByteArray.mk #[0]))
      (.ok false)
    ⟩,
    UnitTest.test "true" ⟨λ () => UnitTest.checkEq
      (Field.interpret? (α := Bool) (ByteArray.mk #[1]))
      (.ok true)
    ⟩,
    UnitTest.test "UInt64" ⟨λ () => UnitTest.checkEq
      (Field.interpret? (α := UInt64) (ByteArray.mk #[150, 01]))
      (.ok 150)
    ⟩,
    UnitTest.test "Int64" ⟨λ () => UnitTest.checkEq
      (Field.interpret? (α := Int64) (ByteArray.mk #[254, 255, 255, 255, 255, 255, 255, 255, 255, 1]))
      (.ok (-2))
    ⟩,
    UnitTest.test "Packed Int64" ⟨λ () => UnitTest.checkEq
      (Field.interpret? (α := Packed Int64) (ByteArray.mk #[06, 03, 142, 02, 158, 167, 05]))
      (.ok #[3, 270, 86942])
    ⟩,
    UnitTest.test "String" ⟨λ () => UnitTest.checkEq
      (Field.interpret? (α := String) (ByteArray.mk #[07, 116, 101, 115, 116, 105, 110, 103]))
      (.ok "testing")
    ⟩,
    UnitTest.test "Tag 1" ⟨λ () => UnitTest.checkEq
      (Tag.interpret? (ByteArray.mk #[08]))
      (.ok (Tag.mk 1 WireType.VARINT))
    ⟩,
    UnitTest.test "Tag 2" ⟨λ () => UnitTest.checkEq
      (Tag.interpret? (ByteArray.mk #[18]))
      (.ok (Tag.mk 2 WireType.LEN))
    ⟩,
    UnitTest.test "Tag 6" ⟨λ () => UnitTest.checkEq
      (Tag.interpret? (ByteArray.mk #[50]))
      (.ok (Tag.mk 6 WireType.LEN))
    ⟩,
    UnitTest.test "HardCodeStruct" ⟨λ () => UnitTest.checkEq
      (Message.interpret? (α := HardCodeStruct) (ByteArray.mk #[50, 06, 03, 142, 02, 158, 167, 05]))
      (.ok (HardCodeStruct.mk #[3, 270, 86942]))
    ⟩,
    UnitTest.test "Enum" ⟨λ () => UnitTest.checkEq
      (Field.interpret? (α := A) (ByteArray.mk #[02]))
      (.ok A.Tuesday)
    ⟩,
    UnitTest.test "map" ⟨λ () => UnitTest.checkEq
      (
        let data := ByteArray.mk #[10, 10, 10, 06, 68, 97, 114, 99, 105, 101, 16, 04, 10, 09, 10, 05,
          83, 104, 97, 119, 110, 16, 02, 10,  09, 10, 05, 67, 97, 114, 108, 121,
          16, 04, 08, 07, 10, 03, 82, 111, 121, 16, 01]
        let interpret_map := BParsec.run (do
          let mut result: Array (String × UInt32) := #[]

          let tag1 ← Tag.parse
          if tag1.fieldNum != 1 then throw "Unexpected field number"

          let element: Map String UInt32 ← Field.parse
          result := Field.merge (α := Map String UInt32) result element

          let tag2 ← Tag.parse
          if tag2.fieldNum != 1 then throw "Unexpected field number"

          let element2: Map String UInt32 ← Field.parse
          result := Field.merge (α := Map String UInt32) result element2

          pure result
        )
        interpret_map data
      )
      (.ok #[("Darcie", 4), ("Shawn", 2)])
    ⟩,
  ] : List (UnitTest.TestCase IO))
]
