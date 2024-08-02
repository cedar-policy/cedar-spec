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
/- Test Cases for Protobuffer functions -/
import Protobuf.Structures
import Protobuf.HardCodeTest
import Protobuf.String
import Protobuf.Map
import Protobuf.Field
import Protobuf.Enum
import Protobuf.Varint
import Protobuf.Packed
open Proto

-- Show DecidableEquality of Except for unit tests
namespace Except
def dec_eq [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := by
  unfold DecidableEq
  intro a b
  cases a <;> cases b <;>
  -- Get rid of obvious cases where .ok != .err
  try { apply isFalse ; intro h ; injection h }
  case error.error c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)
  case ok.ok c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)
end Except

instance : DecidableEq (Except String String) := Except.dec_eq
instance : DecidableEq (Except String Bool) := Except.dec_eq
instance : DecidableEq (Except String (Array Int)) := Except.dec_eq
instance : DecidableEq (Except String (Array Nat)) := Except.dec_eq
instance : DecidableEq (Except String Tag) := Except.dec_eq
instance : DecidableEq (Except String UInt32) := Except.dec_eq
instance : DecidableEq (Except String UInt64) := Except.dec_eq
instance : DecidableEq (Except String Int32) := Except.dec_eq
instance : DecidableEq (Except String Int64) := Except.dec_eq
instance : DecidableEq (Except String HardCodeStruct) := Except.dec_eq
instance : DecidableEq (Except String (Array (String × UInt32))) := Except.dec_eq
instance : DecidableEq (Except String (Packed Int64)) := Except.dec_eq


#guard interpret? (ByteArray.mk #[0]) Bool = Except.ok false
#guard interpret? (ByteArray.mk #[1]) Bool = Except.ok true
#guard interpret? (ByteArray.mk #[150, 01]) UInt64 = Except.ok 150
#guard interpret? (ByteArray.mk #[254, 255, 255, 255, 255, 255, 255, 255, 255, 1]) Int64 = Except.ok (-2)
#guard interpret? (ByteArray.mk #[06, 03, 142, 02, 158, 167, 05]) (Packed Int64) = Except.ok #[3, 270, 86942]
#guard interpret? (ByteArray.mk #[07, 116, 101, 115, 116, 105, 110, 103]) String = Except.ok "testing"
#guard Tag.interpret (ByteArray.mk #[08]) = Except.ok (Tag.mk 1 WireType.VARINT)
#guard Tag.interpret (ByteArray.mk #[18]) = Except.ok (Tag.mk 2 WireType.LEN)
#guard Tag.interpret (ByteArray.mk #[50]) = Except.ok (Tag.mk 6 WireType.LEN)

#eval interpret_message (ByteArray.mk #[50, 06, 03, 142, 02, 158, 167, 05]) =
  Except.ok (HardCodeStruct.mk #[3, 270, 86942])

def map_test : Except String (Array (String × UInt32)) :=
 have data := ByteArray.mk #[10, 10, 10, 06, 68, 97, 114, 99, 105, 101, 16, 04, 10, 09, 10, 05,
 83, 104, 97, 119, 110, 16, 02, 10,  09, 10, 05, 67, 97, 114, 108, 121,
 16, 04, 08, 07, 10, 03, 82, 111, 121, 16, 01]
 BParsec.run (do
     let mut result: Array (String × UInt32) := #[]

     let tag1 ← Tag.parse
     if tag1.fieldNum != 1 then
          throw "Unexpected field number"

     let element ← parse_map_elem String UInt32
     result := result.push element

     let tag2 ← Tag.parse
     if tag2.fieldNum != 1 then
          throw "Unexpected field number"

     let element2 ← parse_map_elem String UInt32
     result := result.push element2

     pure result
 ) data

#guard map_test = Except.ok #[("Darcie", 4), ("Shawn", 2)]

-- Enum Test

inductive A where
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

instance : DecidableEq (Except String A) := Except.dec_eq

#guard interpret? (ByteArray.mk #[02]) A = Except.ok A.Tuesday
