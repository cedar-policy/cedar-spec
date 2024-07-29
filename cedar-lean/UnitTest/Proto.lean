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
instance : DecidableEq (Except String HardCodeStruct) := Except.dec_eq


#guard interpret_bool (ByteArray.mk #[0]) = Except.ok false

#guard interpret_bool (ByteArray.mk #[1]) = Except.ok true

#guard interpret_uint64 (ByteArray.mk #[150, 01]) = 150

#guard interpret_int64 (ByteArray.mk #[254, 255, 255, 255, 255, 255, 255, 255, 255, 1]) = -2

#guard interpret_int64_packed (ByteArray.mk #[03, 142, 02, 158, 167, 05]) = Except.ok #[3, 270, 86942]

#guard interpret_string (ByteArray.mk #[116, 101, 115, 116, 105, 110, 103]) = Except.ok "testing"

#guard Tag.interpret (ByteArray.mk #[08]) = Except.ok (Tag.mk 1 WireType.VARINT)

#guard Tag.interpret (ByteArray.mk #[18]) = Except.ok (Tag.mk 2 WireType.LEN)

#guard Tag.interpret (ByteArray.mk #[50]) = Except.ok (Tag.mk 6 WireType.LEN)

#guard parse_hardcode (ByteArray.mk #[50, 06, 03, 142, 02, 158, 167, 05]).iter =
  Except.ok (HardCodeStruct.mk #[3, 270, 86942])
