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
/-
Parsers for Repeated Fields
-/
import Protobuf.BParsec
import Protobuf.Varint
import Protobuf.Types
namespace Proto

partial def parse_uvarint_packed_helper (size_remaining: Nat) (result: Array Nat) (t: PType) : BParsec (Array Nat) := do
  if size_remaining = 0 then
    return result
  else

  let empty ← BParsec.empty
  if empty then
    BParsec.fail s!"Expected more packed uints, Size Remaining: {size_remaining}"

  let startPos ← BParsec.pos

  let element ← match t with
    -- NOTE: One can only hope I can replace this with a map
    | PType.uint32 => fun it => match parse_uint32 it with
      | BParsec.ParseResult.success it r => BParsec.ParseResult.success it r.toNat
      | BParsec.ParseResult.error it e => BParsec.ParseResult.error it e
    | PType.uint64 => fun it => match parse_uint64 it with
      | BParsec.ParseResult.success it r => BParsec.ParseResult.success it r.toNat
      | BParsec.ParseResult.error it e => BParsec.ParseResult.error it e
    | _ => BParsec.fail "Unexpected type"

  let endPos ← BParsec.pos

  let element_size ← pure (endPos - startPos)

  parse_uvarint_packed_helper (size_remaining - element_size) (result.push element) t
-- termination_by size_remaining
-- decreasing_by
--   simp_wf
--   have H1 : element_size > 0 := sorry
--   omega


@[inline]
def parse_uint_packed (size: Nat) (t: PType): BParsec (Array Nat) := parse_uvarint_packed_helper size #[] t

@[inline]
def interpret_uint_packed (b: ByteArray) (t: PType) : Except String (Array Nat) :=
  BParsec.run (parse_uint_packed b.size t) b


partial def parse_varint_packed_helper (size_remaining: Nat) (result: Array Int) (t: PType) : BParsec (Array Int) := do
  if size_remaining = 0 then
    return result
  else

  let empty ← BParsec.empty
  if empty then
    BParsec.fail s!"Expected more packed uints, Size Remaining: {size_remaining}"

  let startPos ← BParsec.pos

  let element ← match t with
    | PType.int32 => fun it => parse_int32 it
    | PType.int64 => fun it => parse_int64 it
    | _ => BParsec.fail "Unexpected type"

  let endPos ← BParsec.pos

  let element_size ← pure (endPos - startPos)

  parse_varint_packed_helper (size_remaining - element_size) (result.push element) t
-- termination_by size_remaining
-- decreasing_by
--   simp_wf
--   have H1 : element_size > 0 := sorry
--   omega


@[inline]
def parse_int_packed (size: Nat) (t: PType): BParsec (Array Int) := parse_varint_packed_helper size #[] t

@[inline]
def interpret_int_packed (b: ByteArray) (t: PType) : Except String (Array Int) :=
  BParsec.run (parse_int_packed b.size t) b

#guard interpret_int_packed (ByteArray.mk #[03, 142, 02, 158, 167, 05]) PType.int64 = Except.ok #[3, 270, 86942]

end Proto
