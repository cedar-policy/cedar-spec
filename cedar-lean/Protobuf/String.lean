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
import Protobuf.Field
import Protobuf.Structures
import Protobuf.WireType
import Batteries.Data.UInt

/-!
Decode UTF-8 encoded strings with ByteArray Parser Combinators
-/

namespace Proto

/--
  Decodes a UTF8 Char from the iterator, advancing it appropriately, and
  throwing (not panicking) if the byte sequence at the iterator's current position
  is invalid UTF8 or not long enough
-/
@[inline]
def utf8DecodeChar : BParsec Char := do
  let c₀ ← BParsec.nextByte
  match c₀ with
  | none => throw "Not enough bytes for UTF8 Char"
  | some c₀ =>
  if c₀ &&& 0x80 == 0 then
    pure ⟨c₀.toUInt32, .inl (by simp only [UInt8.toNat_toUInt32]; have := UInt8.toNat_lt c₀; omega;)⟩
  else if c₀ &&& 0xe0 == 0xc0 then
    let c₁ ← BParsec.nextByte
    match c₁ with
    | none => throw "Not enough bytes for UTF8 Char"
    | some c₁ =>
    if c₁ &&& 0xc0 != 0x80 then throw s!"Not a valid UTF8 Char: {c₀} {c₁}" else
    let r := ((c₀ &&& 0x1f).toUInt32 <<< 6) ||| (c₁ &&& 0x3f).toUInt32
    if 0x80 > r then throw s!"Not a valid UTF8 Char: {c₀} {c₁}" else
    if h : r < 0xd800 then
      pure ⟨r, .inl h⟩
    else throw s!"Not valid UTF8 Char: {c₀} {c₁}"
  else if c₀ &&& 0xf0 == 0xe0 then
    let c₁ ← BParsec.nextByte
    let c₂ ← BParsec.nextByte
    match c₁, c₂ with
    | none, _ | _, none => throw "Not enough bytes for UTF8 Char"
    | some c₁, some c₂ =>
    if ¬(c₁ &&& 0xc0 == 0x80 && c₂ &&& 0xc0 == 0x80) then
      throw s!"Not a valid UTF8 Char: {c₀} {c₁} {c₂}"
    else
    let r :=
      ((c₀ &&& 0x0f).toUInt32 <<< 12) |||
      ((c₁ &&& 0x3f).toUInt32 <<< 6) |||
      (c₂ &&& 0x3f).toUInt32
    if (0x800 > r) then throw s!"Not a valid UTF8 Char: {c₀} {c₁} {c₂}" else
    if h : r < 0xd800 ∨ 0xdfff < r ∧ r < 0x110000 then
      pure ⟨r, h⟩
    else throw s!"Not valid UTF8 Char: {c₀} {c₁} {c₂}"
  else if c₀ &&& 0xf8 == 0xf0 then
    let c₁ ← BParsec.nextByte
    let c₂ ← BParsec.nextByte
    let c₃ ← BParsec.nextByte
    match c₁, c₂, c₃ with
    | none, _, _ | _, none, _ | _, _, none => throw "Not enough bytes for UTF8 Char"
    | some c₁, some c₂, some c₃ =>
    if ¬(c₁ &&& 0xc0 == 0x80 && c₂ &&& 0xc0 == 0x80 && c₃ &&& 0xc0 == 0x80) then
      throw s!"Not a valid UTF8 Char: {c₀} {c₁} {c₂} {c₃}"
    else
    let r :=
      ((c₀ &&& 0x07).toUInt32 <<< 18) |||
      ((c₁ &&& 0x3f).toUInt32 <<< 12) |||
      ((c₂ &&& 0x3f).toUInt32 <<< 6) |||
      (c₃ &&& 0x3f).toUInt32
    if h : 0x10000 ≤ r ∧ r < 0x110000 then
      pure ⟨r, .inr ⟨Nat.lt_of_lt_of_le (by decide) h.1, h.2⟩⟩
    else throw s!"Not valid UTF8 Char: {c₀} {c₁} {c₂} {c₃}"
  else
    throw s!"Not valid UTF8 Char: {c₀}"


-- Progresses ByteArray.Iterator
-- Assumes UTF8 encoding
partial def parseStringHelper (remaining : Nat) (r : String) : BParsec String := do
  if remaining = 0 then pure r else
  let empty ← BParsec.empty
  if empty then throw s!"Expected more packed uints, Size Remaining: {remaining}" else
  let start_pos ← BParsec.pos
  let c ← utf8DecodeChar
  let end_pos ← BParsec.pos
  let elementSize := end_pos - start_pos
  parseStringHelper (remaining - elementSize) (r.push c)

@[inline]
def parse_string : BParsec String := do
  let len_size ← Len.parseSize
  parseStringHelper len_size ""

instance : Field String := {
  parse := parse_string
  expectedWireType := WireType.LEN
  merge := Field.Merge.override
}

end Proto
