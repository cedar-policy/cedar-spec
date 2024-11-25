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

/-!
Decode UTF-8 encoded strings with ByteArray Parser Combinators
-/

namespace Proto

-- NOTE: Will panic if there's not enough bytes to determine the next character
-- NOTE: Does not progress iterator
-- Returns the size of the character as well
@[inline]
def utf8DecodeChar (i : Nat) : BParsec (Char × Nat) := do
  let c ← BParsec.inspect λ pos => pos.data[i]!
  if c &&& 0x80 == 0 then
    let char := ⟨c.toUInt32, .inl (Nat.lt_trans c.1.2 (by decide))⟩
    pure ⟨char, 1⟩
  else if c &&& 0xe0 == 0xc0 then
    let c1 ← BParsec.inspect λ pos => pos.data[i+1]!
    if c1 &&& 0xc0 != 0x80 then throw s!"Not a valid UTF8 Char: {c} {c1}" else
    let r := ((c &&& 0x1f).toUInt32 <<< 6) ||| (c1 &&& 0x3f).toUInt32
    if 0x80 > r then throw s!"Not a valid UTF8 Char: {c} {c1}" else
    if h : r < 0xd800 then
      let char := ⟨r, .inl h⟩
      pure ⟨char, 2⟩
    else throw s!"Not valid UTF8 Char: {c} {c1}"
  else if c &&& 0xf0 == 0xe0 then
    let c1 ← BParsec.inspect λ pos => pos.data[i+1]!
    let c2 ← BParsec.inspect λ pos => pos.data[i+2]!
    if ¬(c1 &&& 0xc0 == 0x80 && c2 &&& 0xc0 == 0x80) then
      throw s!"Not a valid UTF8 Char: {c} {c1} {c2}"
    else
    let r :=
      ((c &&& 0x0f).toUInt32 <<< 12) |||
      ((c1 &&& 0x3f).toUInt32 <<< 6) |||
      (c2 &&& 0x3f).toUInt32
    if (0x800 > r) then throw s!"Not a valid UTF8 Char: {c} {c1} {c2}" else
    if h : r < 0xd800 ∨ 0xdfff < r ∧ r < 0x110000 then
      let char := ⟨r, h⟩
      pure ⟨char, 3⟩
    else throw s!"Not valid UTF8 Char: {c} {c1} {c2}"
  else if c &&& 0xf8 == 0xf0 then
    let c1 ← BParsec.inspect λ pos => pos.data[i+1]!
    let c2 ← BParsec.inspect λ pos => pos.data[i+2]!
    let c3 ← BParsec.inspect λ pos => pos.data[i+3]!
    if ¬(c1 &&& 0xc0 == 0x80 && c2 &&& 0xc0 == 0x80 && c3 &&& 0xc0 == 0x80) then
      throw s!"Not a valid UTF8 Char: {c} {c1} {c2} {c3}"
    else
    let r :=
      ((c &&& 0x07).toUInt32 <<< 18) |||
      ((c1 &&& 0x3f).toUInt32 <<< 12) |||
      ((c2 &&& 0x3f).toUInt32 <<< 6) |||
      (c3 &&& 0x3f).toUInt32
    if h : 0x10000 ≤ r ∧ r < 0x110000 then
      let char :=  ⟨r, .inr ⟨Nat.lt_of_lt_of_le (by decide) h.1, h.2⟩⟩
      pure ⟨char, 4⟩
    else throw s!"Not valid UTF8 Char: {c} {c1} {c2} {c3}"
  else
    throw s!"Not valid UTF8 Char: {c}"


-- Progresses ByteArray.Iterator
-- Assumes UTF8 encoding
partial def parseStringHelper (remaining : Nat) (r : String) : BParsec String := do
  if remaining = 0 then pure r else
  let empty ← BParsec.empty
  if empty then throw s!"Expected more packed uints, Size Remaining: {remaining}" else
  let pos ← BParsec.pos
  let ⟨c, elementSize⟩ ← utf8DecodeChar pos
  BParsec.forward (elementSize)
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
