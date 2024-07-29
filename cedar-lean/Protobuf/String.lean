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
Decode UTF-8 encoded strings with ByteArray Parser Combinators
-/
import Protobuf.BParsec
import Protobuf.Util

/-
===========================================================================
Parsing Strings
===========================================================================
-/

namespace Proto

-- NOTE: Will panic if there's not enough bytes to determine the next character
-- NOTE: Does not progress iterator
def utf8DecodeChar (i : Nat) : BParsec Char := do
  let c ← fun it => BParsec.ParseResult.success it it.data[i]!
  if c &&& 0x80 == 0 then
    pure ⟨c.toUInt32, .inl (Nat.lt_trans c.1.2 (by decide))⟩
  else if c &&& 0xe0 == 0xc0 then
    let c1 ← fun it => BParsec.ParseResult.success it it.data[i+1]!
    guard (c1 &&& 0xc0 == 0x80)
    let r := ((c &&& 0x1f).toUInt32 <<< 6) ||| (c1 &&& 0x3f).toUInt32
    guard (0x80 ≤ r)
    -- TODO: Prove h from the definition of r once we have the necessary lemmas
    if h : r < 0xd800 then pure ⟨r, .inl h⟩ else BParsec.fail "Not valid UTF8 Char"
  else if c &&& 0xf0 == 0xe0 then
    let c1 ← fun it => BParsec.ParseResult.success it it.data[i+1]!
    let c2 ← fun it => BParsec.ParseResult.success it it.data[i+2]!
    guard (c1 &&& 0xc0 == 0x80 && c2 &&& 0xc0 == 0x80)
    let r :=
      ((c &&& 0x0f).toUInt32 <<< 12) |||
      ((c1 &&& 0x3f).toUInt32 <<< 6) |||
      (c2 &&& 0x3f).toUInt32
    guard (0x800 ≤ r)
    -- TODO: Prove `r < 0x110000` from the definition of r once we have the necessary lemmas
    if h : r < 0xd800 ∨ 0xdfff < r ∧ r < 0x110000 then pure ⟨r, h⟩ else BParsec.fail "Not valid UTF8 Char"
  else if c &&& 0xf8 == 0xf0 then
    let c1 ← fun it => BParsec.ParseResult.success it it.data[i+1]!
    let c2 ← fun it => BParsec.ParseResult.success it it.data[i+2]!
    let c3 ← fun it => BParsec.ParseResult.success it it.data[i+3]!
    guard (c1 &&& 0xc0 == 0x80 && c2 &&& 0xc0 == 0x80 && c3 &&& 0xc0 == 0x80)
    let r :=
      ((c &&& 0x07).toUInt32 <<< 18) |||
      ((c1 &&& 0x3f).toUInt32 <<< 12) |||
      ((c2 &&& 0x3f).toUInt32 <<< 6) |||
      (c3 &&& 0x3f).toUInt32
    if h : 0x10000 ≤ r ∧ r < 0x110000 then
      pure ⟨r, .inr ⟨Nat.lt_of_lt_of_le (by decide) h.1, h.2⟩⟩
    else BParsec.fail "Not valid UTF8 Char"
  else
    BParsec.fail "Not valid UTF8 Char"


-- Progresses ByteArray.Iterator
-- Assumes UTF8 encoding
private partial def parse_string_helper (remaining: Nat) (r: String) : BParsec String := do
  if remaining = 0 then pure r else
  let empty ← BParsec.empty
  if empty then BParsec.fail s!"Expected more packed uints, Size Remaining: {remaining}" else
  let pos ← fun it => BParsec.ParseResult.success it it.pos
  let c ← utf8DecodeChar pos
  have element_size := String.csize c
  BParsec.forward (element_size)
  parse_string_helper (remaining - element_size) (r.push c)
-- Note: Can likely prove temrination if I show that ∀ c: Char, String.csize c > 0

@[inline]
def parse_string (remaining: Nat) : BParsec String := parse_string_helper remaining ""

@[inline]
def interpret_string (b: ByteArray) : Except String String :=
  BParsec.run (parse_string b.size) b

#guard interpret_string (ByteArray.mk #[116, 101, 115, 116, 105, 110, 103]) = Except.ok "testing"

end Proto
