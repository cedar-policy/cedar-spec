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
Variable-width integers and parsers for their relevant
Protobuf Types
-/
import Protobuf.BParsec
import Protobuf.Util


def msb_set8(i: UInt8) : Bool := i &&& (128: UInt8) != 0
def clear_msb8(i: UInt8) : UInt8 := i &&& (127: UInt8)

def msb_set32(i: UInt32): Bool := i &&& (2147483648: UInt32) != 0
def clear_msb32(i: UInt32) : UInt32 := i &&& (2147483648: UInt32)

def msb_set64(i: UInt64): Bool := i &&& (9223372036854775808: UInt64) != 0
def clear_msb64(i: UInt64): UInt64 := i &&& (9223372036854775808: UInt64)


-- Does not progress iterator
-- Has panic! indexing, should work towards adding needed proof
private def find_end_of_varint_helper  (n: Nat) : BParsec Nat := do
  let empty ← BParsec.empty
  have H0 := empty
  if empty then BParsec.fail s!"Expected more bytes" else

  -- Due to the PTypes allowed, we can't have a varint with more than 10 bytes
  if H: n ≥ 10 then BParsec.fail "Too many bytes in this varint" else

  let msbSet ← fun it => BParsec.ParseResult.success it (msb_set8 it.data[it.pos + n]!)
  if ¬msbSet then
    let pos ← BParsec.pos
    pure (pos + n + 1) -- Include current byte as part of varint
  else

  find_end_of_varint_helper (n + 1)
termination_by 10 - n

@[inline]
def find_end_of_varint : BParsec Nat := find_end_of_varint_helper 0


/- Find the start and end indices of the next varint -/
@[inline]
def find_varint : BParsec Slice := do
  let start_idx ← BParsec.pos
  let end_idx ← BParsec.attempt find_end_of_varint
  let slice ← fun it => BParsec.ParseResult.success it (Slice.mk start_idx end_idx)
  pure slice


-- theorem find_varint_success_size_gt_0 (i: ByteArray.Iterator) : (find_varint i) = BParsec.ParseResult.success i2 slice → slice.last - slice.first > 0 := by
--   unfold find_varint
--   unfold find_end_of_varint
--   unfold find_end_of_varint_helper
--   unfold BParsec.attempt
--   unfold BParsec.pos
--   unfold bind
--   unfold Monad.toBind
--   unfold BParsec.instMonad
--   dsimp
--   unfold BParsec.bind
--   dsimp
--   unfold pure
--   unfold Applicative.toPure
--   unfold Alternative.toApplicative
--   unfold BParsec.instAlternative
--   unfold Monad.toApplicative
--   unfold BParsec.instMonad
--   unfold BParsec.pure
--   dsimp
--   unfold BParsec.fail
--   unfold ByteArray.Iterator.empty
--   cases i
--   dsimp
--   -- Induction on data+: ByteArray
--   intro H
--   sorry

-- Note: Panic indexing used but may be able to remove with some work
private def parse_uint64_helper (remaining: Nat) (p: Nat) (r: UInt64) : BParsec UInt64 := do
  if remaining = 0 then pure r else
  let empty ← BParsec.empty
  if empty then BParsec.fail "Expected more bytes" else
  let byte ← fun it => BParsec.ParseResult.success it it.data[it.pos]!
  BParsec.next -- Progress iterator
  have byte2 := clear_msb8 byte
  have byte3 := byte2.toUInt64 <<< (7 * p.toUInt64)
  parse_uint64_helper (remaining - 1) (p + 1) (r ||| byte3)


@[inline]
def parse_uint64 (remaining: Nat) : BParsec UInt64 := parse_uint64_helper remaining 0 0

@[inline]
def interpret_uint64 (b: ByteArray) : UInt64 :=
  BParsec.run! (parse_uint64_helper b.size 0 0) b

#guard interpret_uint64 (ByteArray.mk #[150, 01]) = 150


private def parse_uint32_helper (remaining: Nat) (p: Nat) (r: UInt32) : BParsec UInt32 := do
  if remaining = 0 then pure r else
  let empty ← BParsec.empty -- NOTE: Might be able to remove if we add a hypotheses in the definition
  if empty then BParsec.fail "Expected more bytes" else
  let byte ← fun it => BParsec.ParseResult.success it it.data[it.pos]!
  BParsec.next -- Progress iterator
  have byte2 := clear_msb8 byte
  have byte3 := byte2.toUInt32 <<< (7 * p.toUInt32)
  parse_uint32_helper (remaining - 1) (p + 1) (r ||| byte3)


@[inline]
def parse_uint32 (remaining: Nat) : BParsec UInt32 := parse_uint32_helper remaining 0 0

@[inline]
def interpret_uint32 (b: ByteArray) : UInt32 :=
  BParsec.run! (parse_uint32_helper b.size 0 0) b


@[inline]
def parse_int32 (remaining: Nat): BParsec Int := do
  let r ← parse_uint32 remaining
    match msb_set32 r with
    | true => pure (Int.neg (~~~(r - (1: UInt32))).toNat)
    | false => pure (Int.ofNat r.toNat)


@[inline]
def interpret_int32 (b: ByteArray) : Int :=
  BParsec.run! (parse_int32 b.size) b


@[inline]
def parse_int64 (remaining: Nat): BParsec Int := do
  let r ← parse_uint64 remaining
    match msb_set64 r with
    | true => pure (Int.neg (~~~(r - (1: UInt64))).toNat)
    | false => pure (Int.ofNat r.toNat)


@[inline]
def interpret_int64 (b: ByteArray) : Int :=
  BParsec.run! (parse_int32 b.size) b

#guard interpret_int64 (ByteArray.mk #[254, 255, 255, 255, 255, 255, 255, 255, 255, 1]) = -2


@[inline]
def parse_bool : BParsec Bool := do
  let result ← parse_int32 1
  if result = 1 then pure true else
  if result = 0 then pure false else
  BParsec.fail "Expected 00 or 01"

@[inline]
def interpret_bool (b: ByteArray) : Except String Bool :=
  BParsec.run parse_bool b

#guard interpret_bool (ByteArray.mk #[0]) = Except.ok false
#guard interpret_bool (ByteArray.mk #[1]) = Except.ok true
