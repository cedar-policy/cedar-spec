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
import Protobuf.Field
import Protobuf.Util
import Protobuf.Types
namespace Proto


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
  if empty then throw "Expected more bytes"

  -- Due to the PTypes allowed, we can't have a varint with more than 10 bytes
  if H: n ≥ 10 then throw "Too many bytes in this varint" else

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
-- NOTE: Does not progress iterator
@[inline]
def find_next_varint : BParsec Slice := do
  let start_idx ← BParsec.pos
  let end_idx ← BParsec.attempt find_end_of_varint
  let slice ← fun it => BParsec.ParseResult.success it (Slice.mk start_idx end_idx)
  pure slice


-- Note: Panic indexing used but may be able to remove with some work
private def parse_uint64_helper (remaining: Nat) (p: Nat) (r: UInt64) : BParsec UInt64 := do
  if remaining = 0 then pure r else
  let empty ← BParsec.empty
  if empty then throw "Expected more bytes" else
  let byte ← fun it => BParsec.ParseResult.success it it.data[it.pos]!
  BParsec.next -- Progress iterator
  have byte2 := clear_msb8 byte
  have byte3 := byte2.toUInt64 <<< (7 * p.toUInt64)
  parse_uint64_helper (remaining - 1) (p + 1) (r ||| byte3)


@[inline]
def parse_uint64 : BParsec UInt64 := do
  let slice ← BParsec.attempt find_next_varint
  let remaining := slice.last - slice.first
  parse_uint64_helper remaining 0 0


instance : Field UInt64 := {
  parse := parse_uint64
  checkWireType := fun (w: WireType) => WireType.VARINT = w
  merge := Field.Merge.override
}

private def parse_uint32_helper (remaining: Nat) (p: Nat) (r: UInt32) : BParsec UInt32 := do
  if remaining = 0 then pure r else
  let empty ← BParsec.empty -- NOTE: Might be able to remove if we add a hypotheses in the definition
  if empty then throw "Expected more bytes" else
  let byte ← fun it => BParsec.ParseResult.success it it.data[it.pos]!
  BParsec.next -- Progress iterator
  have byte2 := clear_msb8 byte
  have byte3 := byte2.toUInt32 <<< (7 * p.toUInt32)
  parse_uint32_helper (remaining - 1) (p + 1) (r ||| byte3)


@[inline]
def parse_uint32 : BParsec UInt32 := do
  let slice ← BParsec.attempt find_next_varint
  let remaining ← pure (slice.last - slice.first)
  parse_uint32_helper remaining 0 0

instance : Field UInt32 := {
  parse := parse_uint32
  checkWireType := fun w => WireType.VARINT = w
  merge := Field.Merge.override
}

def Int32 := Int
deriving instance Inhabited, DecidableEq for Int32
instance : OfNat Int32 n := ⟨Int.ofNat n⟩
instance : Neg Int32 := { neg := Int.neg }


@[inline]
def parse_int32: BParsec Int32 := do
  let r ← parse_uint32
    match msb_set32 r with
    | true => pure (Int.neg (~~~(r - (1: UInt32))).toNat)
    | false => pure (Int.ofNat r.toNat)


instance : Field Int32 := {
  parse := parse_int32
  checkWireType := fun w => WireType.VARINT = w
  merge := Field.Merge.override
}

def Int64 := Int
deriving instance Inhabited, DecidableEq for Int64
instance : OfNat Int64 n := ⟨Int.ofNat n⟩
instance : Neg Int64 := { neg := Int.neg }


@[inline]
def parse_int64: BParsec Int64 := do
  let r ← parse_uint64
  if msb_set64 r then
    pure (Int.neg (~~~(r - (1: UInt64))).toNat)
  else
    pure (Int.ofNat r.toNat)

instance : Field Int64 := {
  parse := parse_int64
  checkWireType := fun w => WireType.VARINT = w
  merge := Field.Merge.override
}

@[inline]
def parse_bool : BParsec Bool := do
  let result ← parse_int32
  if result = 1 then pure true else
  if result = 0 then pure false else
  throw "Expected 00 or 01"

instance : Field Bool := {
  parse := Proto.parse_bool
  checkWireType := fun w => WireType.VARINT = w
  merge := Field.Merge.override
}

end Proto
