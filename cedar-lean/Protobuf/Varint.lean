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
import Protobuf.WireType

/-!
Variable-width integers and parsers for their relevant
Protobuf Types
-/

namespace Proto

@[inline] def msb_set8(i : UInt8) : Bool := i &&& (128 : UInt8) != 0
@[inline] def clear_msb8(i : UInt8) : UInt8 := i &&& (127 : UInt8)

@[inline] def msb_set32(i : UInt32) : Bool := i &&& (2147483648 : UInt32) != 0
@[inline] def clear_msb32(i : UInt32) : UInt32 := i &&& (2147483648 : UInt32)

@[inline] def msb_set64(i : UInt64) : Bool := i &&& (9223372036854775808 : UInt64) != 0
@[inline] def clear_msb64(i : UInt64) : UInt64 := i &&& (9223372036854775808 : UInt64)


/--
Parse a varint in a single pass, progressing the iterator as it accumulates
the value. `n` is the number of bytes consumed so far and `r` the value
accumulated from them.
-/
private def parse_uint64_helper (n : Nat) (r : UInt64) : BParsec UInt64 := do
  -- Due to the PTypes allowed, we can't have a varint with more than 10 bytes
  if H : n ≥ 10 then throw "Too many bytes in this varint" else
  let byte ← BParsec.nextByte
  match byte with
  | none => throw "Expected more bytes"
  | some byte =>
    have byte2 := clear_msb8 byte
    have byte3 := byte2.toUInt64 <<< (7 * n.toUInt64)
    if msb_set8 byte then
      parse_uint64_helper (n + 1) (r ||| byte3)
    else
      pure (r ||| byte3)
termination_by 10 - n


@[inline]
def parse_uint64 : BParsec UInt64 := parse_uint64_helper 0 0


instance : Field UInt64 := {
  parse := parse_uint64
  expectedWireType := WireType.VARINT
  merge := Field.Merge.override
}

/-- Parse a varint as a 64-bit value and truncate it to 32 bits, as the
Protobuf encoding of `int32` and `uint32` requires -/
@[inline]
def parse_uint32 : BParsec UInt32 := do
  let r ← parse_uint64
  pure r.toUInt32

instance : Field UInt32 := {
  parse := parse_uint32
  expectedWireType := WireType.VARINT
  merge := Field.Merge.override
}

def Int32 := Int
deriving instance Repr, Inhabited, DecidableEq for Int32
instance : OfNat Int32 n := ⟨Int.ofNat n⟩
instance : Neg Int32 := { neg := Int.neg }


@[inline]
def parse_int32 : BParsec Int32 := do
  let r ← parse_uint32
  if msb_set32 r then
    pure (Int.neg (~~~(r - (1 : UInt32))).toNat)
  else
    pure (Int.ofNat r.toNat)


instance : Field Int32 := {
  parse := parse_int32
  expectedWireType := WireType.VARINT
  merge := Field.Merge.override
}

def Int64 := Int
deriving instance Repr, Inhabited, DecidableEq for Int64
instance : OfNat Int64 n := ⟨Int.ofNat n⟩
instance : Neg Int64 := { neg := Int.neg }


@[inline]
def parse_int64 : BParsec Int64 := do
  let r ← parse_uint64
  if msb_set64 r then
    pure (Int.neg (~~~(r - (1 : UInt64))).toNat)
  else
    pure (Int.ofNat r.toNat)

instance : Field Int64 := {
  parse := parse_int64
  expectedWireType := WireType.VARINT
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
  expectedWireType := WireType.VARINT
  merge := Field.Merge.override
}

end Proto
