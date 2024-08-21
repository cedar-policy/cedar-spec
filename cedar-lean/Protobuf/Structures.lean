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
Various Protobuf Structures, likely will reorganize later
-/
import Lean.Data.HashMap
import Protobuf.BParsec
import Protobuf.Varint
import Protobuf.Types
namespace Proto

structure MessageSchema where
  schema: Lean.HashMap Nat PType

structure Tag where
  fieldNum: Nat
  wireType: WireType
deriving Repr, DecidableEq, Inhabited

structure Len where
  size: Nat
  payload: Slice
deriving Repr, DecidableEq

namespace VarInt
  @[inline]
  def skip : BParsec Unit := do
    let slice ← find_next_varint
    BParsec.forward (slice.last - slice.first)
end VarInt

namespace Len
  @[inline]
  def parse : BParsec Len := do
    let isize ← parse_int32
    match isize with
    | Int.negSucc _ => throw "Expected positive size in len payload"
    | Int.ofNat size =>
        let pos ← BParsec.pos
        let slice := Slice.mk pos (pos + size)
        pure (Len.mk size slice)

  /-- Skips not only the LEN size but also the payload -/
  @[inline]
  def skip : BParsec Unit := do
    let isize ← parse_int32
    match isize with
    | Int.negSucc _ => throw "Expected positive size in len payload"
    | Int.ofNat size =>
        BParsec.forward size

end Len

namespace Tag
@[inline]
def parse : BParsec Tag := do
  let element ← parse_uint32
  have wt_uint := element &&& 7
  let wire_type ← if wt_uint = 0 then pure WireType.VARINT
                    else if wt_uint = 1 then pure WireType.I64
                    else if wt_uint = 2 then pure WireType.LEN
                    else if wt_uint = 3 then pure WireType.SGROUP
                    else if wt_uint = 4 then pure WireType.EGROUP
                    else if wt_uint = 5 then pure WireType.I32
                    else throw "Unexcepted Wire Type"
  have field_num := element >>> 3
  pure (Tag.mk field_num.toNat wire_type)

@[inline]
def interpret? (b: ByteArray) : Except String Tag :=
  BParsec.run Tag.parse b

@[inline]
def interpret! (b: ByteArray) : Tag :=
  BParsec.run! Tag.parse b

end Tag

namespace WireType

@[inline]
def skip (wt: WireType) : BParsec Unit := do
  match wt with
  | .VARINT => VarInt.skip
  | .I64 => BParsec.forward 8
  | .LEN => Len.skip
  | .SGROUP => pure ()
  | .EGROUP => pure ()
  | .I32 => BParsec.forward 4

end WireType

end Proto
