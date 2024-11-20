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

import Lean.Data.HashMap
import Protobuf.BParsec
import Protobuf.Varint
import Protobuf.WireType

/-!
Various Protobuf Structures, likely will reorganize later
-/

namespace Proto

structure MessageSchema where
  schema : Std.HashMap Nat PType

structure Tag where
  fieldNum : Nat
  wireType : WireType
deriving Repr, DecidableEq, Inhabited

structure Len where
  size : Nat
deriving Repr

namespace VarInt
  @[inline]
  def skip : BParsec Unit := do
    let size ← find_varint_size
    BParsec.forward size
end VarInt

namespace Len
  @[inline]
  def parseSize : BParsec Nat := do
    let isize ← parse_int32
    match isize with
    | Int.negSucc _ => throw "Expected positive size in len payload"
    | Int.ofNat size =>
        pure size

  /-- Skips the LEN and its payload-/
  @[inline]
  def skip : BParsec Unit := do
    let size ← Len.parseSize
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
def interpret? (b : ByteArray) : Except String Tag :=
  BParsec.run Tag.parse b

@[inline]
def interpret! (b : ByteArray) : Tag :=
  BParsec.run! Tag.parse b

end Tag

namespace WireType

@[inline]
def skip (wt : WireType) : BParsec Unit := do
  match wt with
  | .VARINT => VarInt.skip
  | .I64 => BParsec.forward 8
  | .LEN => Len.skip
  | .SGROUP => pure ()
  | .EGROUP => pure ()
  | .I32 => BParsec.forward 4

end WireType

end Proto
