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
import Protobuf.Structures
import Protobuf.Packed
import Protobuf.WireType

/-!
Protobuf Message class
-/

namespace Proto

def MergeFn (α : Type) : Type := (α → α)

class Message (α : Type) [Inhabited α] where
  parseField : Tag → BParsec (MergeFn α)
  merge : α → α → α

export Message (parseField)
namespace Message

private def parseMessageHelper [Inhabited α] [Message α] (remaining : Nat) (result : α) : BParsec α := do
  if remaining = 0 then
    pure result
  else

  let empty ← BParsec.empty
  if empty then
    throw "Expected more bytes"
  else

  let startPos ← BParsec.pos

  let tag ← Tag.parse

  let f : MergeFn α ← parseField tag

  let endPos ← BParsec.pos

  let newResult := f result
  let elementSize := (endPos - startPos)
  if elementSize = 0 then
    throw "[parseMessageHelper] f did not progress ByteArray"
  else

  (parseMessageHelper (remaining - elementSize) newResult)



@[inline]
def parse [Inhabited α] [Message α] : BParsec α := do
  let remaining ← BParsec.remaining
  let message : α ← parseMessageHelper remaining default
  BParsec.eof
  pure message

@[inline]
def parseWithLen [Inhabited α] [Message α] : BParsec α := do
  let len_size ← Len.parseSize
  let message : α ← parseMessageHelper len_size default
  pure message

@[inline]
def parseWithSize [Inhabited α] [Message α] (size : Nat) : BParsec α := do
  let message : α ← parseMessageHelper size default
  pure message

@[inline]
def interpret? [Inhabited α] [Message α] (b : ByteArray) : Except String α :=
  BParsec.run parse b

@[inline]
def interpret! [Inhabited α] [Message α] (b : ByteArray) : α :=
  BParsec.run! parse b

instance [Inhabited α] [Message α] : Field α := {
  parse := parseWithLen
  checkWireType := fun (w : WireType) => WireType.LEN = w
  merge := merge
}

end Message

end Proto
