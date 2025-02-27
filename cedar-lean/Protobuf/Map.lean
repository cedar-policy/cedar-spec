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

/-!
Parsers for Map Fields
-/

namespace Proto

def Map (KeyT ValueT : Type) [Field KeyT] [Field ValueT] := Array (KeyT × ValueT)

namespace Map

instance [Field α] [Field β] [Repr α] [Repr β] : Repr (Map α β) where
  reprPrec m n := let a : Array (α × β) := m ; reprPrec a n

instance [Field α] [Field β] : Inhabited (Map α β) where
  default := #[]

instance [Field α] [Field β] [DecidableEq α] [DecidableEq β] : DecidableEq (Map α β) := by
  unfold DecidableEq Map
  exact decEq

instance [Field α] [Field β] : HAppend (Map α β) (Map α β) (Map α β) where
  hAppend m₁ m₂ :=
    let m₁ : Array (α × β) := m₁
    let m₂ : Array (α × β) := m₂
    m₁ ++ m₂

@[inline]
def parse [Inhabited KeyT] [Inhabited ValueT] [Field KeyT] [Field ValueT] : BParsec (Map KeyT ValueT) := do
  let len_size ← Len.parseSize
  let startPos ← BParsec.pos

  let mut key := (default : KeyT)
  let mut val := (default : ValueT)
  while (← BParsec.pos) - startPos < len_size do
    let tag ← Tag.parse
    match tag.fieldNum with
      | 1 => key := (← Field.guardedParse tag)
      | 2 => val := (← Field.guardedParse tag)
      | n => throw s!"Unexpected field number ({n}) within map"

  let endPos ← BParsec.pos
  if endPos - startPos = len_size then
    pure #[(key, val)]
  else
    throw s!"[Map parse] LEN size invariant not maintained: expected {len_size}, parsed {endPos - startPos}"

instance {α β : Type} [Inhabited α] [Inhabited β] [Field α] [Field β] : Field (Map α β) := {
  parse := parse
  expectedWireType := WireType.LEN
  merge := (· ++ ·)
}
end Map
end Proto
