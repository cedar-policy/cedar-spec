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

@[inline]
def parse [Inhabited KeyT] [Inhabited ValueT] [Field KeyT] [Field ValueT] : BParsec (Map KeyT ValueT) := do
     let len_size ← Len.parseSize
     let startPos ← BParsec.pos

     let tag1 ← Tag.parse
     let result ← match tag1.fieldNum with
          | 1 =>
               let wt1Matches := (@Field.checkWireType KeyT) tag1.wireType
               if not wt1Matches then
                    throw s!"WireType mismatch"
               else
               let key : KeyT ← Field.parse

               -- Since the fields are optional, check to see if we're done parsing now
               let curPos ← BParsec.pos
               if curPos - startPos == len_size then
                    pure #[(Prod.mk key (default : ValueT))]
               else

               let tag2 ← Tag.parse
               let wt2Matches := (@Field.checkWireType ValueT) tag2.wireType
               if not wt2Matches then
                    throw s!"WireType mismatch"
               else
               if tag2.fieldNum != 2 then
                    throw s!"Expected Field Number 2 within map, not {tag2.fieldNum}"
               else
               let value : ValueT ← Field.parse
               pure #[(Prod.mk key value)]
          | 2 =>
               let wt1Matches := (@Field.checkWireType ValueT) tag1.wireType
               if not wt1Matches then
                    throw s!"WireType mismatch"
               else
               let value : ValueT ← Field.parse

               -- Since the fields are optional, check to see if we're done parsing now
               let curPos ← BParsec.pos
               if curPos - startPos == len_size then
                    pure #[(Prod.mk (default : KeyT) value)]
               else

               let tag2 ← Tag.parse
               let wt2Matches := (@Field.checkWireType KeyT) tag2.wireType
               if not wt2Matches then
                    throw s!"WireType mismatch"
               else
               if tag2.fieldNum != 1 then
                    throw s!"Expected Field Number 1 within map, not {tag2.fieldNum}"
               else
               let key : KeyT ← Field.parse
               pure #[(Prod.mk key value)]

          | _ => throw "Unexpected Field Number within Map Element"

     let endPos ← BParsec.pos

     if endPos - startPos != len_size then
          throw s!"[Map parse] LEN size invariant not maintained: expected {len_size}, parsed {endPos - startPos}"

     pure result

instance {α β : Type} [Inhabited α] [Inhabited β] [Field α] [Field β] : Field (Map α β) := {
  parse := parse
  checkWireType := (· = WireType.LEN)
  merge := Field.Merge.concatenate
}
end Map
end Proto
