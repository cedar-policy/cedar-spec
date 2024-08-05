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
Parsers for Map Fields
-/
import Protobuf.BParsec
import Protobuf.Field
import Protobuf.Structures
namespace Proto

@[inline]
def parseMapElem (KeyT: Type) (ValueT: Type) [Field KeyT] [Field ValueT]: BParsec (KeyT × ValueT) := do
     let len ← BParsec.attempt Len.parse
     let startPos ← BParsec.pos

     let tag1 ← BParsec.attempt Tag.parse
     let result ← match tag1.fieldNum with
          | 1 =>
               let wt1Matches := (@Field.checkWireType KeyT) tag1.wireType
               if not wt1Matches then
                    throw s!"WireType mismatch"
               let key: KeyT ← Field.parse

               let tag2 ← BParsec.attempt Tag.parse
               let wt2Matches := (@Field.checkWireType ValueT) tag2.wireType
               if not wt2Matches then
                    throw s!"WireType mismatch"
               if tag2.fieldNum != 2 then
                    throw s!"Expected Field Number 2 within map, not {tag2.fieldNum}"
               let value: ValueT ← Field.parse
               pure (Prod.mk key value)
          | 2 =>
               let wt1Matches := (@Field.checkWireType ValueT) tag1.wireType
               if not wt1Matches then
                    throw s!"WireType mismatch"
               let value: ValueT ← Field.parse

               let tag2 ← BParsec.attempt Tag.parse
               let wt2Matches := (@Field.checkWireType KeyT) tag2.wireType
               if not wt2Matches then
                    throw s!"WireType mismatch"
               if tag2.fieldNum != 1 then
                    throw s!"Expected Field Number 1 within map, not {tag2.fieldNum}"
               let key: KeyT ← Field.parse
               pure (Prod.mk key value)

          | _ => throw "Unexpected Field Number within Map Element"

     let endPos ← BParsec.pos

     if endPos - startPos != len.size then
          throw "LEN size invariant not maintained when parsing a map element"

     pure result

instance {α β: Type} [Field α] [Field β]: Field (α × β) := {
  parse := parseMapElem α β
  checkWireType := fun (w: WireType) => WireType.LEN = w
}

end Proto
