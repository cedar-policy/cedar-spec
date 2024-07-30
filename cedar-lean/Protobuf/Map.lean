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
import Protobuf.Structures
namespace Proto

@[inline]
def parse_map_elem (fkey: BParsec α) (fvalue: BParsec β): BParsec (α × β) := do
     let len ← BParsec.attempt Len.parse
     let startPos ← BParsec.pos

     let tag1 ← BParsec.attempt Tag.parse
     let result ← match tag1.fieldNum with
          | 1 =>
               let key ← fkey
               let tag2 ← BParsec.attempt Tag.parse
               if tag2.fieldNum != 2 then
                    throw s!"Expected Field Number 2 within map, not {tag2.fieldNum}"
               let value ← fvalue
               pure (Prod.mk key value)
          | 2 =>
               let value ← fvalue
               let tag2 ← BParsec.attempt Tag.parse
               if tag2.fieldNum != 1 then
                    throw s!"Expected Field Number 1 within map, not {tag2.fieldNum}"

               let key ← fkey
               pure (Prod.mk key value)

          | _ => throw "Unexpected Field Number within Map Element"

     let endPos ← BParsec.pos

     if endPos - startPos != len.size then
          throw "LEN size invariant not maintained when parsing a map element"

     pure result

end Proto
