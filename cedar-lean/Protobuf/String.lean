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
import Protobuf.WireType
import Batteries.Data.UInt

/-!
Decode UTF-8 encoded strings with ByteArray Parser Combinators
-/

namespace Proto

@[inline]
def parse_string : BParsec String := do
  let len_size ← Len.parseSize
  let string_bytes ← BParsec.nextByteArray len_size
  match string_bytes with
  | some string_bytes =>
    match String.fromUTF8? string_bytes with
    | some string => pure string
    | none => throw "[parse_string] invalid UTF-8 encoding in string bytes"
  | none => throw s!"[parse_string] expected {len_size} bytes for string but reached end of input"

instance : Field String := {
  parse := parse_string
  expectedWireType := WireType.LEN
  merge := Field.Merge.override
}

end Proto
