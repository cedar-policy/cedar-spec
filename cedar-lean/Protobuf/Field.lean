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
Protobuf fields and their parsers
-/
import Protobuf.BParsec
import Protobuf.Types
namespace Proto

class Field (α: Type) where
  parse: BParsec α
  checkWireType: WireType → Bool
  merge: α → α → α

namespace Field


namespace Merge

/-- Models override semantics, replaces the former value with the later -/
@[inline]
def override (_: α) (x: α): α := x

/-- Concatenation semantics, combines two arrays -/
@[inline]
def concatenate (x1: Array α) (x2: Array α): Array α :=
  x1.append x2

end Merge

@[inline]
def interpret! {α: Type} [Field α] [Inhabited α] (b: ByteArray) : α :=
  BParsec.run! Field.parse b

@[inline]
def interpret? {α: Type} [Field α] [Inhabited α] (b: ByteArray) : Except String α :=
  BParsec.run Field.parse b

@[inline]
def guardWireType {α: Type} [Field α] (wt: WireType) : BParsec Unit := do
  let wtMatches := (@Field.checkWireType α) wt
  if not wtMatches then
    throw s!"WireType mismatch"

def fromInterField {α β: Type} [Inhabited α] [Field α] (convert: α → β) (merge: β → β → β) : Field β := {
  parse := do
    let intMessage: α ← Field.parse
    pure (convert intMessage)
  checkWireType := Field.checkWireType α
  merge := merge
}

end Field

end Proto
