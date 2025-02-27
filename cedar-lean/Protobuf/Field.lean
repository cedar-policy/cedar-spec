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
import Protobuf.WireType

/-!
Protobuf fields and their parsers
-/

namespace Proto

class Field (α : Type) where
  parse : BParsec α
  expectedWireType : WireType
  merge : α → α → α

namespace Field


namespace Merge

/-- Models override semantics, replaces the former value with the latter -/
@[inline]
def override (_ : α) (x : α) : α := x

end Merge

@[inline]
def interpret! {α : Type} [Field α] [Inhabited α] (b : ByteArray) : α :=
  BParsec.run! Field.parse b

@[inline]
def interpret? {α : Type} [Field α] [Inhabited α] (b : ByteArray) : Except String α :=
  BParsec.run Field.parse b

@[inline]
def guardWireType {α : Type} [Field α] (wt : WireType) : BParsec Unit := do
  let foundWt := Field.expectedWireType α
  if foundWt ≠ wt then
    throw s!"WireType mismatch: found {repr foundWt}, expected {repr wt}"

instance [Field α] : Field (Option α) where
  parse := Field.parse.map some
  merge
    | some a₁, some a₂ => some (Field.merge a₁ a₂)
    | _, a₂ => a₂
  expectedWireType := Field.expectedWireType α

@[inline]
def fromInterField {α β : Type} [Inhabited α] [Field α] (convert : α → β) (merge : β → β → β) : Field β := {
  parse := do
    let m : α ← Field.parse
    pure $ convert m
  expectedWireType := Field.expectedWireType α
  merge := merge
}

end Field

end Proto
