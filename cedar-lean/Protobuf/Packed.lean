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

/-!
Parsers for Repeated Fields
-/

namespace Proto

/-- Repeated fields are assumed to come one record at a time  -/
def Repeated (α : Type) [Field α] : Type := Array α

namespace Repeated

instance [Field α] : Inhabited (Repeated α) where
  default := #[]

instance [DecidableEq α] [Field α] : DecidableEq (Repeated α) := by
  unfold DecidableEq
  unfold Repeated
  intro a b
  apply inferInstance

instance [Repr α] [Field α] : Repr (Repeated α) := by
  unfold Repeated
  apply inferInstance

instance [Field α] : HAppend (Repeated α) (Repeated α) (Repeated α) where
  hAppend a b :=
    let a : Array α := a
    let b : Array α := b
    a ++ b

/-- Parses one value from a record -/
@[inline]
def parse (α : Type) [Field α] : BParsec (Array α) := do
  let element ← Field.parse
  pure #[element]

instance [Field α] : Field (Repeated α) := {
  parse := parse α
  expectedWireType := Field.expectedWireType α
  merge := (· ++ ·)
}

end Repeated

/-- An array of elements that are contained sequentially within
 a single LEN wire type -/
def Packed (α : Type) [Field α] : Type := Array α

namespace Packed

instance [Field α] : Inhabited (Packed α) where
  default := #[]

instance [DecidableEq α] [Field α] : DecidableEq (Packed α) := by
  unfold DecidableEq
  unfold Packed
  intro a b
  apply inferInstance

instance [Repr α] [Field α] : Repr (Packed α) := by
  unfold Packed
  apply inferInstance

instance [Field α] : HAppend (Packed α) (Packed α) (Packed α) where
  hAppend a b :=
    let a : Array α := a
    let b : Array α := b
    a ++ b

@[inline]
def parse (α : Type) [Field α] : BParsec (Array α) := do
  let len_size ← Len.parseSize
  BParsec.foldl
    Field.parse
    (λ arr element => arr.push element)
    len_size
    #[]

instance [Field α] : Field (Packed α) := {
  parse := parse α
  expectedWireType := WireType.LEN
  merge := (· ++ ·)
}

end Packed


end Proto
