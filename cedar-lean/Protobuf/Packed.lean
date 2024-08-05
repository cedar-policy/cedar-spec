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
Parsers for Repeated Fields
-/
import Protobuf.BParsec
import Protobuf.Field
import Protobuf.Structures
import Protobuf.Types

namespace Proto

def Packed (α: Type) [Field α] : Type := Array α

instance [Field α] : Inhabited (Packed α) where
  default := #[]

instance [DecidableEq α] [Field α] : DecidableEq (Packed α) := by
  unfold DecidableEq
  unfold Packed
  intro a b
  apply inferInstance

def parsePacked (α: Type) [Field α] : BParsec (Array α) := do
  let len ← BParsec.attempt Len.parse
  BParsec.foldl
    Field.parse
    (fun arr => fun element => arr.push element)
    len.size
    #[]

instance {α: Type} [Field α]: Field (Packed α) := {
  parse := (parsePacked α)
  checkWireType := fun (w: WireType) => WireType.LEN = w
}

end Proto
