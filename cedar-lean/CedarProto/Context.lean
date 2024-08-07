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
import Protobuf.Message
import Protobuf.String

import Cedar

-- Dependencies
import CedarProto.ValueKind


open Cedar.Spec
open Proto

abbrev Context := ValueKind

namespace Cedar.Spec.Context

def mergeValue (x1: Context) (x2: ValueKind) : Context :=
  (@Field.merge ValueKind) x1 x2

def merge (x1: Context) (x2: Context) : Context :=
  (@Field.merge ValueKind) x1 x2

def parseField (t: Tag) : BParsec (MessageM Context) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Value) t.wireType
      let x: ValueKind ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => mergeValue s x)
    | _ =>
      t.wireType.skip
      pure MessageM.pure

instance : Message Context := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.Context
