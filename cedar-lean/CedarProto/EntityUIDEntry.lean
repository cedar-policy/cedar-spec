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

import CedarProto.EntityUID

open Cedar.Spec
open Proto

-- There are other fields but the Lean client doesn't use it
-- so we save some time by not creating an entire struct
abbrev EntityUIDEntry := EntityUID

namespace Cedar.Spec.EntityUIDEntry

def mergeEuid (x1: EntityUIDEntry) (x2: EntityUID) : EntityUIDEntry :=
  (@Field.merge EntityUID) x1 x2

def merge (x1: EntityUIDEntry) (x2: EntityUIDEntry) : EntityUIDEntry :=
  (@Field.merge EntityUID) x1 x2

def parseField (t: Tag) : BParsec (MessageM EntityUIDEntry) := do
  match t.fieldNum with
    | 2 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => mergeEuid s x)
    | _ =>
      t.wireType.skip
      pure MessageM.pure

instance : Message EntityUIDEntry := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.EntityUIDEntry
