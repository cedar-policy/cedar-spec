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
import Cedar.Spec
import Protobuf.Message
import Protobuf.String

-- Message Dependencies
import CedarProto.EntityUID

open Proto

namespace Cedar.Spec

/-- for the purposes of the Lean implementation, EntityUIDEntry can just be EntityUID -/
def EntityUIDEntry := EntityUID
deriving instance Inhabited for EntityUIDEntry

namespace EntityUIDEntry

@[inline]
def mergeEuid (x1 : EntityUIDEntry) (x2 : EntityUID) : EntityUIDEntry :=
  (@Field.merge EntityUID) x1 x2

@[inline]
def merge (x1 : EntityUIDEntry) (x2 : EntityUIDEntry) : EntityUIDEntry :=
  mergeEuid x1 x2

def parseField (t : Proto.Tag) : BParsec (MergeFn EntityUIDEntry) := do
  match t.fieldNum with
    | 1 =>
      let x : EntityUID ← Field.guardedParse t
      pure (mergeEuid · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message EntityUIDEntry := {
  parseField := parseField
  merge := merge
}

end EntityUIDEntry

end Cedar.Spec
