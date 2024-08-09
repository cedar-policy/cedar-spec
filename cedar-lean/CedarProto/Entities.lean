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

import CedarProto.Entity

import Cedar
open Cedar.Spec
open Proto


namespace Cedar.Spec
def EntitiesProto := Array (EntityUID × EntityData)
deriving instance Inhabited for EntitiesProto
end Cedar.Spec


-- Already defined in Cedar.Spec.Entities
-- abbrev Entities := Map EntityUID EntityData

-- Note that EntityData doesn't contain EntityUID, therefore
-- we need to parse an intermediate representation EntityProto
-- which contains that and transform it to the appropriate types.

namespace Cedar.Spec.EntitiesProto

@[inline]
def toEntitiesWf (e: EntitiesProto): Entities :=
  Cedar.Data.Map.make (e.map (fun ⟨euid, entity⟩ => ⟨euid, entity.makeWf⟩)).toList

@[inline]
def mergeEntities (result: EntitiesProto) (x: Array EntityProto) : EntitiesProto :=
  let newKvs := x.map (fun xi => Prod.mk xi.uid (EntityData.mk xi.attrs xi.ancestors))
  let result : Array (EntityUID × EntityData) := result
  result ++ newKvs

@[inline]
def merge (x: EntitiesProto) (y: EntitiesProto) : EntitiesProto :=
  let x : Array (EntityUID × EntityData) := x
  let y : Array (EntityUID × EntityData) := y
  x ++ y

def parseField (t: Tag) : BParsec (StateM EntitiesProto Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType (Repeated EntityProto)) t.wireType
      let x: Repeated EntityProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEntities s x))
    -- Ignoring 3 | mode
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message EntitiesProto := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.EntitiesProto
