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


-- Already defined in Cedar.Spec.Entities
-- abbrev Entities := Map EntityUID EntityData

-- Note that EntityData doesn't contain EntityUID, therefore
-- we need to parse an intermediate representation EntityProto
-- which contains that and transform it to the appropriate types.



namespace Cedar.Spec.Entities

@[inline]
def mergeEntities (result: Entities) (x: Array EntityProto) : Entities :=
  let newKvs := (x.map (fun xi => Prod.mk xi.uid (EntityData.mk xi.attrs xi.ancestors))).toList
  Cedar.Data.Map.make (result.kvs ++ newKvs)

@[inline]
def merge (x: Entities) (y: Entities) : Entities :=
  Cedar.Data.Map.make (x.kvs ++ y.kvs)

def parseField (t: Tag) : BParsec (StateM Entities Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType (Repeated EntityProto)) t.wireType
      let x: Repeated EntityProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEntities s x))
    -- Ignoring 3 | mode
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message Entities := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.Entities
