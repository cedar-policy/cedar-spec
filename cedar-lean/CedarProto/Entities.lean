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
import Cedar

-- Message Dependencies
import CedarProto.Entity

open Proto

namespace Cedar.Spec

-- Already defined in Cedar.Spec.Entities
-- abbrev Entities := Map EntityUID EntityData

-- Note that EntityData doesn't contain EntityUID, therefore
-- we need to parse an intermediate representation EntityProto
-- which contains that and transform it to the appropriate types.

def EntitiesProto: Type := Array EntityProto
deriving instance Inhabited for EntitiesProto

namespace EntitiesProto

@[inline]
def mergeEntities (result: EntitiesProto) (x: Repeated EntityProto) : EntitiesProto :=
  have x : Array EntityProto := x
  have result : Array EntityProto := result
  x ++ result

@[inline]
def merge (x: EntitiesProto) (y: EntitiesProto) : EntitiesProto :=
  have y : Repeated EntityProto := y
  mergeEntities x y

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

@[inline]
def toEntities (e: EntitiesProto): Entities :=
  Cedar.Data.Map.mk (e.map (fun entity => ⟨entity.uid, EntityProto.toEntityData entity⟩)).toList

end EntitiesProto

namespace Entities
@[inline]
def merge (e1: Entities) (e2: Entities): Entities :=
  let e1: Cedar.Data.Map EntityUID EntityData := e1
  let e2: Cedar.Data.Map EntityUID EntityData := e2
  Cedar.Data.Map.mk (e2.kvs ++ e1.kvs)

instance : Field Entities := Field.fromInterField EntitiesProto.toEntities merge

def mkWf (e: Entities) : Entities :=
  Cedar.Data.Map.make (e.kvs.map (fun (euid, edata) => (euid, edata.mkWf)))

end Entities

end Cedar.Spec
