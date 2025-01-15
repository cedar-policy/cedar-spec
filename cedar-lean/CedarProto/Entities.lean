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

-- Message Dependencies
import CedarProto.Entity

open Proto

namespace Cedar.Spec

-- Note that Cedar.Spec.Entities is defined as
-- abbrev Entities := Map EntityUID EntityData

-- Note that EntityData doesn't contain EntityUID, therefore
-- we need to parse an intermediate representation EntityProto
-- which contains that and transform it to the appropriate types.

def EntitiesProto : Type := Array EntityProto
deriving instance Inhabited for EntitiesProto

namespace EntitiesProto

@[inline]
def mergeEntities (result : EntitiesProto) (x : Repeated EntityProto) : EntitiesProto :=
  have x : Array EntityProto := x.map λ xi => { xi with data := xi.data.mkWf }
  have result : Array EntityProto := result
  result ++ x

@[inline]
def merge (x : EntitiesProto) (y : EntitiesProto) : EntitiesProto :=
  have x : Array EntityProto := x
  have y : Array EntityProto := y
  x ++ y

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn EntitiesProto) := do
  match t.fieldNum with
    | 1 =>
      let x : Repeated EntityProto ← Field.guardedParse t
      pure (pure $ mergeEntities · x)
    -- Ignoring 3 | mode
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message EntitiesProto := {
  parseField := parseField
  merge := merge
}

@[inline]
def toEntities (e : EntitiesProto) : Entities :=
  Cedar.Data.Map.make (e.toList.map λ entity => ⟨entity.uid, entity.data⟩)

end EntitiesProto

namespace Entities
@[inline]
def merge (e1 : Entities) (e2 : Entities) : Entities :=
  let e1 : Cedar.Data.Map EntityUID EntityData := e1
  let e2 : Cedar.Data.Map EntityUID EntityData := e2
  -- Don't sort if e1 is empty
  match e1.kvs with
    | [] => e2
    | _ => Cedar.Data.Map.make (e2.kvs ++ e1.kvs)

instance : Field Entities := Field.fromInterField EntitiesProto.toEntities merge

end Entities

end Cedar.Spec
