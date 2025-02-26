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
instance : HAppend EntitiesProto EntitiesProto EntitiesProto where
  hAppend x y :=
    let x : Array EntityProto := x
    let y : Array EntityProto := y
    x ++ y
instance : HAppend EntitiesProto (Array EntityProto) EntitiesProto where
  hAppend x y :=
    let x : Array EntityProto := x
    x ++ y

namespace EntitiesProto

@[inline]
def mergeEntities (result : EntitiesProto) (x : Array EntityProto) : EntitiesProto :=
  result ++ x

@[inline]
def merge (x : EntitiesProto) (y : EntitiesProto) : EntitiesProto :=
  x ++ y

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn EntitiesProto) := do
  match t.fieldNum with
    | 1 =>
      let x : Repeated EntityProto ← Field.guardedParse t
      pure (pure $ mergeEntities · x)
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
  -- Don't sort if e1 is empty
  match e1.kvs with
    | [] => e2
    | _ => Cedar.Data.Map.make (e2.kvs ++ e1.kvs)

instance : Field Entities := Field.fromInterField EntitiesProto.toEntities merge

end Entities

end Cedar.Spec
