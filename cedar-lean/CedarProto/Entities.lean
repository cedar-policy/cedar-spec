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
import Protobuf.Structure

-- Message Dependencies
import CedarProto.Entity

open Proto

namespace Cedar.Spec.Proto

-- Note that Cedar.Spec.Entities is defined as
-- abbrev Entities := Map EntityUID EntityData

-- Note that EntityData doesn't contain EntityUID, therefore
-- we need to parse an intermediate representation EntityProto
-- which contains that and transform it to the appropriate types.

structure Entities where
  entities : Repeated Entity
deriving Repr, Inhabited

instance : HAppend Entities Entities Entities where
  hAppend x y := { entities := x.entities ++ y.entities }
instance : HAppend Entities (Repeated Entity) Entities where
  hAppend x y := { entities := x.entities ++ y }

namespace Entities

instance : Message Entities := {
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t entities (update entities)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge := (· ++ ·)
}

@[inline]
def toEntities (e : Entities) : Spec.Entities :=
  Data.Map.make $ e.entities.toList.map λ { uid, attrs, ancestors, tags } => (
    uid,
    {
      attrs := Data.Map.make attrs.toList
      ancestors := Data.Set.make ancestors.toList
      tags := Data.Map.make tags.toList
    }
  )

end Entities

end Cedar.Spec.Proto

namespace Cedar.Spec

def Entities.merge (x y : Entities) : Entities :=
  -- avoid sorting if either is empty
  match x.kvs, y.kvs with
  | [], _ => y
  | _, [] => x
  | _, _  => Data.Map.make (x.kvs ++ y.kvs)

instance : Field Entities := Field.fromInterField Proto.Entities.toEntities Entities.merge

end Cedar.Spec
