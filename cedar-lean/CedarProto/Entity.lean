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
import CedarProto.EntityUID
import CedarProto.Value

open Proto

namespace Cedar.Spec.Proto

-- Note that Cedar.Spec.EntityData is defined as
-- structure EntityData where
--   attrs : Map Attr Value
--   ancestors : Set EntityUID
--   tags : Map Tag Value

-- NOTE: EntityData is defined in Cedar.Spec.Entities
-- however it doesn't have the uid field which is
-- needed when crafting Entities, therefore
-- we store within an intermediate representation instead

structure Entity where
  uid : EntityUID
  attrs : Proto.Map String Value
  ancestors: Repeated EntityUID
  tags : Proto.Map String Value
deriving Repr, Inhabited

namespace Entity

instance : Message Entity := {
  parseField (t : Proto.Tag) := do match t.fieldNum with
    | 1 => parseFieldElement t uid (update uid)
    | 2 => parseFieldElement t attrs (update attrs)
    | 3 => parseFieldElement t ancestors (update ancestors)
    | 4 => parseFieldElement t tags (update tags)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    uid       := Field.merge x.uid       y.uid
    attrs     := Field.merge x.attrs     y.attrs
    ancestors := Field.merge x.ancestors y.ancestors
    tags      := Field.merge x.tags      y.tags
  }
}

end Entity

end Cedar.Spec.Proto
