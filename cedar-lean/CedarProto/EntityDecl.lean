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
import CedarProto.Name
import CedarProto.Type

open Proto

namespace Cedar.Validation.Proto

-- Note: EntitySchemaEntry takes ancestors, so we'll create this intermediate
-- representation. Once we gather all the entries, we will perform the transform.
structure EntityDecl where
  name : Spec.Proto.Name
  /-- All (transitive) descendants. Assumes TC is computed before encoding into protobuf. -/
  descendants : Repeated Spec.Proto.Name
  attrs : Proto.Map String (Qualified ProtoType)
  tags : Option ProtoType
  enums : Repeated String
deriving Repr, Inhabited

namespace EntityDecl

instance : Message EntityDecl := {
  parseField (t : Tag) := do match t.fieldNum with
    | 1 => parseFieldElement t name (update name)
    | 2 => parseFieldElement t descendants (update descendants)
    | 3 => parseFieldElement t attrs (update attrs)
    | 5 => parseFieldElement t tags (update tags)
    | 6 => parseFieldElement t enums (update enums)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    name        := Field.merge x.name        y.name
    descendants := Field.merge x.descendants y.descendants
    attrs       := Field.merge x.attrs       y.attrs
    tags        := Field.merge x.tags        y.tags
    enums       := Field.merge x.enums       y.enums
  }
}

end EntityDecl

end Cedar.Validation.Proto
