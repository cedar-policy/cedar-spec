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
import CedarProto.Expr
import CedarProto.Type

open Proto

namespace Cedar.Validation.Proto

-- Note: EntitySchemaEntry takes ancestors,
-- so we'll create an intermediate representation
-- once we gather all the entries, we will perform
-- the transform
structure ActionDecl where
  name : Spec.EntityUID
  descendants : Repeated Spec.EntityUID
  context : Proto.Map String (Qualified ProtoType)
  principalTypes : Repeated Spec.Proto.Name
  resourceTypes : Repeated Spec.Proto.Name
deriving Repr, Inhabited

namespace ActionDecl

instance : Message ActionDecl := {
  parseField (t : Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t name (update name)
    | 3 => parseFieldElement t descendants (update descendants)
    | 4 => parseFieldElement t context (update context)
    | 5 => parseFieldElement t principalTypes (update principalTypes)
    | 6 => parseFieldElement t resourceTypes (update resourceTypes)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    name           := Field.merge x.name           y.name
    descendants    := Field.merge x.descendants    y.descendants
    context        := Field.merge x.context        y.context
    principalTypes := Field.merge x.principalTypes y.principalTypes
    resourceTypes  := Field.merge x.resourceTypes  y.resourceTypes
  }
}

end ActionDecl

end Cedar.Validation.Proto
