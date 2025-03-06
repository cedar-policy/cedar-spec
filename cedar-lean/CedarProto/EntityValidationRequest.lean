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
import CedarProto.Schema
import CedarProto.Entities


open Proto

namespace Cedar.Validation.Proto

structure EntityValidationRequest where
  schema : Validation.Schema
  entities : Cedar.Spec.Entities
deriving Repr, Inhabited

namespace EntityValidationRequest

instance : Message EntityValidationRequest where
  parseField (t : Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t schema (update schema)
    | 2 => parseFieldElement t entities (update entities)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    schema   := Field.merge x.schema   y.schema
    entities := Field.merge x.entities y.entities
  }

end EntityValidationRequest

end Cedar.Validation.Proto
