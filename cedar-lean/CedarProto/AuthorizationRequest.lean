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
import CedarProto.Request
import CedarProto.PolicySet
import CedarProto.Entities

open Proto

namespace Cedar.Spec
structure AuthorizationRequest where
  request : Request
  entities : Entities
  policies : Policies
deriving Inhabited, DecidableEq, Repr

namespace AuthorizationRequest

instance : Message AuthorizationRequest := {
  parseField (t : Proto.Tag) := do match t.fieldNum with
    | 1 => parseFieldElement t request (update request)
    | 2 => parseFieldElement t policies (update policies)
    | 3 => parseFieldElement t entities (update entities)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    request :=  Field.merge x.request  y.request
    entities := Field.merge x.entities y.entities
    policies := Field.merge x.policies y.policies
  }
}

end AuthorizationRequest

end Cedar.Spec
