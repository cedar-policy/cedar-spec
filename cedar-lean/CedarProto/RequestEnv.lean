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
import Cedar.Validation
import Protobuf.Message
import Protobuf.Structure

-- Message Dependencies
import CedarProto.Expr
import CedarProto.EntityUID
import CedarProto.Type

open Proto

namespace Cedar.Validation.Proto

structure RequestEnv where
  principal : Spec.EntityType
  action : Spec.EntityUID
  resource : Spec.EntityType
deriving Inhabited

namespace RequestEnv

instance : Message RequestEnv where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t principal (update principal)
    | 2 => parseFieldElement t action (update action)
    | 3 => parseFieldElement t resource (update resource)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    principal := Field.merge x.principal y.principal
    action := Field.merge x.action y.action
    resource := Field.merge x.resource y.resource
  }

end RequestEnv

end Cedar.Validation.Proto
