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
import CedarProto.Entities

open Proto

namespace Cedar.Spec

/--
  Like `AuthorizationRequest`, but the policies arrive as raw Cedar source text
  (`policyText`) rather than a pre-parsed `Policies`. Lean parses the text with
  its own policy parser before authorizing (see `CedarFFI.isAuthorizedPFFI`),
  so this exercises the parse -> authorize path end to end.

  Field numbers match `AuthorizationRequestFromPolicyText` in `Messages.proto`:
  request = 1, policy_text = 2, entities = 3.
-/
structure AuthorizationRequestP where
  request : Request
  policyText : String
  entities : Entities
deriving Inhabited, DecidableEq, Repr

namespace AuthorizationRequestP

instance : Message AuthorizationRequestP := {
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t request (update request)
    | 2 => parseFieldElement t policyText (update policyText)
    | 3 => parseFieldElement t entities (update entities)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    request :=    Field.merge x.request    y.request
    policyText := Field.merge x.policyText y.policyText
    entities :=   Field.merge x.entities   y.entities
  }
}

end AuthorizationRequestP

end Cedar.Spec
