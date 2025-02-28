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

open Proto

namespace Cedar.Spec.EntityUID

instance : Message EntityUID := {
  parseField (t : Proto.Tag) := do match t.fieldNum with
    | 1 => parseFieldElement t ty (update ty)
    | 2 => parseFieldElement t eid (update eid)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    ty  := Field.merge x.ty  y.ty
    eid := Field.merge x.eid y.eid
  }
}

end Cedar.Spec.EntityUID
