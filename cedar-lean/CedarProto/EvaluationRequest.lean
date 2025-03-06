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
import CedarProto.Expr

open Proto

namespace Cedar.Spec
structure EvaluationRequest where
  expr : Expr
  request : Request
  entities : Entities
  expected : Option Value
deriving Inhabited, DecidableEq, Repr

namespace EvaluationRequest

instance : Message EvaluationRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t expr (update expr)
    | 2 => parseFieldElement t request (update request)
    | 3 => parseFieldElement t entities (update entities)
    | 4 => parseFieldElement t expected (update expected)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    expr     := Field.merge x.expr     y.expr
    request  := Field.merge x.request  y.request
    entities := Field.merge x.entities y.entities
    expected := Field.merge x.expected y.expected
  }

end EvaluationRequest

end Cedar.Spec
