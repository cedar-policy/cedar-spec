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
import CedarProto.Entities
import CedarProto.PolicySet
import CedarProto.Request
import CedarProto.Schema

open Proto

namespace Cedar.Proto

structure BatchedEvaluationRequest where
  policies : Spec.Policies
  schema : Validation.Schema
  request : Spec.Request
  entities : Spec.Entities
  iteration: UInt32
deriving Inhabited

namespace BatchedEvaluationRequest

instance : Message BatchedEvaluationRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t policies (update policies)
    | 2 => parseFieldElement t schema (update schema)
    | 3 => parseFieldElement t request (update request)
    | 4 => parseFieldElement t entities (update entities)
    | 5 => parseFieldElement t iteration (update iteration)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    policies := Field.merge x.policies y.policies
    schema := Field.merge x.schema y.schema
    request := Field.merge x.request y.request
    entities := Field.merge x.entities y.entities
    iteration := Field.merge x.iteration y.iteration
  }

end BatchedEvaluationRequest

end Cedar.Proto
