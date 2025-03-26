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
import CedarProto.PolicySet


open Proto

namespace Cedar.Validation.Proto

deriving instance DecidableEq for ActionSchemaEntry
deriving instance DecidableEq for ActionSchema
deriving instance DecidableEq for EntitySchema
deriving instance DecidableEq for Validation.Schema

structure ValidationRequest where
  schema : Validation.Schema
  policies : Spec.Policies
deriving Inhabited, DecidableEq, Repr

namespace ValidationRequest

instance : Message ValidationRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t schema (update schema)
    | 2 => parseFieldElement t policies (update policies)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    schema   := Field.merge x.schema   y.schema
    policies := Field.merge x.policies y.policies
  }

end ValidationRequest

end Cedar.Validation.Proto
