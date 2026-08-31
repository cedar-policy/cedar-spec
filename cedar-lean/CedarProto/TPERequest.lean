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
import Cedar.TPE.Authorizer
import Cedar.TPE.Input
import Protobuf.Message
import Protobuf.Structure

-- Message Dependencies
import CedarProto.Entities
import CedarProto.PolicySet
import CedarProto.PartialInput
import CedarProto.Request
import CedarProto.Residual
import CedarProto.Schema

open Proto

namespace Cedar.Proto

structure BatchedAuthorizationRequest where
  policies : Spec.Policies
  schema : Validation.Schema
  request : Spec.Request
  entities : Spec.Entities
  iteration: UInt32
deriving Inhabited


namespace BatchedAuthorizationRequest

instance : Message BatchedAuthorizationRequest where
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

end BatchedAuthorizationRequest

structure PartialAuthorizationRequest where
  schema: Validation.Schema
  policies: Spec.Policies
  request: TPE.PartialRequest
  entities: TPE.PartialEntities
deriving Inhabited

namespace PartialAuthorizationRequest

instance : Message PartialAuthorizationRequest where
  parseField (t: Proto.Tag) := do
    match t.fieldNum with
      | 1 => parseFieldElement t schema (update schema)
      | 2 => parseFieldElement t policies (update policies)
      | 3 => parseFieldElement t request (update request)
      | 4 => parseFieldElement t entities (update entities)
      | _ => let _ <- t.wireType.skip; pure ignore

  merge x y := {
    schema := Field.merge x.schema y.schema
    policies := Field.merge x.policies y.policies
    request := Field.merge x.request y.request
    entities := Field.merge x.entities y.entities
  }

end PartialAuthorizationRequest

/-- Reauthorization of an arbitrary residual: evaluating it against concrete data. -/
structure ResidualReauthorizationRequest where
  residual: Spec.Residual
  request: Spec.Request
  entities: Spec.Entities
  expectedValue: Spec.Value
  expectsError: Bool
deriving Inhabited

namespace ResidualReauthorizationRequest

instance : Message ResidualReauthorizationRequest where
  parseField (t: Proto.Tag) := do
    match t.fieldNum with
      | 1 => parseFieldElement t residual (update residual)
      | 2 => parseFieldElement t request (update request)
      | 3 => parseFieldElement t entities (update entities)
      | 4 => parseFieldElement t expectedValue (update expectedValue)
      | 5 => parseFieldElement t expectsError (update expectsError)
      | _ => let _ <- t.wireType.skip; pure ignore

  merge x y := {
    residual := Field.merge x.residual y.residual
    request := Field.merge x.request y.request
    entities := Field.merge x.entities y.entities
    expectedValue := Field.merge x.expectedValue y.expectedValue
    expectsError := Field.merge x.expectsError y.expectsError
  }

end ResidualReauthorizationRequest
structure PartialEntityValidationRequest where
  entities: TPE.PartialEntities
deriving Inhabited

namespace PartialEntityValidationRequest

instance : Message PartialEntityValidationRequest where
  parseField (t: Proto.Tag) := do
    match t.fieldNum with
      | 1 => parseFieldElement t entities (update entities)
      | _ => let _ <- t.wireType.skip; pure ignore

  merge x y := {
    entities := Field.merge x.entities y.entities
  }

end PartialEntityValidationRequest

structure PartialRequestValidationRequest where
  request: TPE.PartialRequest
deriving Inhabited

namespace PartialRequestValidationRequest

instance : Message PartialRequestValidationRequest where
  parseField (t: Proto.Tag) := do
    match t.fieldNum with
      | 1 => parseFieldElement t request (update request)
      | _ => let _ <- t.wireType.skip; pure ignore

  merge x y := {
    request := Field.merge x.request y.request
  }

end PartialRequestValidationRequest

structure PartialRequestConsistencyRequest where
  request: Spec.Request
  partialRequest: TPE.PartialRequest
deriving Inhabited

namespace PartialRequestConsistencyRequest

instance : Message PartialRequestConsistencyRequest where
  parseField (t: Proto.Tag) := do
    match t.fieldNum with
      | 1 => parseFieldElement t request (update request)
      | 2 => parseFieldElement t partialRequest (update partialRequest)
      | _ => let _ <- t.wireType.skip; pure ignore

  merge x y := {
    request := Field.merge x.request y.request
    partialRequest := Field.merge x.partialRequest y.partialRequest
  }

end PartialRequestConsistencyRequest

structure PartialEntityConsistencyRequest where
  entities: Spec.Entities
  partialEntities: TPE.PartialEntities
deriving Inhabited

namespace PartialEntityConsistencyRequest

instance : Message PartialEntityConsistencyRequest where
  parseField (t: Proto.Tag) := do
    match t.fieldNum with
      | 1 => parseFieldElement t entities (update entities)
      | 2 => parseFieldElement t partialEntities (update partialEntities)
      | _ => let _ <- t.wireType.skip; pure ignore

  merge x y := {
    entities := Field.merge x.entities y.entities
    partialEntities := Field.merge x.partialEntities y.partialEntities
  }

end PartialEntityConsistencyRequest

end Cedar.Proto
