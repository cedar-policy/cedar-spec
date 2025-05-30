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

import Lean.Data.Json.FromToJson

import Cedar.Spec
import Cedar.Validation
import CedarProto
import Protobuf

/-! This file defines the public interfaces for the Lean implementation.
    The input and output are stringified JSON objects. -/

namespace DiffTest

open Cedar.Spec
open Cedar.Validation
open Proto

/--
  `req`: binary protobuf for an `AuthorizationRequest`

  returns a string containing JSON
-/
@[export isAuthorized] unsafe def isAuthorizedFFI (req: ByteArray) : String :=
    let result: Except String Response :=
      match (@Message.interpret? AuthorizationRequest) req with
      | .error e =>
        .error s!"isAuthorizedDRT: failed to parse input: {e}"
      | .ok p =>
        let result := isAuthorized p.request p.entities p.policies
        .ok result
    toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `ValidationRequest`

  returns a string containing JSON
-/
@[export validate] unsafe def validateReqFFI (req : ByteArray) : String :=
    let result: Except String ValidationResult :=
      match (@Message.interpret? ValidationRequest) req with
      | .error e =>
        .error s!"validateDRT: failed to parse input: {e}"
      | .ok v =>
        let result := validate v.policies v.schema
        .ok result
    toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `LevelValidationRequest`

  returns a string containing JSON
-/
@[export levelValidate] unsafe def levelValidateFFI (req : ByteArray) : String :=
    let result: Except String ValidationResult :=
      match (@Message.interpret? LevelValidationRequest) req with
      | .error e =>
        .error s!"levelValidateDRT: failed to parse input: {e}"
      | .ok v =>
        let result := validateWithLevel v.policies v.schema v.level.level
        .ok result
    toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `EvaluationRequest`

  Parses req, evalutes expression, and prints it.
  returns a string encoding either .error err_msg if an error occurs or .ok () upon success
-/
@[export printEvaluation] unsafe def printEvaluationFFI (req: ByteArray) : String :=
  let result : Except String Unit :=
    match (@Message.interpret? EvaluationRequest) req with
    | .error e => .error s!"evaluate: failed to parse input: {e}"
    | .ok v =>
      match evaluate v.expr v.request v.entities with
      | .error e => .error s!"evaluate: error during evaluation: {reprStr e}"
      | .ok v =>
        match unsafeIO (println! "{reprStr v}") with
        | .error _ => .error s!"evaluate: error printing value"
        | .ok _ => .ok ()
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `EvaluationRequest`

  returns a string containing JSON, indicating whether the Lean evaluation
  result matches the `expected` in the request (where `expected = none`
  indicates the evaluation is expected to produce an error)
-/
@[export checkEvaluate] unsafe def checkEvaluateFFI (req : ByteArray) : String :=
  let result : Except String Bool := do
    match (@Message.interpret? EvaluationRequest) req with
    | .error e => .error s!"evaluate: failed to parse input: {e}"
    | .ok v =>
      match (evaluate v.expr v.request v.entities), v.expected with
      | .error _, .none => .ok true
      | .ok v₁, .some v₂ => .ok (v₁ == v₂)
      | _, _ => .ok false
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `EntityValidationRequest`

  returns a string containing JSON
-/
@[export validateEntities] unsafe def validateEntitiesFFI (req : ByteArray) : String :=
  let result : Except String EntityValidationResult :=
    match (@Message.interpret? EntityValidationRequest) req with
    | .error e => .error s!"validateEntitiesDRT: failed to parse input: {e}"
    | .ok v => do
        let actionEntities := (v.schema.acts.mapOnValues actionSchemaEntryToEntityData)
        let entities := Cedar.Data.Map.make (v.entities.kvs ++ actionEntities.kvs)
        let schema := updateSchema v.schema actionEntities
        let result := Cedar.Validation.validateEntities schema entities
        .ok result
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `RequestValidationRequest`

  returns a string containing JSON
-/
@[export validateRequest] unsafe def validateRequestFFI (req : ByteArray) : String :=
  let result : Except String RequestValidationResult :=
    match (@Message.interpret? RequestValidationRequest) req with
    | .error e => .error s!"validateRequestDRT: failed to parse input: {e}"
    | .ok v => do
        let result := Cedar.Validation.validateRequest v.schema v.request
        .ok result
  toString (Lean.toJson result)

end DiffTest
