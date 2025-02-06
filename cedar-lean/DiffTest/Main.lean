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
import DiffTest.Util
import DiffTest.Parser
import CedarProto
import Protobuf

/-! This file defines the public interfaces for the Lean implementation.
    The input and output are stringified JSON objects. -/

namespace DiffTest

open Cedar.Spec
open Cedar.Validation
open Proto

structure Timed (α : Type) where
  data : α
  /-- Duration in nanoseconds -/
  duration : Nat
deriving Lean.ToJson

def runAndTime (f : Unit -> α) : BaseIO (Timed α) := do
  let start ← IO.monoNanosNow
  let result := f ()
  let stop ← IO.monoNanosNow
  .ok {
    data := result,
    duration := stop - start
  }

def runAndTimeIO (f : IO α) : IO (Timed α) := do
  let start ← IO.monoNanosNow
  let result ← f
  let stop ← IO.monoNanosNow
  .ok {
    data := result,
    duration := stop - start
  }

/--
  `req`: binary protobuf for an `AuthorizationRequest`

  returns a string containing JSON
-/
@[export isAuthorizedDRT] unsafe def isAuthorizedDRT (req: ByteArray) : String :=
    let result: ParseResult (Timed Response) :=
      match (@Message.interpret? AuthorizationRequest) req with
      | .error e =>
        .error s!"isAuthorizedDRT: failed to parse input: {e}"
      | .ok p =>
        let result := runAndTime (λ () => isAuthorized p.request p.entities p.policies)
        .ok (unsafeBaseIO result)
    toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `ValidationRequest`

  returns a string containing JSON
-/
@[export validateDRT] unsafe def validateDRT (req : ByteArray) : String :=
    let result: ParseResult (Timed ValidationResult) :=
      match (@Message.interpret? ValidationRequest) req with
      | .error e =>
        .error s!"validateDRT: failed to parse input: {e}"
      | .ok v =>
        let result := runAndTime (λ () => validate v.policies v.schema)
        .ok (unsafeBaseIO result)
    toString (Lean.toJson result)

/--
  `req`: string containing JSON

  returns a string containing JSON
-/
@[export evaluateDRT] unsafe def evaluateDRT (req : String) : String :=
  let result : ParseResult (Timed Bool) :=
    match Lean.Json.parse req with
    | .error e => .error s!"evaluateDRT: failed to parse input: {e}"
    | .ok json => do
      let expr ← getJsonField json "expr" >>= jsonToExpr
      let request ← getJsonField json "request" >>= jsonToRequest
      let entities ← getJsonField json "entities" >>= jsonToEntities
      let expected ← getJsonField json "expected" >>= jsonToOptionalValue
      let result := runAndTime (λ () => evaluate expr request entities)
      let { data, duration } := unsafeBaseIO result
      let data := match data, expected with
        | .error _, .none => true
        | .ok v₁, .some v₂ => v₁ == v₂
        | _, _ => false
      .ok { data, duration }
  toString (Lean.toJson result)

@[export partialAuthorizeDRT] unsafe def partialAuthorizeDRT (req : String) : String :=
  s!"partialAuthorizeDRT: not supported {req}"

@[export partialEvaluateDRT] unsafe def partialEvaluateDRT (req : String) : String :=
  s!"partialEvaluateDRT: not supported {req}"

/--
  `req`: string containing JSON

  returns a string containing JSON
-/
@[export validateEntitiesDRT] unsafe def validateEntitiesDRT (req : String) : String :=
  let result : ParseResult (Timed EntityValidationResult) :=
    match Lean.Json.parse req with
    | .error e => .error s!"validateEntitiesDRT: failed to parse input: {e}"
    | .ok json => do
        let schema ← getJsonField json "schema" >>= jsonToSchema
        let entities ← getJsonField json "entities" >>= jsonToEntities
        let actionEntities := (schema.acts.mapOnValues actionSchemaEntryToEntityData)
        let entities := Cedar.Data.Map.make (entities.kvs ++ actionEntities.kvs)
        let schema := updateSchema schema actionEntities
        let result := runAndTime (λ () => Cedar.Validation.typeCheckEntities schema entities )
        .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

/--
  `req`: string containing JSON

  returns a string containing JSON
-/
@[export validateRequestDRT] unsafe def validateRequestDRT (req : String) : String :=
  let result : ParseResult (Timed RequestValidationResult) :=
    match Lean.Json.parse req with
    | .error e => .error s!"validateRequestDRT: failed to parse input: {e}"
    | .ok json => do
        let schema ← getJsonField json "schema" >>= jsonToSchema
        let request ← getJsonField json "request" >>= jsonToRequest
        let result := runAndTime (λ () => Cedar.Validation.typeCheckRequest schema request )
        .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

end DiffTest
