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

structure Timed (α : Type) where
  data : α
  /-- Duration in nanoseconds -/
  duration : Nat
deriving Lean.ToJson

def runAndTime (f : Unit → α) : BaseIO (Timed α) := do
  let start ← IO.monoNanosNow
  let result := f ()
  let stop ← IO.monoNanosNow
  return {
    data := result,
    duration := stop - start
  }

def runAndTimeIO (f : IO α) : IO (Timed α) := do
  let start ← IO.monoNanosNow
  let result ← f
  let stop ← IO.monoNanosNow
  return {
    data := result,
    duration := stop - start
  }

/--
  `req`: binary protobuf for an `AuthorizationRequest`

  returns a string containing JSON
-/
@[export isAuthorizedDRT] unsafe def isAuthorizedDRT (req: ByteArray) : String :=
    let result: Except String (Timed Response) :=
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
    let result: Except String (Timed ValidationResult) :=
      match (@Message.interpret? ValidationRequest) req with
      | .error e =>
        .error s!"validateDRT: failed to parse input: {e}"
      | .ok v =>
        let result := runAndTime (λ () => validate v.policies v.schema)
        .ok (unsafeBaseIO result)
    toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `LevelValidationRequest`

  returns a string containing JSON
-/
@[export levelValidateDRT] unsafe def levelValidateDRT (req : ByteArray) : String :=
    let result: Except String (Timed ValidationResult) :=
      match (@Message.interpret? LevelValidationRequest) req with
      | .error e =>
        .error s!"levelValidateDRT: failed to parse input: {e}"
      | .ok v =>
        let result := runAndTime (λ () => validateWithLevel v.policies v.schema v.level.level)
        .ok (unsafeBaseIO result)
    toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `EvaluationRequest`

  returns the evaluation result itself (which may be `.error`) along with the
  `expected` in the request (which may be `none`, indicating the evaluation is
  expected to produce an error, or `expected` was not provided in the Protobuf
  input)
-/
@[export evaluate] unsafe def evaluateReq (req : ByteArray) : Except String (Timed (Result Value) × Option Value) :=
  match (@Message.interpret? EvaluationRequest) req with
    | .error e => .error s!"evaluateReq: failed to parse input: {e}"
    | .ok v => do
      let result := unsafeBaseIO $ runAndTime λ () => evaluate v.expr v.request v.entities
      .ok (result, v.expected)

/--
  `req`: binary protobuf for an `EvaluationRequest`

  returns a string containing JSON, indicating whether the Lean evaluation
  result matches the `expected` in the request (where `expected = none`
  indicates the evaluation is expected to produce an error)
-/
@[export evaluateDRT] unsafe def evaluateDRT (req : ByteArray) : String :=
  let result : Except String (Timed Bool) := do
    let ({ data, duration }, expected) ← evaluateReq req
      let data := match data, expected with
        | .error _, .none => true
        | .ok v₁, .some v₂ => v₁ == v₂
        | _, _ => false
      .ok { data, duration }
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `EntityValidationRequest`

  returns a string containing JSON
-/
@[export validateEntitiesDRT] unsafe def validateEntitiesDRT (req : ByteArray) : String :=
  let result : Except String (Timed EntityValidationResult) :=
    match (@Message.interpret? EntityValidationRequest) req with
    | .error e => .error s!"validateEntitiesDRT: failed to parse input: {e}"
    | .ok v => do
        let actionEntities := (v.schema.acts.mapOnValues actionSchemaEntryToEntityData)
        let entities := Cedar.Data.Map.make (v.entities.kvs ++ actionEntities.kvs)
        let result := runAndTime (λ () => Cedar.Validation.validateEntities v.schema entities )
        .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `RequestValidationRequest`

  returns a string containing JSON
-/
@[export validateRequestDRT] unsafe def validateRequestDRT (req : ByteArray) : String :=
  let result : Except String (Timed RequestValidationResult) :=
    match (@Message.interpret? RequestValidationRequest) req with
    | .error e => .error s!"validateRequestDRT: failed to parse input: {e}"
    | .ok v => do
        let result := runAndTime (λ () => Cedar.Validation.validateRequest v.schema v.request )
        .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

end DiffTest
