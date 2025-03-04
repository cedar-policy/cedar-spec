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
  `req`: binary protobuf for an `EvaluationRequest`

  returns a string containing JSON
-/
@[export evaluateDRT] unsafe def evaluateDRT (req : ByteArray) : String :=
  let result : ParseResult (Timed Bool) :=
    match (@Message.interpret? EvaluationRequest) req with
    | .error e => .error s!"evaluateDRT: failed to parse input: {e}"
    | .ok v => do
      let result := runAndTime (λ () => evaluate v.expr v.request v.entities)
      let { data, duration } := unsafeBaseIO result
      let data := match data, v.expected with
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
  let result : ParseResult (Timed EntityValidationResult) :=
    match (@Message.interpret? EntityValidationRequest) req with
    | .error e => .error s!"validateEntitiesDRT: failed to parse input: {e}"
    | .ok v => do
        let actionEntities := (v.schema.acts.mapOnValues actionSchemaEntryToEntityData)
        let entities := Cedar.Data.Map.make (v.entities.kvs ++ actionEntities.kvs)
        let schema := updateSchema v.schema actionEntities
        let result := runAndTime (λ () => Cedar.Validation.validateEntities schema entities )
        .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `RequestValidationRequest`

  returns a string containing JSON
-/
@[export validateRequestDRT] unsafe def validateRequestDRT (req : ByteArray) : String :=
  let result : ParseResult (Timed RequestValidationResult) :=
    match (@Message.interpret? RequestValidationRequest) req with
    | .error e => .error s!"validateRequestDRT: failed to parse input: {e}"
    | .ok v => do
        let result := runAndTime (λ () => Cedar.Validation.validateRequest v.schema v.request )
        .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

end DiffTest
