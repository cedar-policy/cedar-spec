/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

/-! This file defines the public interfaces for the Lean implementation.
    The input and output are stringified JSON objects. -/

namespace DiffTest

open Cedar.Spec
open Cedar.Validation

structure Timed (α : Type) where
  data : α
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

@[export isAuthorizedDRT] unsafe def isAuthorizedDRT (req : String) : String :=
  let result : ParseResult (Timed Response) :=
    match Lean.Json.parse req with
    | .error e => .error s!"isAuthorizedDRT: failed to parse input: {e}"
    | .ok json => do
      let request ← getJsonField json "request" >>= jsonToRequest
      let entities ← getJsonField json "entities" >>= jsonToEntities
      let policies ← getJsonField json "policies" >>= jsonToPolicies
      let result := runAndTime (λ () => isAuthorized request entities policies)
      .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

@[export validateDRT] unsafe def validateDRT (req : String) : String :=
  let result : ParseResult (Timed ValidationResult) :=
    match Lean.Json.parse req with
    | .error e => .error s!"validateDRT: failed to parse input: {e}"
    | .ok json => do
      let policies ← getJsonField json "policies" >>= jsonToPolicies
      let schema ← getJsonField json "schema" >>= jsonToSchema
      let result := runAndTime (λ () => validate policies schema)
      .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

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

-- variant of `evaluateDRT` that returns the result of evaluation; used in the Cli
def evaluate (req : String) : ParseResult (Result Value) :=
  match Lean.Json.parse req with
  | .error e => .error s!"evaluate: failed to parse input: {e}"
  | .ok json => do
    let expr ← getJsonField json "expr" >>= jsonToExpr
    let request ← getJsonField json "request" >>= jsonToRequest
    let entities ← getJsonField json "entities" >>= jsonToEntities
    .ok (Cedar.Spec.evaluate expr request entities)

end DiffTest
