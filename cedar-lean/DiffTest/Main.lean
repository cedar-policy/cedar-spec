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

@[export isAuthorizedDRT] def isAuthorizedDRT (req : String) : String :=
  let json := Lean.Json.parse req
  match json with
  | .error e => panic! s!"isAuthorizedDRT: failed to parse input: {e}"
  | .ok json =>
    let request := jsonToRequest (getJsonField json "request")
    let entities := jsonToEntities (getJsonField json "entities")
    let policies := jsonToPolicies (getJsonField json "policies")
    let response := isAuthorized request entities policies
    toString (Lean.toJson response)

@[export validateDRT] def validateDRT (req : String) : String :=
  let json := Lean.Json.parse req
  match json with
  | .error e => panic! s!"validateDRT: failed to parse input: {e}"
  | .ok json =>
    let policies := jsonToPolicies (getJsonField json "policies")
    let schema := jsonToSchema (getJsonField json "schema")
    let response := validate policies schema
    toString (Lean.toJson response)

def test : IO Unit := do
  let input ← IO.FS.readFile "DiffTest/example.json"
  IO.println (isAuthorizedDRT input)

-- result should be "allow" due to policy0
#eval test

end DiffTest
