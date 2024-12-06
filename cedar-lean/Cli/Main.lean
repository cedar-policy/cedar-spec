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

import DiffTest.Main
import DiffTest.Parser

/-! This file provides a basic command line interface for authorization
    and validation. It uses the interface functions defined in `DiffTest`. -/

open DiffTest

def printUsage (err : String) : IO Unit :=
  IO.println s!"{err}\nUsage: Cli <command> <file>"

/--
  `req`: string containing JSON
-/
def evaluate (req : String) : ParseResult (Cedar.Spec.Result Cedar.Spec.Value) :=
  match Lean.Json.parse req with
  | .error e => .error s!"evaluate: failed to parse input: {e}"
  | .ok json => do
    let expr ← getJsonField json "expr" >>= jsonToExpr
    let request ← getJsonField json "request" >>= jsonToRequest
    let entities ← getJsonField json "entities" >>= jsonToEntities
    .ok (Cedar.Spec.evaluate expr request entities)

unsafe def main (args : List String) : IO Unit :=
  match args.length with
    | 2 => do
      let command := args.get! 0
      let filename := args.get! 1
      match command with
      | "authorize" =>
        let request ← IO.FS.readBinFile filename
        let response := isAuthorizedDRT request
        IO.println response
      | "validate" =>
        let request ← IO.FS.readBinFile filename
        let response := validateDRT request
        IO.println response
      | "evaluate" =>
        let request ← IO.FS.readFile filename
        let response := evaluate request
        IO.println s!"{repr response}"
      | "validateRequest" =>
        let request ← IO.FS.readFile filename
        let response := validateRequestDRT request
        IO.println response
      | "validateEntities" =>
        let request ← IO.FS.readFile filename
        let response := validateEntitiesDRT request
        IO.println response
      | _ => printUsage s!"Invalid command `{command}` (expected `authorize`, `validate`, `validateRequest`, `validateEntities`, or `evaluate`)"
    | n => printUsage s!"Incorrect number of arguments (expected 2, but got {n})"
