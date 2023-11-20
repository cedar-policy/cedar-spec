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
import DiffTest.Parser


/-! This file defines the public interfaces for the Lean implementation.
    The input and output are stringified JSON objects. -/

open Cedar.Spec
open Cedar.Validation
open Cedar.Data
open DiffTest


def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def readFile (filename : String) : IO String :=
  IO.FS.readFile filename

def main (args : List String) : IO Unit :=
  match args.length with
    | 1 => do
      let filename := args.head!
      let req ← readFile filename
      let json := Lean.Json.parse req
      match json with
      | .error e => panic! s!"isAuthorizedDRT: failed to parse input: {e}"
      | .ok json =>
        -- let request := jsonToRequest (getJsonField json "request")
        -- let entities := jsonToEntities (getJsonField json "entities")
        -- let policies := jsonToPolicies (getJsonField json "policies")
        -- let response := isAuthorized request entities policies
        -- let json := Lean.toJson response
        -- IO.println (toString json)
        let policies := jsonToPolicies (getJsonField json "policies")
        let schema := jsonToSchema (getJsonField json "schema")
        let response := validate policies schema
        let json := Lean.toJson response
        IO.println (toString json)
    | _ => IO.println s!"Incorrect number of arguments"
