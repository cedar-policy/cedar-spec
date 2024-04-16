/-
 Copyright Cedar Contributors. All Rights Reserved.

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

def readFile (filename : String) : IO String :=
  IO.FS.readFile filename

def printUsage (err : String) : IO Unit :=
  IO.println s!"{err}\nUsage: Cli <command> <file>"

unsafe def main (args : List String) : IO Unit :=
  match args.length with
    | 2 => do
      let command := args.get! 0
      let filename := args.get! 1
      let request ← readFile filename
      match command with
      | "authorize" =>
        let response := isAuthorizedDRT request
        IO.println response
      | "validate" =>
        let response := validateDRT request
        IO.println response
      | "evaluate" =>
        let response := evaluate request
        IO.println s!"{repr response}"
      | _ => printUsage s!"Invalid command `{command}` (expected `authorize`, `validate` or `evaluate`)"
    | n => printUsage s!"Incorrect number of arguments (expected 2, but got {n})"
