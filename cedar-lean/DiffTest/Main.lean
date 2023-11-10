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
import DiffTest.Parser

/-! This file defines the public interfaces for the Lean implementation.
    The input and output are stringified JSON objects. -/

namespace DiffTest

open Cedar.Spec
open Cedar.Data

@[export isAuthorizedDRT] def isAuthorizedDRT (req : String) : String :=
  let json := Lean.Json.parse req
  let request := jsonToRequest json
  let entities := jsonToEntities json
  let policies := jsonToPolicies json
  let json := Lean.toJson (isAuthorized request entities policies)
  toString json

end DiffTest
