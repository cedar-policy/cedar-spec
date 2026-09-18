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

module

public import Lean.Data.Json
public import Cedar.Spec.Request
public import Cedar.Frontend.Json.Value
public import Cedar.Frontend.Json.Entities

/-!
Pure-Lean JSON reader for Cedar `Spec.Request`, matching Cedar's on-the-wire
request JSON (`cedar-policy/src/ffi/is_authorized.rs`):
```
{ "principal": <EntityUidJson>,
  "action":    <EntityUidJson>,
  "resource":  <EntityUidJson>,
  "context":   { <name>: <value>, ... }
}
```
Each of principal/action/resource is an `EntityUidJson` (explicit `__entity`
escape or implicit `{ "type", "id" }`). `context` is a JSON object of
attribute name to value; a missing `context` defaults to the empty record.

This is frontend/ingestion code producing `Spec` values, reusable by any
pure-Lean tool (e.g. a future CLI), not just the FFI.
-/

namespace Cedar.Frontend.Json

open Cedar.Spec
open Cedar.Data

/-- Read a Cedar request JSON object into a `Spec.Request`. -/
public def jsonToRequest (j : Lean.Json) : Except String Request := do
  let principalJson ← j.getObjVal? "principal"
  let actionJson ← j.getObjVal? "action"
  let resourceJson ← j.getObjVal? "resource"
  let principal ← jsonToEntityUID principalJson
  let action ← jsonToEntityUID actionJson
  let resource ← jsonToEntityUID resourceJson
  let context ← match j.getObjVal? "context" with
    | .ok c => jsonToAttrMap c
    | .error _ => .ok Map.empty
  .ok { principal := principal, action := action, resource := resource, context := context }

/-- Parse a `Spec.Request` from a JSON string. -/
public def requestOfJsonStr (s : String) : Except String Request := do
  let j ← Lean.Json.parse s
  jsonToRequest j

end Cedar.Frontend.Json
