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

/- Pure-Lean JSON readers for Cedar `Spec` values, entities, and requests,
   matching Cedar's on-the-wire JSON formats. Frontend/ingestion code, reusable
   by any pure-Lean tool (e.g. a future CLI), not just the FFI. -/

public import Cedar.Frontend.Json.Value
public import Cedar.Frontend.Json.Entities
public import Cedar.Frontend.Json.Request
