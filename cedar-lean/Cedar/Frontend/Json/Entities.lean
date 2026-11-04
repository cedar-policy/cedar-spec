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
public import Cedar.Spec.Entities
public import Cedar.Frontend.Json.Value

/-!
Pure-Lean JSON reader for Cedar `Spec.Entities`, matching Cedar's on-the-wire
entities JSON (`cedar-policy-core/src/entities/json/entities.rs`, `EntityJson`).

The entities file is a JSON array of entity objects, each of the form:
```
{ "uid": <EntityUidJson>,
  "attrs": { <name>: <value>, ... },
  "parents": [ <EntityUidJson>, ... ],
  "tags": { <name>: <value>, ... }   -- optional, default {}
}
```
An `EntityUidJson` is either the explicit escape `{ "__entity": { "type", "id" } }`
or the implicit form `{ "type", "id" }`. Both map to a `Spec.EntityUID`.

This is frontend/ingestion code producing `Spec` values, reusable by any
pure-Lean tool (e.g. a future CLI), not just the FFI.
-/

namespace Cedar.Frontend.Json

open Cedar.Spec
open Cedar.Data

/-- Read a Cedar `EntityUidJson` into a `Spec.EntityUID`. Accepts both the
    explicit `{ "__entity": { "type", "id" } }` escape and the implicit
    `{ "type", "id" }` form. -/
public def jsonToEntityUID (j : Lean.Json) : Except String EntityUID :=
  -- Try the explicit escape first: a single-key object with key `__entity`.
  match j.getObjVal? "__entity" with
  | .ok inner => readTypeId inner
  | .error _  => readTypeId j
where
  readTypeId (o : Lean.Json) : Except String EntityUID := do
    let tyJson ← o.getObjVal? "type"
    let idJson ← o.getObjVal? "id"
    let ty ← tyJson.getStr?
    let id ← idJson.getStr?
    .ok (mkEntityUID ty id)

/-- Read the `attrs`/`tags` object (a JSON object mapping names to values) into a
    `Map Attr Value`. A missing key is treated as the empty map by the caller. -/
public def jsonToAttrMap (j : Lean.Json) : Except String (Map String Value) := do
  let kvs ← j.getObj?
  let pairs ← kvs.toList.mapM (fun (k, v) => do
    let v' ← jsonToValue v
    .ok (k, v'))
  .ok (Map.make pairs)

/-- Read one entity object into an `EntityUID × EntityData` pair. -/
public def jsonToEntity (j : Lean.Json) : Except String (EntityUID × EntityData) := do
  let uidJson ← j.getObjVal? "uid"
  let uid ← jsonToEntityUID uidJson
  -- attrs: optional, default empty
  let attrs ← match j.getObjVal? "attrs" with
    | .ok a => jsonToAttrMap a
    | .error _ => .ok Map.empty
  -- parents: optional, default empty
  let ancestors ← match j.getObjVal? "parents" with
    | .ok p => do
      let arr ← p.getArr?
      let uids ← arr.toList.mapM jsonToEntityUID
      .ok (Set.make uids)
    | .error _ => .ok Set.empty
  -- tags: optional, default empty
  let tags ← match j.getObjVal? "tags" with
    | .ok t => jsonToAttrMap t
    | .error _ => .ok Map.empty
  .ok (uid, { attrs := attrs, ancestors := ancestors, tags := tags })

/-- Read a Cedar entities JSON array into `Spec.Entities`. -/
public def jsonToEntities (j : Lean.Json) : Except String Entities := do
  let arr ← j.getArr?
  let pairs ← arr.toList.mapM jsonToEntity
  .ok (Map.make pairs)

/-- Parse `Spec.Entities` from a JSON string. -/
public def entitiesOfJsonStr (s : String) : Except String Entities := do
  let j ← Lean.Json.parse s
  jsonToEntities j

end Cedar.Frontend.Json
