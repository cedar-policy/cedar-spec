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
public import Cedar.Spec.Value
public import Cedar.Spec.Ext

/-!
Pure-Lean JSON reader for Cedar `Spec.Value`s, matching Cedar's schema-free
on-the-wire JSON (`cedar-policy-core/src/entities/json/value.rs`,
`CedarValueJson`).

This is frontend/ingestion code: it produces `Spec` values but is not part of
the pure semantic core (`Cedar/Spec`). It is written on top of Lean's
`Lean.Data.Json` and is reusable by any pure-Lean tool (e.g. a future CLI), not
just the FFI.

Mapping (schema-free):
- JSON bool   -> `Value.prim (.bool ..)`
- JSON int    -> `Value.prim (.int ..)`  (bounds-checked via `Int64.ofInt?`)
- JSON string -> `Value.prim (.string ..)`
- JSON array  -> `Value.set`
- JSON object -> `Value.record`, EXCEPT single-key escape objects:
  - `{ "__entity": { "type": <name>, "id": <string> } }` -> entity reference
  - `{ "__extn": { "fn": <name>, "arg": <value> } }` (or `"args": [..]`) -> extension value
  - `{ "__expr": .. }` -> error (reserved, removed in Cedar 3.0)
  A single-key object whose key looks like an escape but whose inner shape does
  not match falls through to a plain record, matching serde's `untagged`
  behavior on the Rust side.
-/

namespace Cedar.Frontend.Json

open Cedar.Spec
open Cedar.Data

/-- Parse a normalized entity type name (e.g. `"A::B::C"`) into a `Spec.Name`.
    The last `::`-separated component is the id; the earlier components are the
    path. An empty string yields an empty id with empty path. -/
public def parseTypeName (s : String) : Name :=
  let parts := s.splitOn "::"
  match parts.reverse with
  | [] => { id := "", path := [] }
  | id :: revPath => { id := id, path := revPath.reverse }

/-- Build an `EntityUID` from a `type` string and an `id` string. -/
public def mkEntityUID (ty : String) (id : String) : EntityUID :=
  { ty := parseTypeName ty, eid := id }

/-- The extension value constructors recognized in a `__extn` escape, keyed by
    their Cedar function name. Each takes the (single, string) argument. -/
public def extConstructor (fn : String) (arg : String) : Except String Ext :=
  match fn with
  | "decimal" => match Ext.Decimal.decimal arg with
    | some d => .ok (.decimal d)
    | none => .error s!"invalid decimal extension value: {arg}"
  | "ip" => match Ext.IPAddr.ip arg with
    | some ip => .ok (.ipaddr ip)
    | none => .error s!"invalid ip extension value: {arg}"
  | "datetime" => match Ext.Datetime.datetime arg with
    | some dt => .ok (.datetime dt)
    | none => .error s!"invalid datetime extension value: {arg}"
  | "duration" => match Ext.Datetime.duration arg with
    | some dur => .ok (.duration dur)
    | none => .error s!"invalid duration extension value: {arg}"
  | _ => .error s!"unknown extension constructor: {fn}"

/-- Convenience: the key/value list of a JSON object, or `none` if `j` is not an
    object. -/
private def objEntries? (j : Lean.Json) : Option (List (String × Lean.Json)) :=
  match j.getObj? with
  | .ok kvs => some kvs.toList
  | .error _ => none

mutual

/-- Read a `Spec.Value` from a `Lean.Json` value (schema-free). -/
public partial def jsonToValue (j : Lean.Json) : Except String Value := do
  match j with
  | .null => .error "null is not a valid Cedar value"
  | .bool b => .ok (.prim (.bool b))
  | .str s => .ok (.prim (.string s))
  | .num _ =>
    -- Cedar longs are 64-bit signed integers; reject non-integers and out-of-range.
    let i ← j.getInt?
    match Int64.ofInt? i with
    | some i64 => .ok (.prim (.int i64))
    | none => .error s!"integer out of Int64 range: {i}"
  | .arr elts => do
    let vs ← elts.toList.mapM jsonToValue
    .ok (.set (Set.make vs))
  | .obj _ => jsonObjToValue j

/-- Read a `Spec.Value` from a JSON object, handling the `__entity` / `__extn` /
    `__expr` escapes before falling back to a plain record. -/
public partial def jsonObjToValue (j : Lean.Json) : Except String Value := do
  let entries := (objEntries? j).getD []
  match entries with
  | [(k, inner)] =>
    -- Single-key object: candidate escape. Only treated as an escape when the
    -- inner shape matches; otherwise falls through to a plain record.
    match k with
    | "__entity" =>
      match escapeEntity? inner with
      | some uid => .ok (.prim (.entityUID uid))
      | none => jsonRecord entries
    | "__extn" =>
      match escapeExtn inner with
      | some res => (·.map Value.ext) res
      | none => jsonRecord entries
    | "__expr" =>
      .error "the `__expr` escape was removed in Cedar 3.0 and is no longer supported"
    | _ => jsonRecord entries
  | _ => jsonRecord entries

/-- Build a `Value.record` from JSON object entries, reading each value. -/
public partial def jsonRecord (entries : List (String × Lean.Json)) : Except String Value := do
  let kvs ← entries.mapM (fun (k, v) => do let v' ← jsonToValue v; .ok (k, v'))
  .ok (.record (Map.make kvs))

/-- Try to read a `{ "type": .., "id": .. }` inner object as an `EntityUID`.
    Returns `none` (fall through to record) if the shape does not match. -/
public partial def escapeEntity? (inner : Lean.Json) : Option EntityUID :=
  match inner.getObjVal? "type", inner.getObjVal? "id" with
  | .ok tyJson, .ok idJson =>
    match tyJson.getStr?, idJson.getStr? with
    | .ok ty, .ok id => some (mkEntityUID ty id)
    | _, _ => none
  | _, _ => none

/-- Read a `{ "fn": .., "arg"/"args": .. }` inner object as an extension value.
    Returns `none` (fall through to record) only when the object is not shaped
    like an extn escape at all; a shaped-but-invalid escape yields `some (.error ..)`. -/
public partial def escapeExtn (inner : Lean.Json) : Option (Except String Ext) :=
  match inner.getObjVal? "fn" with
  | .ok fnJson =>
    match fnJson.getStr? with
    | .ok fn =>
      match inner.getObjVal? "arg" with
      | .ok argJson =>
        -- Single-argument form. The value constructors all take a string arg.
        match argJson.getStr? with
        | .ok arg => some (extConstructor fn arg)
        | .error _ => some (.error s!"extension constructor `{fn}` expects a string argument")
      | .error _ =>
        match inner.getObjVal? "args" with
        | .ok argsJson =>
          match argsJson.getArr? with
          | .ok #[argJson] =>
            match argJson.getStr? with
            | .ok arg => some (extConstructor fn arg)
            | .error _ => some (.error s!"extension constructor `{fn}` expects a string argument")
          | .ok _ => some (.error s!"extension constructor `{fn}` expects exactly one argument")
          | .error _ => none
        | .error _ => none
    | .error _ => none
  | .error _ => none

end

/-- Parse a `Spec.Value` from a JSON string. -/
public def valueOfJsonStr (s : String) : Except String Value := do
  let j ← Lean.Json.parse s
  jsonToValue j

end Cedar.Frontend.Json
