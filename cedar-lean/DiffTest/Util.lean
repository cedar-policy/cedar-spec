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

import Lean.Data.Json.Parser
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson
import Lean.Data.AssocList
import Lean.Data.RBMap

import Cedar.Data

/-! Utilities for parsing the JSON representation of serialized Rust datatypes. -/

namespace DiffTest

open Cedar.Data
open Lean

abbrev ParseError := String
abbrev ParseResult (α) := Except ParseError α

def getJsonField (json : Json) (field : String) : ParseResult Json :=
  match json.getObjVal? field with
  | .ok v => .ok v
  | .error e => .error s!"getJsonField {field}: {e}\n{json.pretty}"

def jsonToString (json : Json) : ParseResult String :=
  match json.getStr? with
  | .ok s => .ok s
  | .error e => .error s!"jsonToString: {e}\n{json.pretty}"

def jsonToArray (json : Json) : ParseResult (Array Json) :=
  match json.getArr? with
  | .ok a => .ok a
  | .error e => .error s!"jsonToArray: {e}\n{json.pretty}"

def jsonToTuple (json : Json) : ParseResult (Json × Json) := do
  let kv ← jsonToArray json
  if kv.size == 2 then .ok (kv[0]!, kv[1]!)
  else .error s!"jsonToTuple: expected exactly two elements\n{json.pretty}"

def jsonArrayToKVList (json : Json) : ParseResult (List (Json × Json)) := do
  let arr ← jsonToArray json
  List.mapM jsonToTuple arr.toList

def jsonObjToKVList (json : Json) : ParseResult (List (String × Json)) :=
  match json.getObj? with
  | .ok kvs => .ok (kvs.fold (λ acc k v => (k,v) :: acc) [])
  | .error e => .error s!"jsonToKVList: {e}\n{json.pretty}"

def jsonToBool (json : Json) : ParseResult Bool :=
  match json.getBool? with
  | .ok b => .ok b
  | .error e => .error s!"jsonToBool: {e}\n{json.pretty}"

def jsonToNum (json : Json) : ParseResult JsonNumber :=
  match json.getNum? with
  | .ok n => .ok n
  | .error e => .error s!"jsonToNum: {e}\n{json.pretty}"

def jsonToInt64 (json : Json) : ParseResult Cedar.Data.Int64 := do
  let num ← jsonToNum json
  match num.exponent with
  | 0 =>
    match Int64.mk? num.mantissa with
    | .some i64 => .ok i64
    | .none => .error s!"jsonToInt64: not a signed 64-bit integer {num.mantissa}"
  | n => .error s!"jsonToInt64: number has exponent {n}"

def jsonToChar (json: Json) : ParseResult Char :=
  match json.getStr? with
  | .ok s => match s.data with
    | [c] => .ok c
    | _ => .error s!"jsonToChar: Expected single character"
  | .error e => .error s!"jsonToChar: {e}\n{json.pretty}"

def getSingleElement (kvs : RBNode String (λ _ => Json)) : String × Json :=
  kvs.fold (init := ("",Json.null)) (λ _ k v => (k,v))

/-
Unpack the default Serde serialization of a Rust "enum" value into a tuple:
(variant tag, body).

If the Rust enum constructor has no fields, Serde just outputs the tag as a
string. If the constructor has at least one field, Serde generates a JSON
object with a single field, named after the tag, whose value is a JSON
object containing the original fields. unpackJsonSum accepts both formats,
and in the first case, it returns jsonEmptyObject as the body for
consistency.
-/
def unpackJsonSum (json : Json) : ParseResult (String × Json) := match json with
  | .str tag => .ok (tag, .obj ∅)
  | .obj kvs =>
      if kvs.size == 1 then .ok (getSingleElement kvs)
      else .error s!"unpackJsonSum: expected exactly one key, got either zero or multiple\n{json.pretty}"
  | _ => .error s!"unpackJsonSum: expected an object or a string\n{json.pretty}"

end DiffTest
