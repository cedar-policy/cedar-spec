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

def getJsonField (json : Json) (field : String) : Json :=
  match json.getObjVal? field with
  | .ok v => v
  | .error e => panic! s!"getJsonField {field}: {e}\n" ++ json.pretty

def jsonToString (json : Json) : String :=
  match json.getStr? with
  | .ok s => s
  | .error e => panic! s!"jsonToString: {e}\n" ++ json.pretty

def jsonToArray (json : Json) : Array Json :=
  match json.getArr? with
  | .ok a => a
  | .error e => panic! s!"jsonToArray: {e}\n" ++ json.pretty

def jsonToTuple (json : Json) : (Json × Json) :=
  let kv := jsonToArray json
  if kv.size == 2 then (kv[0]!, kv[1]!)
  else panic! "jsonToTuple: expected exactly two elements\n" ++ json.pretty

def jsonArrayToKVList (json : Json) : List (Json × Json) :=
  let arr := jsonToArray json
  List.map jsonToTuple arr.toList

def arrayToKVPairList (json : Array Lean.Json) : Prod (List Lean.Json) (List Lean.Json) :=
List.unzip (List.map (λ x => match x with
                                      | Lean.Json.arr kv => (kv[0]!, kv[1]!)
                                      | _ => panic! "arrayToKVPairList: " ++ x.pretty) json.toList)


def jsonObjToKVList (json : Json) : List (String × Json) :=
  match json.getObj? with
  | .ok kvs => kvs.fold (λ acc k v => (k,v) :: acc) []
  | .error e => panic! s!"jsonToKVList: {e}\n" ++ json.pretty

def jsonToBool (json : Json) : Bool :=
  match json.getBool? with
  | .ok b => b
  | .error e => panic! s!"jsonToBool: {e}\n" ++ json.pretty

def jsonToNum (json : Json) : JsonNumber :=
  match json.getNum? with
  | .ok n => n
  | .error e => panic! s!"jsonToNum: {e}\n" ++ json.pretty

def jsonToInt64 (json : Json) : Int64 :=
  let num := jsonToNum json
  match num.exponent with
  | 0 => Int64.mk! num.mantissa
  | n => panic! s!"jsonToInt64: number has exponent {n}"

def jsonToChar (json : Json) : Char :=
  let num := jsonToNum json
  match num.exponent with
  | 0 =>
    let nat := num.mantissa.toNat
    if nat.isValidChar
    then Char.ofNat nat
    else panic! s!"jsonToChar: cannot convert to character {nat}"
  | n => panic! s!"jsonToChar: cannot convert to character {n}"

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
def unpackJsonSum (json : Json) : String × Json := match json with
  | .str tag => (tag, .obj ∅)
  | .obj kvs =>
      if kvs.size == 1 then getSingleElement kvs
      else panic! "unpackJsonSum: expected exactly one key, got either zero or multiple\n" ++ json.pretty
  | _ => panic! "unpackJsonSum: expected an object or a string\n" ++ json.pretty

end DiffTest
