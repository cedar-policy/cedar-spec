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
/-
Struct with array of UInt32 for Benchmarking
-/
import Lean.Data.Json.FromToJson
import Lean.Data.Json.Parser
import Lean.Data.Json.Basic

import Protobuf.Types
import Protobuf.BParsec
import Protobuf.Structures
import Protobuf.Packed

namespace Proto

structure HardCodeStruct where
  a: Array Nat -- Field 6
deriving Inhabited, Repr, DecidableEq

namespace HardCodeStruct

def set_6 (_ : HardCodeStruct) (v: Array Nat) : HardCodeStruct :=
  HardCodeStruct.mk v

/- Get PType from field number -/
def get_type (_: HardCodeStruct) (n: Nat) : Option PType :=
  match n with
  | 6 => some (PType.packed PType.uint32)
  | _ => none

end HardCodeStruct


-- Progresses the entire ByteArray.Iterator
partial def parse_hardcode_helper (result: HardCodeStruct) : BParsec HardCodeStruct := do
  let hasNext ← BParsec.hasNext

  if ¬hasNext then
    return result

  let tag ← BParsec.attempt Tag.parse

  match tag.wireType with
    | .VARINT => throw "Unexpected VARINT WireType"
    | .LEN =>
      match tag.fieldNum with
        | 6 =>
          let x ← BParsec.attempt parse_uint32_packed
          have new_result := result.set_6 x
          (parse_hardcode_helper new_result)
        | _ =>
          -- Skip this field
          let len ← Len.parse
          BParsec.forward len.size
          parse_hardcode_helper result

      | .I32 => throw "Unexpected I32 WireType"
      | .I64 => throw "Unexpected I64 WireType"

      -- The following two records don't have values
      | .SGROUP => parse_hardcode_helper result
      | .EGROUP => parse_hardcode_helper result


def parse_hardcode (i: ByteArray.Iterator) : Except String HardCodeStruct :=
  have empty_result: HardCodeStruct := default
  match (parse_hardcode_helper empty_result) i with
    | BParsec.ParseResult.success _ v => .ok v
    | BParsec.ParseResult.error _ e => .error e


-- JSON functions

def getNat! (j: Lean.Json) : Nat :=
  match j.getNat? with
  | .ok v => v
  | .error _ => panic!("Unable to parse natural number")

def parse_hardcode_json_helper (j: Array Lean.Json) : Array Nat :=
  Array.map getNat! j


def parse_hardcode_json (s: String) : Except String HardCodeStruct :=
  match Lean.Json.parse s with
  | Except.error _ => .error "Error parsing JSON"
  | Except.ok v =>
    have jar := v.getArr?
    match jar with
      | .error _ => .error "Error converting to array"
      | .ok ja =>
        have parsed_array := parse_hardcode_json_helper ja
        .ok (HardCodeStruct.mk parsed_array)


end Proto
