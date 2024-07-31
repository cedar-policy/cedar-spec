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
import Protobuf.Message

namespace Proto

structure HardCodeStruct where
  a: Array Nat -- Field 6
deriving Inhabited, Repr, DecidableEq

namespace HardCodeStruct

/-- Returns whether the wire type matches the field number,
note that this returns true for unknown field numbers-/
def wt_matches (t: Tag) : Bool :=
  match t.fieldNum with
  | 6 => t.wireType = WireType.LEN
  | _ => true

def parse_field (h: HardCodeStruct) (t: Tag) : BParsec HardCodeStruct := do
  match t.fieldNum with
    | 6 =>
      guard (wt_matches t)
      let x ← BParsec.attempt parse_uint32_packed
      pure (HardCodeStruct.mk x)
    | _ =>
      t.wireType.skip
      pure h

instance : Message HardCodeStruct := {
  wt_matches := wt_matches, parse_field := parse_field
}

end HardCodeStruct

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
