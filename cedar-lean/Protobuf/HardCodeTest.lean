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

import Protobuf.BParsec
import Protobuf.Field
import Protobuf.Message
import Protobuf.Packed
import Protobuf.Structures
import Protobuf.Types

namespace Proto

structure HardCodeStruct where
  f6: Array UInt32 -- Field 6
deriving Inhabited, Repr, DecidableEq

namespace HardCodeStruct

def merge_6 (result: HardCodeStruct) (x: Array UInt32) : HardCodeStruct :=
  {result with
    f6 := (@Field.merge (Packed UInt32)) result.f6 x
  }

def merge (x: HardCodeStruct) (y: HardCodeStruct) : HardCodeStruct :=
  {x with
    f6 := (@Field.merge (Packed UInt32)) x.f6 y.f6
  }

def parseField (t: Tag) : BParsec (MessageM HardCodeStruct) := do
  match t.fieldNum with
    | 6 =>
      (@Field.guardWireType (Packed UInt32)) t.wireType
      let x: Packed UInt32 ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => s.merge_6 x)
    | _ =>
      t.wireType.skip
      pure MessageM.pure



instance : Message HardCodeStruct := {
  parseField := parseField
  merge := merge
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
        have convert_array := parsed_array.map (fun pai => pai.toUInt32)
        .ok (HardCodeStruct.mk convert_array)


end Proto
