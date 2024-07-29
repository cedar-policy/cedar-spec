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
Parsers for Repeated Fields
-/
import Protobuf.BParsec
import Protobuf.Varint
import Protobuf.Types
import Protobuf.Structures
namespace Proto

@[inline]
def parse_uint32_packed: BParsec (Array Nat) := do
  let len ← BParsec.attempt Len.parse
  BParsec.foldl
    parse_uint32
    (fun arr => fun element => arr.push element.toNat)
    len.size
    #[]

@[inline]
def interpret_uint32_packed (b: ByteArray): Except String (Array Nat) :=
  BParsec.run parse_uint32_packed b

@[inline]
def parse_uint64_packed: BParsec (Array Nat) := do
  let len ← BParsec.attempt Len.parse
  BParsec.foldl
    parse_uint32
    (fun arr => fun element => arr.push element.toNat)
    len.size
    #[]

@[inline]
def interpret_uint64_packed (b: ByteArray): Except String (Array Nat) :=
  BParsec.run parse_uint64_packed b

@[inline]
def parse_generic_packed (f: BParsec α): BParsec (Array α) := do
  let len ← BParsec.attempt Len.parse
  BParsec.foldl
    f
    (fun arr => fun element => arr.push element)
    len.size
    #[]

@[inline]
def parse_int32_packed: BParsec (Array Int) :=
  parse_generic_packed parse_int32

@[inline]
def interpret_int32_packed (b: ByteArray): Except String (Array Int) :=
  BParsec.run parse_int32_packed b

@[inline]
def parse_int64_packed: BParsec (Array Int) :=
  parse_generic_packed parse_int64

@[inline]
def interpret_int64_packed (b: ByteArray): Except String (Array Int) :=
  BParsec.run parse_int64_packed b

end Proto
