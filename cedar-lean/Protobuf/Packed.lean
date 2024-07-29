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
namespace Proto

@[inline]
def parse_uint32_packed (size_remaining: Nat): BParsec (Array Nat) :=
  BParsec.foldl
    parse_uint32
    (fun arr => fun element => arr.push element.toNat)
    size_remaining
    #[]

@[inline]
def interpret_uint32_packed (b: ByteArray): Except String (Array Nat) :=
  BParsec.run (parse_uint32_packed b.size) b

@[inline]
def parse_uint64_packed (size_remaining: Nat): BParsec (Array Nat) :=
  BParsec.foldl
    parse_uint32
    (fun arr => fun element => arr.push element.toNat)
    size_remaining
    #[]

@[inline]
def interpret_uint64_packed (b: ByteArray): Except String (Array Nat) :=
  BParsec.run (parse_uint64_packed b.size) b

@[inline]
def parse_generic_packed (f: BParsec α) (size_remaining: Nat): BParsec (Array α) :=
  BParsec.foldl
    f
    (fun arr => fun element => arr.push element)
    size_remaining
    #[]

@[inline]
def parse_int32_packed (size_remaining: Nat): BParsec (Array Int) :=
  parse_generic_packed parse_int32 size_remaining

@[inline]
def interpret_int32_packed (b: ByteArray): Except String (Array Int) :=
  BParsec.run (parse_int32_packed b.size) b

@[inline]
def parse_int64_packed (size_remaining: Nat): BParsec (Array Int) :=
  parse_generic_packed parse_int64 size_remaining

@[inline]
def interpret_int64_packed (b: ByteArray): Except String (Array Int) :=
  BParsec.run (parse_int64_packed b.size) b

#guard interpret_int64_packed (ByteArray.mk #[03, 142, 02, 158, 167, 05]) = Except.ok #[3, 270, 86942]

end Proto
