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
import Cedar
import Protobuf.Message
import Protobuf.Map
import Protobuf.String

-- Message Dependencies
import CedarProto.Value

open Proto

namespace Cedar.Spec

def Context := Cedar.Data.Map Attr Value
deriving Inhabited

namespace Context

@[inline]
def mergeValue (result : Context) (x : Value) : Context :=
  match x with
    | .record m => Cedar.Data.Map.mk (result.kvs ++ m.kvs)
    | _ => panic!("Context is not of correct type")

@[inline]
def merge (x1 : Context) (x2 : Context) : Context :=
  -- Avoid a sort if x1 is empty
  match x1.kvs with
    | [] => x2
    | _ => Cedar.Data.Map.make (x2.kvs ++ x1.kvs)

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn Context) := do
  match t.fieldNum with
    | 1 =>
      let x : Value ← Field.guardedParse t
      pure (mergeValue · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message Context := {
  parseField := parseField
  merge := merge
}

end Context

end Cedar.Spec
