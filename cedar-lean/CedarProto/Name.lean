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
import Protobuf.String

open Proto

namespace Cedar.Spec.Name

-- Already defined in Cedar.Spec.Name
-- structure Name where
--   id: String
--   path: List String
-- deriving Inhabited, Repr, DecidableEq

@[inline]
def mergeId (result: Name) (x: String) : Name :=
  {result with
    id := Field.merge result.id x
  }

@[inline]
def mergePath (result: Name) (path_elem: Repeated String): Name :=
  {result with
    path := result.path ++ path_elem.toList
  }

@[inline]
def merge (x y: Name) : Name :=
  {x with
    id := Field.merge x.id y.id
    path := x.path ++ y.path
  }

def parseField (t: Tag) : BParsec (StateM Name Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType String) t.wireType
      let x: String ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeId s x))
    | 2 =>
      (@Field.guardWireType (Repeated String)) t.wireType
      let x: Repeated String ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergePath s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message Name := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.Name
