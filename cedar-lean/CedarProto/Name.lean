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
import Cedar.Spec
import Protobuf.Message
import Protobuf.String

open Proto

namespace Cedar.Spec.Name

-- Note that Cedar.Spec.Name is defined as
-- structure Name where
--   id : String
--   path : List String
-- deriving Inhabited, Repr, DecidableEq

@[inline]
def mergeId (result : Name) (x : String) : Name :=
  {result with
    id := Field.merge result.id x
  }

@[inline]
def mergePath (result : Name) (path_elem : Repeated String) : Name :=
  {result with
    path := result.path ++ path_elem.toList
  }

@[inline]
def merge (x y : Name) : Name :=
  {
    id := Field.merge x.id y.id
    path := x.path ++ y.path
  }

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn Name) := do
  match t.fieldNum with
    | 1 =>
      let x : String ← Field.guardedParse t
      pure (mergeId · x)
    | 2 =>
      let x : Repeated String ← Field.guardedParse t
      pure (mergePath · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message Name := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.Name
