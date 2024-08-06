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
import Protobuf.BParsec
import Protobuf.Message
import Protobuf.String

import Cedar
open Cedar.Spec
open Proto


-- Already defined in Cedar.Spec.Name
-- structure Name where
--   id: String
--   path: List String
-- deriving Inhabited, Repr, DecidableEq

namespace Cedar.Spec.Name

def merge_id (result: Name) (x: String) : Name :=
  {result with
    id := Field.merge result.id x
  }

def merge_path (result: Name) (path_elem: Array String): Name :=
  {result with
    path := path_elem.toList ++ result.path
  }

def merge (x: Name) (y: Name) : Name :=
  {x with
    id := Field.merge x.id y.id
    path := x.path ++ y.path
  }


def parseField (t: Tag) : BParsec (MessageM Name) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType String) t.wireType
      let x: String ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => s.merge_id x)
    | 2 =>
      (@Field.guardWireType (Repeated String)) t.wireType
      let x: Repeated String ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => s.merge_path x)
    | _ =>
      t.wireType.skip
      pure MessageM.pure

instance : Message Name := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.Name
