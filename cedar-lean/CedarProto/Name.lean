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
import Protobuf.Structure

open Proto

namespace Cedar.Spec.Proto

structure Name where
  id : String
  path : Repeated String
deriving Repr, Inhabited

namespace Name

instance : Message Name := {
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t id (update id)
    | 2 => parseFieldElement t path (update path)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    id   := Field.merge x.id   y.id
    path := Field.merge x.path y.path
  }
}

def toName : Name -> Spec.Name
  | { id, path } => { id, path := path.toList }

end Name

end Cedar.Spec.Proto

namespace Cedar.Spec

def Name.merge (x y : Name) : Name := {
  id := Field.merge x.id y.id
  path := x.path ++ y.path
}

def EntityType.merge := Name.merge

instance : Field Name := Field.fromInterField Proto.Name.toName Name.merge
instance : Field EntityType := Field.fromInterField (λ n => n) EntityType.merge

end Cedar.Spec
