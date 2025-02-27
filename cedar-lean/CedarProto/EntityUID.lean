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

-- Message Dependencies
import CedarProto.Name

open Proto

namespace Cedar.Spec

-- Note that Cedar.Spec.EntityUID is defined as
-- structure EntityUID where
--   ty : EntityType
--   eid : String

namespace EntityUID

@[inline]
def mergeTy (result : EntityUID) (ty : Name) : EntityUID :=
  {result with
    ty := Field.merge result.ty ty
  }

@[inline]
def mergeEid (result : EntityUID) (eid : String) : EntityUID :=
  {result with
    eid := Field.merge result.eid eid
  }

@[inline]
def merge (x1 : EntityUID) (x2 : EntityUID) : EntityUID :=
  {x1 with
    ty := Field.merge x1.ty x2.ty
    eid := Field.merge x1.eid x2.eid
  }

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn EntityUID) := do
  match t.fieldNum with
    | 1 =>
      let x : Name ← Field.guardedParse t
      pure (pure $ mergeTy · x)
    | 2 =>
      let x : String ← Field.guardedParse t
      pure (pure $ mergeEid · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message EntityUID := {
  parseField := parseField
  merge := merge
}

end EntityUID

end Cedar.Spec
