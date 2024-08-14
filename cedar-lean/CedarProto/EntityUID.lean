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

-- Message Dependencies
import CedarProto.EntityType

open Proto

namespace Cedar.Spec

-- Already defined in Cedar.Spec.EntityUID
-- structure EntityUID where
--   ty : EntityType
--   eid : String

namespace EntityUID

@[inline]
def mergeTy (result: EntityUID) (ty: EntityTypeProto) : EntityUID :=
  {result with
    ty := Field.merge result.ty ty
  }

@[inline]
def mergeEid (result: EntityUID) (eid: String) : EntityUID :=
  {result with
    eid := Field.merge result.eid eid
  }

@[inline]
def merge (x1: EntityUID) (x2: EntityUID) : EntityUID :=
  {x1 with
    ty := Field.merge x1.ty x2.ty
    eid := Field.merge x1.eid x2.eid
  }

def parseField (t: Tag) : BParsec (StateM EntityUID Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityTypeProto) t.wireType
      let x: EntityTypeProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeTy x))
    | 2 =>
      (@Field.guardWireType String) t.wireType
      let x: String ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeEid x))
    | _ =>
      t.wireType.skip
      pure (pure ())

instance : Message EntityUID := {
  parseField := parseField
  merge := merge
}

end EntityUID

end Cedar.Spec
