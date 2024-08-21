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

-- Message Dependencies
import CedarProto.Name

open Proto

namespace Cedar.Spec

-- Already defined in Cedar.Spec.EntityType
-- abbrev EntityType := Name

-- Note: We don't want it to automatically reduce like
-- abbrev and @[reducible] as this causes issues
-- with typeclass resolution when calling Field.parse
def EntityTypeProto := Cedar.Spec.Name
deriving Inhabited, DecidableEq, Repr, LT

namespace EntityTypeProto

@[inline]
def mergeName (x1: EntityTypeProto) (x2: Name) : EntityTypeProto :=
  (@Field.merge Name) x1 x2

@[inline]
def merge (x1: EntityTypeProto) (x2: EntityTypeProto) : EntityTypeProto :=
  mergeName x1 x2

def parseField (t: Tag) : BParsec (StateM EntityTypeProto Unit) := do
  match t.fieldNum with
    | 2 =>
      (@Field.guardWireType Name) t.wireType
      let x: Name ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeName s x))
    | _ =>
      t.wireType.skip
      pure (pure ())

instance : Message EntityTypeProto := {
  parseField := parseField
  merge := merge
}

end EntityTypeProto

end Cedar.Spec
