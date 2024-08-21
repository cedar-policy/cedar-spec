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
import CedarProto.Type

open Proto

namespace Cedar.Validation.Proto

-- Note: EntitySchemaEntry takes ancestors,
-- so we'll create an intermediate representation
-- once we gather all the entries, we will perform
-- the transform
structure ValidatorEntityType where
  descendants : Array Spec.EntityTypeProto
  attrs: RecordType
deriving Inhabited

namespace ValidatorEntityType

@[inline]
def mergeDescendants (result: ValidatorEntityType) (x: Array Spec.EntityTypeProto) : ValidatorEntityType :=
  {result with
    descendants := x ++ result.descendants
  }

@[inline]
def mergeAttributes (result: ValidatorEntityType) (x: RecordType): ValidatorEntityType :=
  {result with
    attrs := Field.merge result.attrs x
  }

@[inline]
def merge (x y: ValidatorEntityType) : ValidatorEntityType :=
  {x with
    descendants := y.descendants ++ x.descendants
    attrs := Field.merge x.attrs y.attrs
  }

def parseField (t: Tag) : BParsec (StateM ValidatorEntityType Unit) := do
  match t.fieldNum with
    | 2 =>
      (@Field.guardWireType (Repeated Spec.EntityTypeProto)) t.wireType
      let x: Repeated Spec.EntityTypeProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeDescendants s x))
    | 3 =>
      (@Field.guardWireType RecordType) t.wireType
      let x: RecordType ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeAttributes s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ValidatorEntityType := {
  parseField := parseField
  merge := merge
}

end ValidatorEntityType

end Cedar.Validation.Proto
