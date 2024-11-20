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
  attrs : RecordType
  tags : Option CedarType
deriving Inhabited

namespace ValidatorEntityType

@[inline]
def mergeOption [Field α] (x1 x2 : Option α) : Option α :=
  match x1, x2 with
  | some s1, some s2 => some (Field.merge s1 s2)
  | none, some x => some x
  | some x, none => some x
  | none, none => none

@[inline]
def mergeDescendants (result : ValidatorEntityType) (x : Array Spec.EntityTypeProto) : ValidatorEntityType :=
  {result with
    descendants := result.descendants ++ x
  }

@[inline]
def mergeAttributes (result : ValidatorEntityType) (x : RecordType) : ValidatorEntityType :=
  {result with
    attrs := Field.merge result.attrs x
  }

@[inline]
def mergeTags (result : ValidatorEntityType) (x : Option CedarType) : ValidatorEntityType :=
  {result with
    tags := mergeOption result.tags x
  }

@[inline]
def merge (x y : ValidatorEntityType) : ValidatorEntityType :=
  {
    descendants := y.descendants ++ x.descendants
    attrs := Field.merge x.attrs y.attrs
    tags := mergeOption x.tags y.tags
  }

@[inline]
def parseField (t : Tag) : BParsec (MergeFn ValidatorEntityType) := do
  match t.fieldNum with
    | 2 =>
      let x : Repeated Spec.EntityTypeProto ← Field.guardedParse t
      pure (mergeDescendants · x)
    | 3 =>
      let x : RecordType ← Field.guardedParse t
      pure (mergeAttributes · x)
    | 4 =>
      let x : CedarType ← Field.guardedParse t
      pure (mergeTags · x)
    | _ =>
      t.wireType.skip
      pure id

instance : Message ValidatorEntityType := {
  parseField := parseField
  merge := merge
}

end ValidatorEntityType

end Cedar.Validation.Proto
