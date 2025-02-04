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
import CedarProto.EntityType
import CedarProto.Type

open Proto

namespace Cedar.Validation.Proto

-- Note: EntitySchemaEntry takes ancestors, so we'll create this intermediate
-- representation. Once we gather all the entries, we will perform the transform.
structure ValidatorEntityType where
  /-- All (transitive) descendants. Assumes TC is computed before encoding into protobuf. -/
  descendants : Array Spec.EntityTypeProto
  attrs : RecordType
  tags : Option CedarType
  enums: Array String
deriving Inhabited

-- the Tag message in Validator.proto
structure TagMessage where
  optional_type: CedarType
deriving Repr, Inhabited

namespace TagMessage

@[inline]
def parseField (t : Tag) : BParsec (MergeFn TagMessage) := do
  match t.fieldNum with
    | 1 =>
      let ty : CedarType ← Field.guardedParse t
      pure λ { optional_type := old_ty } => pure { optional_type := Field.merge old_ty ty }
    | _ =>
      t.wireType.skip
      pure ignore

@[inline]
def merge (x y : TagMessage) : TagMessage :=
  {
    optional_type := Message.merge x.optional_type y.optional_type
  }

instance : Message TagMessage where
  parseField := parseField
  merge := merge

end TagMessage

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
def mergeTags (result : ValidatorEntityType) (x : TagMessage) : ValidatorEntityType :=
  {result with
    tags := mergeOption result.tags (some x.optional_type)
  }

@[inline]
def mergeEnums (result : ValidatorEntityType) (x : Array String) : ValidatorEntityType :=
  {result with
    enums := result.enums ++ x
  }

@[inline]
def merge (x y : ValidatorEntityType) : ValidatorEntityType :=
  {
    descendants := y.descendants ++ x.descendants
    attrs := Field.merge x.attrs y.attrs
    tags := mergeOption x.tags y.tags
    enums := x.enums ++ y.enums
  }

@[inline]
def parseField (t : Tag) : BParsec (MergeFn ValidatorEntityType) := do
  match t.fieldNum with
    | 2 =>
      let x : Repeated Spec.EntityTypeProto ← Field.guardedParse t
      pure (pure $ mergeDescendants · x)
    | 3 =>
      let x : RecordType ← Field.guardedParse t
      pure (pure $ mergeAttributes · x)
    | 5 =>
      let x : TagMessage ← Field.guardedParse t
      pure (pure $ mergeTags · x)
    | 6 =>
      let x : Repeated String ← Field.guardedParse t
      pure (pure $ mergeEnums · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message ValidatorEntityType := {
  parseField := parseField
  merge := merge
}

end ValidatorEntityType

end Cedar.Validation.Proto
