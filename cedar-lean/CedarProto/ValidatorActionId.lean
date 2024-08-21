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
import CedarProto.EntityUID
import CedarProto.Expr
import CedarProto.Type
import CedarProto.ValidatorApplySpec

open Proto

namespace Cedar.Validation.Proto

-- Note: EntitySchemaEntry takes ancestors,
-- so we'll create an intermediate representation
-- once we gather all the entries, we will perform
-- the transform
structure ValidatorActionId where
  appliesTo: ValidatorApplySpec
  descendants: Array Spec.EntityUID
  context: CedarType

instance : Inhabited ValidatorActionId where
  default := ValidatorActionId.mk default default (CedarType.record default)

namespace ValidatorActionId

@[inline]
def mergeAppliesTo (result: ValidatorActionId) (x: ValidatorApplySpec) : ValidatorActionId :=
  {result with
    appliesTo := Field.merge result.appliesTo x
  }

@[inline]
def mergeDescendants (result: ValidatorActionId) (x: Array Spec.EntityUID): ValidatorActionId :=
  {result with
    descendants := x ++ result.descendants
  }

@[inline]
def mergeContext (result: ValidatorActionId) (x: CedarType): ValidatorActionId :=
  {result with
    context := Field.merge result.context x
  }

@[inline]
def merge (x y: ValidatorActionId) : ValidatorActionId :=
  {x with
    appliesTo := Field.merge x.appliesTo y.appliesTo
    descendants := y.descendants ++ x.descendants
    context := Field.merge x.context y.context
  }

def parseField (t: Tag) : BParsec (StateM ValidatorActionId Unit) := do
  match t.fieldNum with
    | 2 =>
      (@Field.guardWireType ValidatorApplySpec) t.wireType
      let x: ValidatorApplySpec ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeAppliesTo s x))
    | 3 =>
      (@Field.guardWireType (Repeated Spec.EntityUID)) t.wireType
      let x: Repeated Spec.EntityUID ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeDescendants s x))
    | 4 =>
      (@Field.guardWireType CedarType) t.wireType
      let x: CedarType ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeContext s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ValidatorActionId := {
  parseField := parseField
  merge := merge
}

end ValidatorActionId

end Cedar.Validation.Proto
