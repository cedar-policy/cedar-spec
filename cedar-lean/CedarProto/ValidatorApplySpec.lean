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

namespace Cedar.Validation.Proto

structure ValidatorApplySpec where
  principalApplySpec : Array Spec.EntityTypeProto
  resourceApplySpec : Array Spec.EntityTypeProto
deriving Inhabited

namespace ValidatorApplySpec

@[inline]
def mergePas (result: ValidatorApplySpec) (x: Array Spec.EntityTypeProto) : ValidatorApplySpec :=
  {result with
    principalApplySpec := result.principalApplySpec ++ x
  }

@[inline]
def mergeRas (result: ValidatorApplySpec) (x: Array Spec.EntityTypeProto): ValidatorApplySpec :=
  {result with
    resourceApplySpec := result.resourceApplySpec ++ x
  }

@[inline]
def merge (x y: ValidatorApplySpec) : ValidatorApplySpec :=
  {x with
    principalApplySpec := x.principalApplySpec ++ y.principalApplySpec
    resourceApplySpec := x.resourceApplySpec ++ y.resourceApplySpec
  }

@[inline]
def parseField (t: Tag) : BParsec (StateM ValidatorApplySpec Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType (Repeated Spec.EntityTypeProto)) t.wireType
      let x: Repeated Spec.EntityTypeProto ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergePas s x))
    | 2 =>
      (@Field.guardWireType (Repeated Spec.EntityTypeProto)) t.wireType
      let x: Repeated Spec.EntityTypeProto ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeRas s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ValidatorApplySpec := {
  parseField := parseField
  merge := merge
}

end ValidatorApplySpec

end Cedar.Validation.Proto
