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
import CedarProto.ValidatorSchema
import CedarProto.LiteralPolicySet


open Proto

namespace Cedar.Validation.Proto

deriving instance DecidableEq for ActionSchemaEntry
deriving instance DecidableEq for ActionSchema
deriving instance DecidableEq for EntitySchemaEntry
deriving instance DecidableEq for EntitySchema
deriving instance DecidableEq for Schema

structure ValidationRequest where
  schema: Schema
  policies: Spec.Policies
deriving Inhabited, DecidableEq, Repr

namespace ValidationRequest

@[inline]
def mergeSchema (result: ValidationRequest) (x: Schema) : ValidationRequest :=
  {result with
    schema := Field.merge result.schema x
  }

@[inline]
def mergePolicies (result: ValidationRequest) (x: Spec.Policies): ValidationRequest :=
  {result with
    policies := Field.merge result.policies x
  }

@[inline]
def merge (x y: ValidationRequest) : ValidationRequest :=
  {x with
    schema := Field.merge x.schema y.schema
    policies := x.policies ++ y.policies
  }

@[inline]
def parseField (t: Tag) : BParsec (MergeFn ValidationRequest) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Schema) t.wireType
      let x: Schema ← Field.parse
      pure (fun s => mergeSchema s x)
    | 2 =>
      (@Field.guardWireType Spec.Policies) t.wireType
      let x: Spec.Policies ← Field.parse
      pure (fun s => mergePolicies s x)
    | _ =>
      t.wireType.skip
      pure (fun s => s)

instance : Message ValidationRequest := {
  parseField := parseField
  merge := merge
}

end ValidationRequest

end Cedar.Validation.Proto
