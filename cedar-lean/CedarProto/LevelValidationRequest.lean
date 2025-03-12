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
import Protobuf.Structure

-- Message Dependencies
import CedarProto.Schema
import CedarProto.PolicySet
import CedarProto.ValidationRequest


open Proto

namespace Cedar.Validation.Proto

structure LevelValidationRequest where
  schema : Validation.Schema
  policies : Spec.Policies
  level: Nat
deriving Inhabited, DecidableEq, Repr

namespace LevelValidationRequest

@[inline]
def mergeSchema (result : LevelValidationRequest) (x : Validation.Schema) : LevelValidationRequest :=
  {result with
    schema := Field.merge result.schema x
  }

@[inline]
def mergePolicies (result : LevelValidationRequest) (x : Spec.Policies) : LevelValidationRequest :=
  {result with
    policies := Field.merge result.policies x
  }

@[inline]
def mergeLevel (result : LevelValidationRequest) (x : Proto.Int32) : LevelValidationRequest :=
  have i : Int := x
  {result with
    level :=
      match i with
      | Int.ofNat n  => n
      | Int.negSucc  _ => panic! "Can't validate with a negative level!"
  }

@[inline]
def merge (x y : LevelValidationRequest) : LevelValidationRequest :=
  {
    schema := Field.merge x.schema y.schema
    policies := x.policies ++ y.policies
    level := y.level
  }

@[inline]
def parseField (t : Tag) : BParsec (MergeFn LevelValidationRequest) := do
  match t.fieldNum with
    | 1 =>
      let x : Validation.Schema ← Field.guardedParse t
      pure (pure $ mergeSchema · x)
    | 2 =>
      let x : Spec.Policies ← Field.guardedParse t
      pure (pure $ mergePolicies · x)
    | 3 =>
      let x : Proto.Int32 ← Field.guardedParse t
      pure (pure $ mergeLevel · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message LevelValidationRequest := {
  parseField := parseField
  merge := merge
}

end LevelValidationRequest

end Cedar.Validation.Proto
