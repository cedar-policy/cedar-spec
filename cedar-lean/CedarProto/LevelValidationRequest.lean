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

structure Level where
  level : Nat
deriving Inhabited, DecidableEq, Repr

private def Level.fromInt32 : Proto.Int32 → Level
  | .ofNat n => { level := n }
  | .negSucc _ => panic!("Can't validate with a negative level!")

private def Level.merge (x y : Level) :=
  Level.fromInt32 $ Field.merge (Int.ofNat x.level) (Int.ofNat y.level)

instance : Field Level := Field.fromInterField Level.fromInt32 Level.merge

structure LevelValidationRequest where
  schema : Validation.Schema
  policies : Spec.Policies
  level : Level
deriving Inhabited, DecidableEq, Repr

namespace LevelValidationRequest

instance : Message LevelValidationRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t schema (update schema)
    | 2 => parseFieldElement t policies (update policies)
    | 3 => parseFieldElement t level (update level)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    schema   := Field.merge x.schema   y.schema
    policies := Field.merge x.policies y.policies
    level    := Field.merge x.level    y.level
  }

end LevelValidationRequest

end Cedar.Validation.Proto
