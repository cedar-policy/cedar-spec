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
import Protobuf.BParsec
import Protobuf.Message
import Protobuf.String

import CedarProto.PrincipalOrResourceConstraint

import Cedar
open Cedar.Spec
open Proto

deriving instance Inhabited for ScopeTemplate

structure ResourceConstraint where
  c : ScopeTemplate
deriving Inhabited

namespace Cedar.Spec.ResourceConstraint

@[inline]
def mergeConstraint (result: ResourceConstraint) (x: Cedar.Spec.ScopeTemplate.PrincipalOrResourceConstraint) : ResourceConstraint :=
  ResourceConstraint.mk (ScopeTemplate.merge result.c (x.toScopeTemplate "?resource"))

@[inline]
def merge (x: ResourceConstraint) (y: ResourceConstraint) : ResourceConstraint :=
  {x with
    c := ScopeTemplate.merge x.c y.c
  }


def parseField (t: Tag) : BParsec (StateM ResourceConstraint Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Cedar.Spec.ScopeTemplate.PrincipalOrResourceConstraint) t.wireType
      let x: Cedar.Spec.ScopeTemplate.PrincipalOrResourceConstraint ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeConstraint s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ResourceConstraint := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.ResourceConstraint
