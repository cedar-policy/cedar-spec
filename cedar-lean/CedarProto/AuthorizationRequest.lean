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

import CedarProto.Request
import CedarProto.LiteralPolicySet
import CedarProto.Entities

import Cedar
open Cedar.Spec
open Proto

namespace Cedar.Spec
structure AuthorizationRequest where
  request: Request
  entities: Entities
  policies: Policies
deriving Inhabited, DecidableEq
end Cedar.Spec


namespace Cedar.Spec.AuthorizationRequest

@[inline]
def mergeRequest (result: AuthorizationRequest) (x: Request) : AuthorizationRequest :=
  {result with
    request := Field.merge result.request x
  }

@[inline]
def mergeEntities (result: AuthorizationRequest) (x: Entities): AuthorizationRequest :=
  {result with
    entities := Field.merge result.entities x
  }

@[inline]
def mergePolicies (result: AuthorizationRequest) (x: Policies): AuthorizationRequest :=
  {result with
    policies := Field.merge result.policies x
  }

@[inline]
def merge (x y: AuthorizationRequest) : AuthorizationRequest :=
  {x with
    request := Field.merge x.request y.request
    entities := Field.merge x.entities y.entities
    policies := Field.merge x.policies y.policies
  }


def parseField (t: Tag) : BParsec (StateM AuthorizationRequest Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Request) t.wireType
      let x: Request ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeRequest s x))
    | 2 =>
      (@Field.guardWireType Policies) t.wireType
      let x: Policies ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergePolicies s x))
    | 3 =>
      (@Field.guardWireType Entities) t.wireType
      let x: Entities ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEntities s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message AuthorizationRequest := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.AuthorizationRequest
