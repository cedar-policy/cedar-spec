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

-- Message Dependencies
import CedarProto.Request
import CedarProto.LiteralPolicySet
import CedarProto.Entities

open Proto

namespace Cedar.Spec
structure AuthorizationRequest where
  request : Request
  entities : Entities
  policies : Policies
deriving Inhabited, DecidableEq, Repr

namespace AuthorizationRequest

@[inline]
def mergeRequest (result : AuthorizationRequest) (x : Request) : AuthorizationRequest :=
  {result with
    request := Field.merge result.request x
  }

@[inline]
def mergeEntities (result : AuthorizationRequest) (x : Entities) : AuthorizationRequest :=
  {result with
    entities := Field.merge result.entities x
  }

@[inline]
def mergePolicies (result : AuthorizationRequest) (x : Policies) : AuthorizationRequest :=
  {result with
    policies := Field.merge result.policies x
  }

@[inline]
def merge (x y : AuthorizationRequest) : AuthorizationRequest :=
  {
    request := Field.merge x.request y.request
    entities := Field.merge x.entities y.entities
    policies := Field.merge x.policies y.policies
  }

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn AuthorizationRequest) := do
  match t.fieldNum with
    | 1 =>
      let x : Request ← Field.guardedParse t
      pure (mergeRequest · x)
    | 2 =>
      let x : Policies ← Field.guardedParse t
      pure (mergePolicies · x)
    | 3 =>
      let x : Entities ← Field.guardedParse t
      pure (mergeEntities · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message AuthorizationRequest := {
  parseField := parseField
  merge := merge
}

end AuthorizationRequest

end Cedar.Spec
