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
import CedarProto.EntityUID
import CedarProto.Expr
import CedarProto.Value

open Proto

namespace Cedar.Spec.Proto

structure Request where
  principal : EntityUID
  action : EntityUID
  resource : EntityUID
  context : Expr
deriving Repr, Inhabited

namespace Request

instance : Message Request := {
  parseField (t : Proto.Tag) := do match t.fieldNum with
    | 1 => parseFieldElement t principal (update principal)
    | 2 => parseFieldElement t action (update action)
    | 3 => parseFieldElement t resource (update resource)
    | 4 => parseFieldElement t context (update context)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    principal := Field.merge x.principal y.principal
    action    := Field.merge x.action    y.action
    resource  := Field.merge x.resource  y.resource
    context   := Field.merge x.context   y.context
  }
}

def toRequest : Request → Spec.Request
  | { principal, action, resource, context } =>
    {
      principal
      action
      resource
      context := match context with
        | .record pairs => Data.Map.make $ pairs.map λ (k,v) => (k, Spec.Value.exprToValue v)
        | _ => panic!("expected context to be a record")
    }

end Request

end Cedar.Spec.Proto

namespace Cedar.Spec

def Request.merge (x y : Request) : Request := {
  principal := Field.merge x.principal y.principal
  action    := Field.merge x.action    y.action
  resource  := Field.merge x.resource  y.resource
  context   := match x.context.kvs, y.context.kvs with
  -- avoid sort if either is empty
  | [], _ => y.context
  | _, [] => x.context
  | xkvs, ykvs => Data.Map.make $ xkvs ++ ykvs
}

instance : Field Request := Field.fromInterField Proto.Request.toRequest Request.merge

end Cedar.Spec
