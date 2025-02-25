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
import CedarProto.EntityUID
import CedarProto.Expr
import CedarProto.Value

open Proto

namespace Cedar.Spec

-- Note that Cedar.Spec.Request is defined as
-- structure Request where
--   principal : EntityUID
--   action : EntityUID
--   resource : EntityUID
--   context : Map Attr Value

namespace Request

@[inline]
def mergePrincipal (result : Request) (x : EntityUID) : Request :=
  {result with
    principal := Field.merge result.principal x
  }

@[inline]
def mergeAction (result : Request) (x : EntityUID) : Request :=
  {result with
    action := Field.merge result.action x
  }

@[inline]
def mergeResource (result : Request) (x : EntityUID) : Request :=
  {result with
    resource := Field.merge result.resource x
  }

@[inline]
def mergeContext (result : Request) (x : Value) : Request :=
  match x with
  | .record pairs =>
    {result with
      context := Data.Map.mk (result.context.kvs ++ pairs.kvs)
    }
  | _ => panic!("Context is not of correct type")

@[inline]
def merge (x : Request) (y : Request) : Request :=
  {
    principal := Field.merge x.principal y.principal
    action := Field.merge x.action y.action
    resource := Field.merge x.resource y.resource
    context :=
      -- Avoid a sort if x1 is empty
      match x.context.kvs with
        | [] => y.context
        | _ => Data.Map.make (y.context.kvs ++ x.context.kvs)
  }

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn Request) := do
  match t.fieldNum with
    | 1 =>
      let x : EntityUID ← Field.guardedParse t
      pure (pure $ mergePrincipal · x)
    | 2 =>
      let x : EntityUID ← Field.guardedParse t
      pure (pure $ mergeAction · x)
    | 3 =>
      let x : EntityUID ← Field.guardedParse t
      pure (pure $ mergeResource · x)
    | 4 =>
      let x : Value ← Field.guardedParse t
      pure (pure $ mergeContext · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message Request := {
  parseField := parseField
  merge := merge
}

end Request

end Cedar.Spec
