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

import Cedar

-- Dependencies
import CedarProto.EntityUID
import CedarProto.Value

open Cedar.Spec
open Proto

-- Defined in Cedar.Spec..
-- structure Request where
--   principal : EntityUID
--   action : EntityUID
--   resource : EntityUID
--   context : Map Attr Value

namespace Cedar.Spec.Request

def mergePrincipal (result: Request) (x: EntityUID) : Request :=
  {result with
    principal := Field.merge result.principal x
  }

def mergeAction (result: Request) (x: EntityUID) : Request :=
  {result with
    action := Field.merge result.action x
  }

def mergeResource (result: Request) (x: EntityUID) : Request :=
  {result with
    resource := Field.merge result.resource x
  }

def mergeContext (result: Request) (x: Value) : Request :=
  match x with
    | .record m =>
      {result with
        context := Data.Map.make (result.context.kvs ++ m.kvs)
      }
    | _ => panic!("Context is not of correct type")

def merge (x: Request) (y: Request) : Request :=
  {x with
    principal := (@Field.merge EntityUID) x.principal y.principal
    action := (@Field.merge EntityUID) x.action y.action
    resource := (@Field.merge EntityUID) x.resource y.resource
    context := Data.Map.make (x.context.kvs ++ y.context.kvs)
  }

def parseField (t: Tag) : BParsec (MessageM Request) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => s.mergePrincipal x)
    | 2 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => s.mergeAction x)
    | 3 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => s.mergeResource x)
    | 4 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: Value ← BParsec.attempt Field.parse
      pure (MessageM.modifyGet fun s => s.mergeContext x)
    | _ =>
      t.wireType.skip
      pure MessageM.pure

instance : Message Request := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.Request
