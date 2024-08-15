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
import CedarProto.EntityUIDEntry
import CedarProto.Value
import CedarProto.Context

open Proto

namespace Cedar.Spec

-- Already defined
-- structure Request where
--   principal : EntityUID
--   action : EntityUID
--   resource : EntityUID
--   context : Map Attr Value

namespace Request

@[inline]
def mergePrincipal (result: Request) (x: EntityUIDEntry) : Request :=
  {result with
    principal := Field.merge result.principal x
  }

@[inline]
def mergeAction (result: Request) (x: EntityUIDEntry) : Request :=
  {result with
    action := Field.merge result.action x
  }

@[inline]
def mergeResource (result: Request) (x: EntityUIDEntry) : Request :=
  {result with
    resource := Field.merge result.resource x
  }

@[inline]
def mergeContext (result: Request) (x: Context) : Request :=
  {result with
    context := (@Field.merge Context) result.context x
  }

@[inline]
def merge (x: Request) (y: Request) : Request :=
  {x with
    principal := Field.merge x.principal y.principal
    action := Field.merge x.action y.action
    resource := Field.merge x.resource y.resource
    context := (@Field.merge Context) x.context y.context
  }


def parseField (t: Tag) : BParsec (StateM Request Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityUIDEntry) t.wireType
      let x: EntityUIDEntry ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergePrincipal x))
    | 2 =>
      (@Field.guardWireType EntityUIDEntry) t.wireType
      let x: EntityUIDEntry ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeAction x))
    | 3 =>
      (@Field.guardWireType EntityUIDEntry) t.wireType
      let x: EntityUIDEntry ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeResource x))
    | 4 =>
      (@Field.guardWireType Context) t.wireType
      let x: Context ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeContext x))
    | _ =>
      t.wireType.skip
      pure (pure ())

instance : Message Request := {
  parseField := parseField
  merge := merge
}

@[inline]
def mkWf (r: Request) : Request :=
  {r with
    context := Context.mkWf r.context
  }

end Request

end Cedar.Spec
