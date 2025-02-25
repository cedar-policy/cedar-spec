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
import CedarProto.Type

open Proto

namespace Cedar.Validation.Proto

-- Note: EntitySchemaEntry takes ancestors,
-- so we'll create an intermediate representation
-- once we gather all the entries, we will perform
-- the transform
structure ActionDecl where
  name : Spec.EntityUID
  descendants : Array Spec.EntityUID
  context : CedarType
  principal_types : Array Spec.Name
  resource_types : Array Spec.Name

instance : Inhabited ActionDecl where
  default := ActionDecl.mk default default (CedarType.record default) default default

namespace ActionDecl

@[inline]
def mergeName (result : ActionDecl) (x : Spec.EntityUID) : ActionDecl :=
  {result with
    name := Field.merge result.name x
  }

@[inline]
def mergeDescendants (result : ActionDecl) (x : Array Spec.EntityUID) : ActionDecl :=
  {result with
    descendants := result.descendants ++ x
  }

@[inline]
def mergeContext (result : ActionDecl) (x : CedarType) : ActionDecl :=
  {result with
    context := Field.merge result.context x
  }

@[inline]
def mergePrincipalTypes (result : ActionDecl) (x : Array Spec.Name) : ActionDecl :=
  {result with
    principal_types := result.principal_types ++ x
  }

@[inline]
def mergeResourceTypes (result : ActionDecl) (x : Array Spec.Name) : ActionDecl :=
  {result with
    resource_types := result.resource_types ++ x
  }

@[inline]
def merge (x y : ActionDecl) : ActionDecl :=
  {
    name := Field.merge x.name y.name
    descendants := x.descendants ++ y.descendants
    context := Field.merge x.context y.context
    principal_types := x.principal_types ++ y.principal_types
    resource_types := x.resource_types ++ y.resource_types
  }

@[inline]
def parseField (t : Tag) : BParsec (MergeFn ActionDecl) := do
  match t.fieldNum with
    | 1 =>
      let x : Spec.EntityUID ← Field.guardedParse t
      pure (pure $ mergeName · x)
    | 3 =>
      let x : Repeated Spec.EntityUID ← Field.guardedParse t
      pure (pure $ mergeDescendants · x)
    | 4 =>
      let x : CedarType ← Field.guardedParse t
      pure (pure $ mergeContext · x)
    | 7 =>
      let x : Repeated Spec.Name ← Field.guardedParse t
      pure (pure $ mergePrincipalTypes · x)
    | 8 =>
      let x : Repeated Spec.Name ← Field.guardedParse t
      pure (pure $ mergeResourceTypes · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message ActionDecl := {
  parseField := parseField
  merge := merge
}

end ActionDecl

end Cedar.Validation.Proto
