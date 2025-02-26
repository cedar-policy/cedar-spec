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
import CedarProto.Name
import CedarProto.Type

open Proto

namespace Cedar.Validation.Proto

-- Note: EntitySchemaEntry takes ancestors, so we'll create this intermediate
-- representation. Once we gather all the entries, we will perform the transform.
structure EntityDecl where
  name : Spec.Name
  /-- All (transitive) descendants. Assumes TC is computed before encoding into protobuf. -/
  descendants : Array Spec.Name
  attrs : Proto.Map String (Qualified ProtoType)
  tags : Option ProtoType
  enums : Array String
deriving Repr, Inhabited

namespace EntityDecl

@[inline]
def mergeOption [Field α] (x1 x2 : Option α) : Option α :=
  match x1, x2 with
  | some s1, some s2 => some (Field.merge s1 s2)
  | none, some x => some x
  | some x, none => some x
  | none, none => none

@[inline]
def mergeName (result : EntityDecl) (x : Spec.Name) : EntityDecl :=
  {result with
    name := Field.merge result.name x
  }

@[inline]
def mergeDescendants (result : EntityDecl) (x : Array Spec.Name) : EntityDecl :=
  {result with
    descendants := result.descendants ++ x
  }

@[inline]
def mergeAttributes (result : EntityDecl) (x : Proto.Map String (Qualified ProtoType)) : EntityDecl :=
  {result with
    attrs := result.attrs ++ x
  }

@[inline]
def mergeTags (result : EntityDecl) (x : ProtoType) : EntityDecl :=
  {result with
    tags := mergeOption result.tags (some x)
  }

@[inline]
def mergeEnums (result : EntityDecl) (x : Array String) : EntityDecl :=
  {result with
    enums := result.enums ++ x
  }

@[inline]
def merge (x y : EntityDecl) : EntityDecl :=
  {
    name := Field.merge x.name y.name
    descendants := y.descendants ++ x.descendants
    attrs := x.attrs ++ y.attrs
    tags := mergeOption x.tags y.tags
    enums := x.enums ++ y.enums
  }

@[inline]
def parseField (t : Tag) : BParsec (MergeFn EntityDecl) := do
  match t.fieldNum with
    | 1 =>
      let x : Spec.Name ← Field.guardedParse t
      pure (pure $ mergeName · x)
    | 2 =>
      let x : Repeated Spec.Name ← Field.guardedParse t
      pure (pure $ mergeDescendants · x)
    | 3 =>
      let x : Proto.Map String (Qualified ProtoType) ← Field.guardedParse t
      pure (pure $ mergeAttributes · x)
    | 5 =>
      let x : ProtoType ← Field.guardedParse t
      pure (pure $ mergeTags · x)
    | 6 =>
      let x : Repeated String ← Field.guardedParse t
      pure (pure $ mergeEnums · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message EntityDecl := {
  parseField := parseField
  merge := merge
}

end EntityDecl

end Cedar.Validation.Proto
