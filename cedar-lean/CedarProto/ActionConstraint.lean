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
import Protobuf.Enum

-- Message Dependencies
import CedarProto.EntityUID

open Proto

namespace Cedar.Spec

-- Note that Cedar.Spec.ActionScope is defined as
-- inductive ActionScope where
--   | actionScope (scope : Scope)
--   | actionInAny (ls : List EntityUID)

namespace Proto
-- Constructors for ActionScope

inductive ActionScope.Ty where
  | any
deriving Inhabited

def ActionScope.In := ActionScope
def ActionScope.Eq := ActionScope
end Proto

namespace Proto.ActionScope.Ty
@[inline]
def fromInt (n : Int) : Except String ActionScope.Ty :=
  match n with
  | 0 => .ok .any
  | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum ActionScope.Ty := {
  fromInt := fromInt
}
end Proto.ActionScope.Ty

namespace Proto.ActionScope.In
instance : Inhabited ActionScope.In where
  default := .actionInAny default

@[inline]
def mergeEuids (result : ActionScope.In) (e2 : Array EntityUID) : ActionScope.In :=
  match result with
    | .actionInAny e1 => .actionInAny (e1 ++ e2.toList)
    | _ => panic!("ActionScope.In expected ActionScope constructor to be set to .actionInAny")

@[inline]
def merge (x1 x2 : ActionScope.In) : ActionScope.In :=
  match x1, x2 with
  | .actionInAny e1, .actionInAny e2 =>
    .actionInAny (e1 ++ e2)
  | _, _ => panic!("ActionScope.In expected ActionScope constructor to be set to .actionInAny")

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn ActionScope.In) := do
  match t.fieldNum with
    | 1 =>
      let x : Repeated EntityUID ← Field.guardedParse t
      pure (mergeEuids · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message ActionScope.In := {
  parseField := parseField
  merge := merge
}
end Proto.ActionScope.In

namespace Proto.ActionScope.Eq
instance : Inhabited ActionScope.Eq where
  default := .actionScope (.eq default)

@[inline]
def mergeEuid (result : ActionScope.Eq) (e2 : EntityUID) : ActionScope.Eq :=
  match result with
  | .actionScope (.eq e1) => .actionScope (.eq (Field.merge e1 e2))
  | _ => panic!("ActionScope.Eq expected ActionScope constructor to be set to .actionScope .eq")

@[inline]
def merge (x1 x2 : ActionScope.Eq) : ActionScope.Eq :=
  match x2 with
  | .actionScope (.eq e) => mergeEuid x1 e
  | _ => panic!("ActionScope.Eq expected ActionScope constructor to be set to .actionScope .eq")

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn ActionScope.Eq) := do
  match t.fieldNum with
    | 1 =>
      let x : EntityUID ← Field.guardedParse t
      pure (mergeEuid · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message ActionScope.Eq := {
  parseField := parseField
  merge := merge
}
end Proto.ActionScope.Eq

namespace ActionScope

@[inline]
def mergeTy (_ : ActionScope) (x : Proto.ActionScope.Ty) : ActionScope :=
  match x with
    | .any => .actionScope (Scope.any)

@[inline]
def mergeIn (result : ActionScope) (x : Proto.ActionScope.In) : ActionScope :=
  have e2 := match x with
    | .actionInAny e => e
    | _ => panic!("Proto.ActionScope.In expected to have constructor .actionInAny")
  match result with
    | .actionInAny e1 => .actionInAny (e1 ++ e2)
    | _ => .actionInAny e2

@[inline]
def mergeEq (result : ActionScope) (x : Proto.ActionScope.Eq) : ActionScope :=
  have e2 := match x with
    | .actionScope (.eq e) => e
    | _ => panic!("Proto.ActionScope.Eq expected to have constructor .actionScope .eq")
  match result with
    | .actionScope (.eq e1) => .actionScope (.eq (Field.merge e1 e2))
    | _ => .actionScope (.eq e2)

@[inline]
def merge (x1 x2 : ActionScope) : ActionScope :=
  match x1, x2 with
  | .actionScope (.eq e1), .actionScope (.eq e2) =>
    -- Merge entity data
    .actionScope (.eq (Field.merge e1 e2))
  | .actionInAny l1, .actionInAny l2 =>
    -- Merge entity uids
    .actionInAny (l1 ++ l2)
  | _, _ => x2

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn ActionScope) := do
  match t.fieldNum with
    | 1 =>
      let x : Proto.ActionScope.Ty ← Field.guardedParse t
      pure (mergeTy · x)
    | 2 =>
      let x : Proto.ActionScope.In ← Field.guardedParse t
      pure (mergeIn · x)
    | 3 =>
      let x : Proto.ActionScope.Eq ← Field.guardedParse t
      pure (mergeEq · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message ActionScope := {
  parseField := parseField
  merge := merge
}

end ActionScope

end Cedar.Spec
