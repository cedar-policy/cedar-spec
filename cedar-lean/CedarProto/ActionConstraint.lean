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

-- Already defined
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
def fromInt (n: Int): Except String ActionScope.Ty :=
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

def mergeEuids (result: ActionScope.In) (e2: Array EntityUID) : ActionScope.In :=
  match result with
    | .actionInAny e1 => .actionInAny (e2.toList ++ e1)
    | _ => panic!("ActionScope.In expected ActionScope constructor to be set to .actionInAny")

def merge (x1 x2: ActionScope.In) : ActionScope.In :=
  have e2 := match x2 with
    | .actionInAny e => e
    | _ => panic!("ActionScope.In expected ActionScope constructor to be set to .actionInAny")
  match x1 with
    | .actionInAny e1 => .actionInAny (e2 ++ e1)
    | _ => panic!("ActionScope.In expected ActionScope constructor to be set to .actionInAny")

def parseField (t: Tag) : BParsec (StateM ActionScope.In Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType (Repeated EntityUID)) t.wireType
      let x: Repeated EntityUID ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEuids s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ActionScope.In := {
  parseField := parseField
  merge := merge
}
end Proto.ActionScope.In

namespace Proto.ActionScope.Eq
instance : Inhabited ActionScope.Eq where
  default := .actionScope (.eq default)
@[inline]
def mergeEuid (result: ActionScope.Eq) (e2: EntityUID) : ActionScope.Eq :=
  match result with
    | .actionScope s => match s with
      | .eq e1 => .actionScope (.eq (Field.merge e1 e2))
      | _ => panic!("ActionScope.Eq expected ActionScope constructor to be set to .actionScope .eq")
    | _ => panic!("ActionScope.Eq expected ActionScope constructor to be set to .actionScope")

@[inline]
def merge (x1 x2: ActionScope.Eq) : ActionScope.Eq :=
  have e2 := match x2 with
    | .actionScope s => match s with
      | .eq e => e
      | _ => panic!("ActionScope.Eq expected ActionScope constructor to be set to .actionScope .eq")
    | _ => panic!("ActionScope.Eq expected ActionScope constructor to be set to .actionScope")
  mergeEuid x1 e2

def parseField (t: Tag) : BParsec (StateM ActionScope.Eq Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEuid s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ActionScope.Eq := {
  parseField := parseField
  merge := merge
}
end Proto.ActionScope.Eq

namespace ActionScope

@[inline]
def mergeTy (_: ActionScope) (x: Proto.ActionScope.Ty) : ActionScope :=
  match x with
    | .any => .actionScope (Scope.any)

@[inline]
def mergeIn (result: ActionScope) (x: Proto.ActionScope.In): ActionScope :=
  have e2 := match x with
    | .actionInAny e => e
    | _ => panic!("Proto.ActionScope.In expected to have constructor .actionInAny")
  match result with
    | .actionInAny e1 => .actionInAny (e2 ++ e1)
    | _ => .actionInAny e2


@[inline]
def mergeEq (result: ActionScope) (x: Proto.ActionScope.Eq): ActionScope :=
  have e2 := match x with
    | .actionScope s => match s with
      | .eq e => e
      | _ => panic!("Proto.ActionScope.Eq expected to have constructor .actionScope .eq")
    | _ => panic!("Proto.ActionScope.Eq expected to have constructor .actionScope")
  match result with
    | .actionScope s => match s with
      | .eq e1 => .actionScope (.eq (Field.merge e1 e2))
      | _ => .actionScope (.eq e2)
    | _ => .actionScope (.eq e2)

@[inline]
def merge (x1 x2: ActionScope) : ActionScope :=
  match x2 with
    | .actionScope s2 => match s2 with
      | .eq e2 => match x1 with
        | .actionScope s => match s with
          -- Merge entity data
          | .eq e1 => .actionScope (.eq (Field.merge e1 e2))
          | _ => x2
        | .actionInAny _ => x2
      | _ => x2
    | .actionInAny l2 => match x1 with
      -- Merge entity uids
      | .actionInAny l1 => .actionInAny (l2 ++ l1)
      | _ => x2

def parseField (t: Tag) : BParsec (StateM ActionScope Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Proto.ActionScope.Ty) t.wireType
      let x: Proto.ActionScope.Ty ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeTy s x))
    | 2 =>
      (@Field.guardWireType Proto.ActionScope.In) t.wireType
      let x: Proto.ActionScope.In ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeIn s x))
    | 3 =>
      (@Field.guardWireType Proto.ActionScope.Eq) t.wireType
      let x: Proto.ActionScope.Eq ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEq s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ActionScope := {
  parseField := parseField
  merge := merge
}

end ActionScope

end Cedar.Spec
