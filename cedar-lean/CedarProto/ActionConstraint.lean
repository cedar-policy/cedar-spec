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
import Protobuf.Enum
import Protobuf.Message
import Protobuf.String

import CedarProto.EntityUID

import Cedar
open Cedar.Spec
open Proto


-- Already defined
-- inductive ActionScope where
--   | actionScope (scope : Scope)
--   | actionInAny (ls : List EntityUID)


namespace Cedar.Spec.ActionScope

inductive ActionConstraintType where
  | any
  | in
  | eq
deriving Inhabited

namespace ActionConstraintType
def get? (n: Int) : Except String ActionConstraintType :=
  match n with
    | 1 => .ok ActionConstraintType.any
    | 2 => .ok ActionConstraintType.in
    | 3 => .ok ActionConstraintType.eq
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum ActionConstraintType where
  fromInt := get?
end ActionConstraintType


@[inline]
def mergeTy (result: ActionScope) (x: ActionConstraintType) : ActionScope :=
  match x with
    | .any => .actionScope (Scope.any)
    | .eq => match result with
      | .actionScope s => match s with
        | .eq _ => result
        | _ => .actionScope (Scope.eq default)
      | .actionInAny _ => .actionScope (Scope.eq default)
    | .in => match result with
      | .actionScope _ => .actionInAny default
      | .actionInAny _ => result

@[inline]
def mergeEuids (result: ActionScope) (x: Array EntityUID): ActionScope :=
  match result with
    | .actionInAny l => .actionInAny (x.toList ++ l)
    | _ => .actionInAny x.toList

@[inline]
def mergeEuid (result: ActionScope) (x: EntityUID): ActionScope :=
  match result with
    | .actionScope s => match s with
      | .eq x2 => .actionScope (.eq (Field.merge x2 x))
      | _ => .actionScope (.eq x)
    | _ => .actionScope (.eq x)


@[inline]
def merge (x: ActionScope) (y: ActionScope) : ActionScope :=
  match y with
    | .actionScope s2 => match s2 with
      | .eq e2 => match x with
        | .actionScope s => match s with
          | .eq e1 => .actionScope (.eq (Field.merge e1 e2))
          | _ => y
        | .actionInAny _ => y
      | _ => y
    | .actionInAny l2 => match x with
      | .actionInAny l => .actionInAny (l2 ++ l)
      | _ => y



def parseField (t: Tag) : BParsec (StateM ActionScope Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType ActionConstraintType) t.wireType
      let x: ActionConstraintType ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeTy s x))
    | 2 =>
      (@Field.guardWireType (Repeated EntityUID)) t.wireType
      let x: Repeated EntityUID ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEuids s x))
    | 3 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEuid s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ActionScope := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.ActionScope
