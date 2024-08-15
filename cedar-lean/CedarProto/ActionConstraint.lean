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


namespace ActionScope

inductive ActionConstraintType where
  | any
  | in
  | eq
deriving Inhabited

namespace ActionConstraintType
def get? (n: Int) : Except String ActionConstraintType :=
  match n with
    | 0 => .ok ActionConstraintType.any
    | 1 => .ok ActionConstraintType.in
    | 2 => .ok ActionConstraintType.eq
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum ActionConstraintType where
  fromInt := get?
end ActionConstraintType

@[inline]
def mergeTy (result: ActionScope) (x: ActionConstraintType) : ActionScope :=
  -- ActionConstraintTypes don't contain any data, but exists to tell
  -- us which constructor we need to use. If it matches the current constructor
  -- chosen within ActionScope, then we don't do anything. Otherwise, we switch
  -- to the new constructor with default arguments
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
def mergeEuid (result: ActionScope) (x2: EntityUID): ActionScope :=
  match result with
    | .actionScope s => match s with
      | .eq x1 => .actionScope (.eq (Field.merge x1 x2))
      | _ => .actionScope (.eq x2)
    | _ => .actionScope (.eq x2)

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

end ActionScope

end Cedar.Spec
