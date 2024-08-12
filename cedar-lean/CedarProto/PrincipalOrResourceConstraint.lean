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

import CedarProto.EntityReference
import CedarProto.EntityType

import Cedar
open Cedar.Spec
open Proto




namespace Cedar.Spec.ScopeTemplate

-- Already defined
-- inductive ScopeTemplate where
--   | any
--   | eq (entityOrSlot : EntityUIDOrSlot)
--   | mem (entityOrSlot : EntityUIDOrSlot)
--   | is (ety : EntityType)
--   | isMem (ety : EntityType) (entityOrSlot : EntityUIDOrSlot)

-- Note: In this case, EntityType and EntityUIDOrSlot do not uniquely
-- tell us which constructor to call. Therefore we create an intermediate
-- representation which we can post process later

-- We cannot create ScopeTemplate directly from PrincipalOrResourceConstraint
-- since the slot information is not known in this message

inductive ScopeType where
  | any
  | in
  | eq
  | is
  | isIn
deriving Inhabited

namespace ScopeType
@[inline]
def fromInt (n: Int): Except String ScopeType :=
  match n with
    | 1 => .ok .any
    | 2 => .ok .in
    | 3 => .ok .eq
    | 4 => .ok .is
    | 5 => .ok .isIn
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum ScopeType := {
  fromInt := fromInt
}
end ScopeType

structure PrincipalOrResourceConstraint where
  ty: ScopeType
  er: Cedar.Spec.EntityUIDOrSlot.EntityUIDOrSlotProto
  na: EntityType
deriving Inhabited

namespace PrincipalOrResourceConstraint
@[inline]
def mergeTy (result: PrincipalOrResourceConstraint) (x: ScopeType) : PrincipalOrResourceConstraint :=
  {result with
    ty := Field.merge result.ty x
  }

@[inline]
def mergeEr (result: PrincipalOrResourceConstraint) (x: Cedar.Spec.EntityUIDOrSlot.EntityUIDOrSlotProto): PrincipalOrResourceConstraint :=
  {result with
    er := Field.merge result.er x
  }

@[inline]
def mergeNa (result: PrincipalOrResourceConstraint) (x: EntityType) : PrincipalOrResourceConstraint :=
  {result with
    na := Field.merge result.na x
  }

@[inline]
def merge (x: PrincipalOrResourceConstraint) (y: PrincipalOrResourceConstraint) : PrincipalOrResourceConstraint :=
  {x with
    ty := Field.merge x.ty y.ty
    er := Field.merge x.er y.er
    na := Field.merge x.na y.na
  }


def parseField (t: Tag) : BParsec (StateM PrincipalOrResourceConstraint Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType ScopeType) t.wireType
      let x: ScopeType ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeTy s x))
    | 2 =>
      (@Field.guardWireType Cedar.Spec.EntityUIDOrSlot.EntityUIDOrSlotProto) t.wireType
      let x: Cedar.Spec.EntityUIDOrSlot.EntityUIDOrSlotProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEr s x))
    | 3 =>
      (@Field.guardWireType EntityType) t.wireType
      let x: EntityType ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeNa s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message PrincipalOrResourceConstraint := {
  parseField := parseField
  merge := merge
}

def toScopeTemplate (x: PrincipalOrResourceConstraint) (s: SlotID): ScopeTemplate :=
  match x.ty with
    | .any => .any
    | .in => .mem (x.er.toEntityUIDOrSlot s)
    | .eq => .eq (x.er.toEntityUIDOrSlot s)
    | .is => .is x.na
    | .isIn => .isMem x.na (x.er.toEntityUIDOrSlot s)

end PrincipalOrResourceConstraint

def merge (x1: ScopeTemplate) (x2: ScopeTemplate) : ScopeTemplate :=
  match x2 with
   | .any => x2
   | .mem e2 => match x1 with
    | .mem e1 => .mem (EntityUIDOrSlot.merge e1 e2)
    | _ => x2
   | .eq e2 => match x1 with
    | .eq e1 => .eq (EntityUIDOrSlot.merge e1 e2)
    | _ => x2
   | .is n2 => match x1 with
    | .is n1 => .is (Field.merge n1 n2)
    | _ => x2
   | .isMem n2 e2 => match x1 with
    | .isMem n1 e1 => .isMem (Field.merge n1 n2) (EntityUIDOrSlot.merge e1 e2)
    | _ => x2


end Cedar.Spec.ScopeTemplate
