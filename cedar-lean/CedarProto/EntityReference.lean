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

namespace Cedar.Spec.EntityUIDOrSlot

-- Already defined in Cedar.Spec
-- inductive EntityUIDOrSlot where
--   | entityUID (entity : EntityUID)
--   | slot (id : SlotID)

-- Note that we cannot automatically parse into
-- EntityUIDOrSlot since the slot id is not known
-- by the EntityReference message

inductive EntityUIDOrSlotProto
  | entityUID (entity: EntityUID)
  | slot
deriving Inhabited

inductive EntityReferenceType where
  | slot
  | euid
deriving Inhabited

namespace EntityReferenceType
def fromInt (n: Int): Except String EntityReferenceType :=
  match n with
    | 0 => .ok .slot
    | 1 => .ok .euid
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum EntityReferenceType := {
  fromInt := fromInt
}
end EntityReferenceType

namespace EntityUIDOrSlotProto
@[inline]
def mergeTy (result: EntityUIDOrSlotProto) (x: EntityReferenceType) : EntityUIDOrSlotProto :=
  -- For enums, if result is already of the same type, then we don't do anything
  -- otherwise, we construct a default object of the new type.
  match x with
    | .euid => match result with
      | .entityUID _ => result
      | .slot => .entityUID default
    | .slot => match result with
      | .entityUID _ => .slot
      | .slot  => result


@[inline]
def mergeEuid (result: EntityUIDOrSlotProto) (x: EntityUID): EntityUIDOrSlotProto :=
  match result with
    | .entityUID e => .entityUID (Field.merge e x)
    | .slot => .entityUID x


@[inline]
def merge (x: EntityUIDOrSlotProto) (y: EntityUIDOrSlotProto) : EntityUIDOrSlotProto :=
  match y with
    | .entityUID e2 => mergeEuid x e2
    | .slot => y

def parseField (t: Tag) : BParsec (StateM EntityUIDOrSlotProto Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityReferenceType) t.wireType
      let x: EntityReferenceType ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeTy s x))
    | 2 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEuid s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message EntityUIDOrSlotProto := {
  parseField := parseField
  merge := merge
}

@[inline]
def toEntityUIDOrSlot (x: EntityUIDOrSlotProto) (s: SlotID): EntityUIDOrSlot :=
  match x with
    | .entityUID e => .entityUID e
    | .slot => .slot s

end EntityUIDOrSlotProto

@[inline]
def merge (x1: EntityUIDOrSlot) (x2: EntityUIDOrSlot) : EntityUIDOrSlot :=
  match x2 with
    | .entityUID e2 => match x1 with
      | .entityUID e1 => .entityUID (Field.merge e1 e2)
      | _ => x2
    | .slot s2 => match x1 with
      | .slot s1 => .slot (Field.merge s1 s2)
      | _ => x2


end Cedar.Spec.EntityUIDOrSlot
