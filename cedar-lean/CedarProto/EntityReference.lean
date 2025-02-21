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
import Protobuf.Enum

-- Message Dependencies
import CedarProto.EntityUID

open Proto

namespace Cedar.Spec

namespace Proto
inductive EntityReferenceType where
  | slot
deriving Inhabited

namespace EntityReferenceType
@[inline]
def fromInt (n : Int) : Except String EntityReferenceType :=
  match n with
    | 0 => .ok .slot
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum EntityReferenceType := {
  fromInt := fromInt
}
end EntityReferenceType
end Proto

namespace EntityUIDOrSlot

deriving instance Inhabited for EntityUIDOrSlot

@[inline]
def mergeTy (result : EntityUIDOrSlot) (x : Proto.EntityReferenceType) : EntityUIDOrSlot :=
  -- For enums, if result is already of the same type, then we don't do anything
  -- otherwise, we construct a default object of the new type.
  match x with
    | .slot => match result with
      | .entityUID _ => .slot default
      | .slot _ => result

@[inline]
def mergeEuid (result : EntityUIDOrSlot) (x : EntityUID) : EntityUIDOrSlot :=
  match result with
    | .entityUID e => .entityUID (Field.merge e x)
    | .slot _ => .entityUID x

@[inline]
def merge (x : EntityUIDOrSlot) (y : EntityUIDOrSlot) : EntityUIDOrSlot :=
  match y with
    | .entityUID e2 => mergeEuid x e2
    | .slot s2 => match x with
      | .entityUID _ => y
      | .slot s1 => .slot (Field.merge s1 s2)


@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn EntityUIDOrSlot) := do
  match t.fieldNum with
    | 1 =>
      let x : Proto.EntityReferenceType ← Field.guardedParse t
      pure (pure $ mergeTy · x)
    | 2 =>
      let x : EntityUID ← Field.guardedParse t
      pure (pure $ mergeEuid · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message EntityUIDOrSlot := {
  parseField := parseField
  merge := merge
}

@[inline]
def withSlot (x : EntityUIDOrSlot) (s : SlotID) : EntityUIDOrSlot :=
  match x with
    | .entityUID _ => x
    | .slot _ => .slot s

end EntityUIDOrSlot

end Cedar.Spec
