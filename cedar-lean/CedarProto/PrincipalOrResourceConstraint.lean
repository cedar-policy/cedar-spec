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

-- Message Dependencies
import CedarProto.EntityReference
import CedarProto.EntityType

open Proto

namespace Cedar.Spec

namespace Proto
-- Constructors for ScopeTemplate

inductive ScopeTemplate.Ty where
  | any
deriving Inhabited

def ScopeTemplate.In := ScopeTemplate
def ScopeTemplate.Eq := ScopeTemplate
def ScopeTemplate.Is := ScopeTemplate
def ScopeTemplate.IsIn := ScopeTemplate
end Proto

namespace Proto.ScopeTemplate.Ty
@[inline]
def fromInt (n: Int): Except String ScopeTemplate.Ty :=
  match n with
    | 0 => .ok .any
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum ScopeTemplate.Ty := {
  fromInt := fromInt
}
end Proto.ScopeTemplate.Ty

namespace Proto.ScopeTemplate.In
instance : Inhabited ScopeTemplate.In where
  default := .mem default
@[inline]
def mergeER (result: ScopeTemplate.In) (e2: EntityUIDOrSlot) : ScopeTemplate.In :=
  match result with
    | .mem e1 => .mem (Field.merge e1 e2)
    | _ => panic!("ScopeTemplate.In expected ScopeTemplate constructor to be set to .in")

@[inline]
def merge (x1 x2: ScopeTemplate.In) : ScopeTemplate.In :=
  have e2 := match x2 with
    | .mem e => e
    | _ => panic!("ScopeTemplate.In expected ScopeTemplate constructor to be set to .in")
  mergeER x1 e2

@[inline]
def parseField (t: Tag) : BParsec (StateM ScopeTemplate.In Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityUIDOrSlot) t.wireType
      let x: EntityUIDOrSlot ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeER s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ScopeTemplate.In := {
  parseField := parseField
  merge := merge
}
end Proto.ScopeTemplate.In

namespace Proto.ScopeTemplate.Eq
instance : Inhabited ScopeTemplate.Eq where
  default := .eq default

@[inline]
def mergeER (result: ScopeTemplate.Eq) (e2: EntityUIDOrSlot) : ScopeTemplate.Eq :=
  match result with
    | .eq e1 => .eq (Field.merge e1 e2)
    | _ => panic!("ScopeTemplate.Eq expected ScopeTemplate constructor to be set to .eq")

@[inline]
def merge (x1 x2: ScopeTemplate.Eq) : ScopeTemplate.Eq :=
  have e2 := match x2 with
    | .eq e => e
    | _ => panic!("ScopeTemplate.Eq expected ScopeTemplate constructor to be set to .eq")
  mergeER x1 e2

@[inline]
def parseField (t: Tag) : BParsec (StateM ScopeTemplate.Eq Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityUIDOrSlot) t.wireType
      let x: EntityUIDOrSlot ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeER s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ScopeTemplate.Eq := {
  parseField := parseField
  merge := merge
}
end Proto.ScopeTemplate.Eq

namespace Proto.ScopeTemplate.Is
instance : Inhabited ScopeTemplate.Is where
  default := .is default

@[inline]
def mergeET (result: ScopeTemplate.Is) (e2: EntityType) : ScopeTemplate.Is :=
  match result with
    | .is e1 => .is (Field.merge e1 e2)
    | _ => panic!("ScopeTemplate.Is expected ScopeTemplate constructor to be set to .is")

@[inline]
def merge (x1 x2: ScopeTemplate.Is) : ScopeTemplate.Is :=
  have e2 := match x2 with
    | .is e => e
    | _ => panic!("ScopeTemplate.Is expected ScopeTemplate constructor to be set to .is")
  mergeET x1 e2

@[inline]
def parseField (t: Tag) : BParsec (StateM ScopeTemplate.Is Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityType) t.wireType
      let x: EntityType ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeET s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ScopeTemplate.Is := {
  parseField := parseField
  merge := merge
}
end Proto.ScopeTemplate.Is

namespace Proto.ScopeTemplate.IsIn
instance : Inhabited ScopeTemplate.IsIn where
  default := .isMem default default

@[inline]
def mergeER (result: ScopeTemplate.IsIn) (er2: EntityUIDOrSlot) : ScopeTemplate.IsIn :=
  match result with
    | .isMem et er1 => .isMem et (Field.merge er1 er2)
    | _ => panic!("ScopeTemplate.IsIn expected ScopeTemplate constructor to be set to .isMem")

@[inline]
def mergeET (result: ScopeTemplate.Is) (et2: EntityType) : ScopeTemplate.Is :=
  match result with
    | .isMem et1 er => .isMem (Field.merge et1 et2) er
    | _ => panic!("ScopeTemplate.IsIn expected ScopeTemplate constructor to be set to .isMem")

@[inline]
def merge (x1 x2: ScopeTemplate.Is) : ScopeTemplate.Is :=
  have ⟨et2, er2⟩ := match x2 with
    | .isMem et er => (et, er)
    | _ => panic!("ScopeTemplate.IsIn expected ScopeTemplate constructor to be set to .isMem")
  match x1 with
    | .isMem et1 er1 => .isMem (Field.merge et1 et2) (Field.merge er1 er2)
    | _ => panic!("ScopeTemplate.IsIn expected ScopeTemplate constructor to be set to .isMem")

@[inline]
def parseField (t: Tag) : BParsec (StateM ScopeTemplate.IsIn Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType EntityUIDOrSlot) t.wireType
      let x: EntityUIDOrSlot ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeER s x))
    | 2 =>
      (@Field.guardWireType EntityType) t.wireType
      let x: EntityType ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeET s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message ScopeTemplate.IsIn := {
  parseField := parseField
  merge := merge
}
end Proto.ScopeTemplate.IsIn

namespace ScopeTemplate

-- Already defined
-- inductive ScopeTemplate where
--   | any
--   | eq (entityOrSlot : EntityUIDOrSlot)
--   | mem (entityOrSlot : EntityUIDOrSlot)
--   | is (ety : EntityType)
--   | isMem (ety : EntityType) (entityOrSlot : EntityUIDOrSlot)


deriving instance Inhabited for EntityUIDOrSlot

@[inline]
def mergeTy (_: ScopeTemplate) (x: Proto.ScopeTemplate.Ty) : ScopeTemplate :=
  match x with
    | .any => .any

@[inline]
def mergeIn (result: ScopeTemplate) (x: Proto.ScopeTemplate.In): ScopeTemplate :=
  have er2 := match x with
    | .mem e => e
    | _ => panic!("Proto.ScopeTemplate.In expected to have constructor .mem")
  match result with
    | .mem er1 => .mem (Field.merge er1 er2)
    | _ => .mem er2

@[inline]
def mergeEq (result: ScopeTemplate) (x: Proto.ScopeTemplate.Eq) : ScopeTemplate :=
  have er2 := match x with
    | .eq e => e
    | _ => panic!("Proto.ScopeTemplate.Eq expected to have constructor .eq")
  match result with
    | .eq er1 => .eq (Field.merge er1 er2)
    | _ => .eq er2

@[inline]
def mergeIs (result: ScopeTemplate) (x: Proto.ScopeTemplate.Is): ScopeTemplate :=
  have et2 := match x with
    | .is e => e
    | _ => panic!("Proto.ScopeTemplate.Is expected to have constructor .is")
  match result with
    | .is et1 => .is (Field.merge et1 et2)
    | _ => .is et2

@[inline]
def mergeIsIn (result: ScopeTemplate) (x: Proto.ScopeTemplate.IsIn): ScopeTemplate :=
  have ⟨et2, er2⟩ := match x with
    | .isMem et er => (et, er)
    | _ => panic!("Proto.ScopeTemplate.IsIn expected to have constructor .isMem")
  match result with
    | .isMem et1 er1 => .isMem (Field.merge et1 et2) (Field.merge er1 er2)
    | _ => .isMem et2 er2


@[inline]
def merge (x1: ScopeTemplate) (x2: ScopeTemplate) : ScopeTemplate :=
  -- If x1 and x2 have different constructors, then
  -- return x2, otherwise merge the fields
  match x2 with
   | .any => x2
   | .mem e2 => match x1 with
    | .mem e1 => .mem (Field.merge e1 e2)
    | _ => x2
   | .eq e2 => match x1 with
    | .eq e1 => .eq (Field.merge e1 e2)
    | _ => x2
   | .is n2 => match x1 with
    | .is n1 => .is (Field.merge n1 n2)
    | _ => x2
   | .isMem n2 e2 => match x1 with
    | .isMem n1 e1 => .isMem (Field.merge n1 n2) (Field.merge e1 e2)
    | _ => x2


def parseField (t: Tag) : BParsec (StateM ScopeTemplate Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Proto.ScopeTemplate.Ty) t.wireType
      let x: Proto.ScopeTemplate.Ty ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeTy s x))
    | 2 =>
      (@Field.guardWireType Proto.ScopeTemplate.In) t.wireType
      let x: Proto.ScopeTemplate.In ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeIn s x))
    | 3 =>
      (@Field.guardWireType Proto.ScopeTemplate.Eq) t.wireType
      let x: Proto.ScopeTemplate.Eq ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeEq s x))
    | 4 =>
      (@Field.guardWireType Proto.ScopeTemplate.Is) t.wireType
      let x: Proto.ScopeTemplate.Is ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeIs s x))
    | 5 =>
      (@Field.guardWireType Proto.ScopeTemplate.IsIn) t.wireType
      let x: Proto.ScopeTemplate.IsIn ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeIsIn s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

deriving instance Inhabited for ScopeTemplate
instance : Message ScopeTemplate := {
  parseField := parseField
  merge := merge
}

@[inline]
def withSlot (x: ScopeTemplate) (s: SlotID): ScopeTemplate :=
  match x with
    | .any => .any
    | .mem er => .mem (er.withSlot s)
    | .eq er => .eq (er.withSlot s)
    | .is et => .is et
    | .isMem et er => .isMem et (er.withSlot s)

end ScopeTemplate

end Cedar.Spec
