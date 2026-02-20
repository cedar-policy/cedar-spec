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
import Cedar.Thm.Data

namespace Cedar.Validation
open Cedar.Data
open Cedar.Spec

----- Definitions -----

inductive BoolType where
  | anyBool
  | tt
  | ff
deriving Repr

def BoolType.not : BoolType → BoolType
  | .anyBool => .anyBool
  | .tt => .ff
  | .ff => .tt

def BoolType.lift : BoolType → BoolType
  | _ => .anyBool

inductive ExtType where
  | ipAddr
  | decimal
  | datetime
  | duration
deriving Repr

inductive Qualified (α : Type u) where
  | optional (a : α)
  | required (a : α)
deriving Repr

namespace Qualified

instance [Inhabited α] : Inhabited (Qualified α) where
  default := .required default

def getType {α} : Qualified α → α
  | optional a => a
  | required a => a

def isRequired {α} : Qualified α → Bool
  | optional _ => false
  | required _ => true

-- effectively making Qualified a functor
def map {α β} (f : α → β) : Qualified α → Qualified β
  | optional a => optional (f a)
  | required a => required (f a)

def transpose {α ε} : Qualified (Except ε α) → Except ε (Qualified α)
  | optional (.ok a) => .ok (optional a)
  | required (.ok a) => .ok (required a)
  | optional (.error e) => .error e
  | required (.error e) => .error e

end Qualified

inductive CedarType where
  | bool (bty : BoolType)
  | int
  | string
  | entity (ety : EntityType)
  | set (ty : CedarType)
  | record (rty : Map Attr (Qualified CedarType))
  | ext (xty : ExtType)
deriving Repr

instance : Inhabited CedarType where
  default := .int

abbrev QualifiedType := Qualified CedarType

abbrev RecordType := Map Attr QualifiedType

mutual
def QualifiedType.liftBoolTypes : QualifiedType → QualifiedType
  | .optional ty => .optional ty.liftBoolTypes
  | .required ty => .required ty.liftBoolTypes

def RecordType.liftBoolTypes : RecordType → RecordType
  | rty => rty.mapOnValues₂ λ ⟨v, _⟩ => v.liftBoolTypes

def CedarType.liftBoolTypes : CedarType → CedarType
  | .bool bty => .bool bty.lift
  | .set s => .set s.liftBoolTypes
  | .record rty => .record (RecordType.liftBoolTypes rty)
  | ty => ty
end

structure StandardSchemaEntry where
  ancestors : Cedar.Data.Set EntityType
  attrs : RecordType
  tags : Option CedarType

inductive EntitySchemaEntry where
  | standard (ty: StandardSchemaEntry)
  | enum (eids: Set String)

def EntitySchemaEntry.isValidEntityEID (entry: EntitySchemaEntry) (eid: String): Bool :=
  match entry with
  | .standard _ => true
  | .enum eids => eids.contains eid

def EntitySchemaEntry.tags? : EntitySchemaEntry → Option CedarType
  | .standard ty => ty.tags
  | .enum _ => none

def EntitySchemaEntry.attrs : EntitySchemaEntry → RecordType
  | .standard ty => ty.attrs
  | .enum _ => Map.empty

def EntitySchemaEntry.ancestors : EntitySchemaEntry → Set EntityType
  | .standard ty => ty.ancestors
  | .enum _ => Set.empty

def EntitySchemaEntry.isStandard : EntitySchemaEntry → Bool
  | .standard _ => true
  | .enum _     => false

abbrev EntitySchema := Map EntityType EntitySchemaEntry

def EntitySchema.entityTypeMembers? (ets: EntitySchema) (et: EntityType) : Option (Set String) :=
  match ets.find? et with
  | .some (.enum eids) => .some eids
  | _ => .none

def EntitySchema.isValidEntityUID (ets : EntitySchema) (uid : EntityUID) : Bool :=
  match ets.find? uid.ty with
  | .some entry => entry.isValidEntityEID uid.eid
  | .none   => false

def EntitySchema.contains (ets : EntitySchema) (ety : EntityType) : Bool :=
  (ets.find? ety).isSome

def EntitySchema.attrs? (ets : EntitySchema) (ety : EntityType) : Option RecordType :=
  (ets.find? ety).map EntitySchemaEntry.attrs

def EntitySchema.tags? (ets : EntitySchema) (ety : EntityType) : Option (Option CedarType) :=
  (ets.find? ety).map EntitySchemaEntry.tags?

structure ActionSchemaEntry where
  appliesToPrincipal : Set EntityType
  appliesToResource : Set EntityType
  ancestors : Set EntityUID
  context : RecordType
deriving Repr, Inhabited

abbrev ActionSchema := Map EntityUID ActionSchemaEntry

def ActionSchema.actionType? (acts: ActionSchema) (ety : EntityType) : Bool :=
  acts.keys.any (EntityUID.ty · == ety)

def ActionSchema.contains (as : ActionSchema) (uid : EntityUID) : Bool :=
  (as.find? uid).isSome

def ActionSchema.descendentOf (as : ActionSchema)  (uid₁ uid₂ : EntityUID) : Bool :=
  if uid₁ == uid₂
  then true
  else match as.find? uid₁ with
    | .some entry => entry.ancestors.contains uid₂
    | .none => false

structure Schema where
  ets : EntitySchema
  acts : ActionSchema

structure RequestType where
  principal : EntityType
  action : EntityUID
  resource : EntityType
  context : RecordType
deriving Inhabited

structure TypeEnv where
  ets : EntitySchema
  acts : ActionSchema
  reqty : RequestType
deriving Inhabited

def ActionSchema.maybeDescendentOf (as : ActionSchema) (ety₁ ety₂ : EntityType) : Bool :=
  as.kvs.any λ (act, entry) => act.ty = ety₁ && entry.ancestors.any (EntityUID.ty · == ety₂)

def TypeEnv.descendentOf (env : TypeEnv) (ety₁ ety₂ : EntityType) : Bool :=
  if ety₁ = ety₂
  then true
  else match env.ets.find? ety₁ with
    | .some entry => entry.ancestors.contains ety₂
    | .none       => env.acts.maybeDescendentOf ety₁ ety₂

----- Derivations -----

deriving instance Repr, DecidableEq for BoolType
deriving instance Repr, DecidableEq, Inhabited for ExtType
deriving instance Repr, DecidableEq, Inhabited for Qualified
deriving instance Repr, Inhabited for CedarType
deriving instance Repr for ActionSchemaEntry
deriving instance Repr for StandardSchemaEntry
deriving instance Repr for EntitySchemaEntry
deriving instance Repr for Schema

mutual

def decCedarType (a b : CedarType) : Decidable (a = b) := by
  cases a <;> cases b
  case string.string => apply isTrue (by rfl)
  case int.int => apply isTrue (by rfl)
  case bool.bool b1 b2 => exact match decEq b1 b2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set t1 t2 => exact match decCedarType t1 t2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case entity.entity lub1 lub2 => exact match decEq lub1 lub2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record r1 r2 => exact match decAttrQualifiedCedarTypeMap r1 r2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ext.ext n1 n2 => exact match decEq n1 n2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  all_goals {
    apply isFalse
    intro h
    injection h
  }

def decQualifiedCedarType (a b : QualifiedType) : Decidable (a = b) := by
  cases a <;> cases b
  case optional.optional a' b' => exact match decCedarType a' b' with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case required.required a' b' => exact match decCedarType a' b' with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  all_goals {
    apply isFalse
    intro h
    injection h
  }

def decProdAttrQualifiedCedarType (a b : Prod Attr QualifiedType) : Decidable (a = b) :=
  match a, b with
  | (a1, a2), (b1, b2) => match decEq a1 b1 with
    | isTrue h₀ => match decQualifiedCedarType a2 b2 with
      | isTrue h₁ => isTrue (by rw [h₀, h₁])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrQualifiedCedarTypeList (as bs : List (Prod Attr QualifiedType)) : Decidable (as = bs) :=
  match as, bs with
    | [], [] => isTrue rfl
    | _::_, [] => isFalse (by intro; contradiction)
    | [], _::_ => isFalse (by intro; contradiction)
    | a::as, b::bs =>
      match decProdAttrQualifiedCedarType a b with
      | isTrue h₁ => match decProdAttrQualifiedCedarTypeList as bs with
        | isTrue h₂ => isTrue (by rw [h₁, h₂])
        | isFalse _ => isFalse (by intro h; injection h; contradiction)
      | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decAttrQualifiedCedarTypeMap (as bs : Map Attr QualifiedType) : Decidable (as = bs) := by
  match as, bs with
  | Map.mk ma, Map.mk mb => exact match decProdAttrQualifiedCedarTypeList ma mb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

end

instance : DecidableEq CedarType := decCedarType

deriving instance DecidableEq for StandardSchemaEntry

def decEntitySchemaEntry (e₁ e₂: EntitySchemaEntry) : Decidable (e₁ = e₂) := by
  cases e₁ <;> cases e₂
  case standard.standard t₁ t₂ =>
    exact match decEq t₁ t₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case enum.enum l₁ l₂ =>
    exact match decEq l₁ l₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  all_goals {
    apply isFalse
    intro h
    injection h
  }

instance : DecidableEq EntitySchemaEntry := decEntitySchemaEntry

end Cedar.Validation
