/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Data
import Cedar.Spec.Ext

/-! This file defines Cedar values and results. -/

namespace Cedar.Spec

open Cedar.Data
open Cedar.Spec.Ext
open Except

----- Definitions -----

inductive Error where
  | entityDoesNotExist
  | attrDoesNotExist
  | typeError
  | arithBoundsError
  | extensionError

abbrev Result (α) := Except Error α

abbrev Id := String

structure Name where
  id : Id
  path : List Id

abbrev EntityType := Name

structure EntityUID where
  ty : EntityType
  eid : String

inductive Prim where
  | bool (b : Bool)
  | int (i : Int64)
  | string (s : String)
  | entityUID (uid : EntityUID)

abbrev Attr := String

inductive Value where
  | prim (p : Prim)
  | set (s : Set Value)
  | record (m : Map Attr Value)
  | ext (x : Ext)

----- Coercions -----

def Value.asEntityUID : Value → Result EntityUID
  | .prim (.entityUID uid) => ok uid
  | _ => error Error.typeError

def Value.asSet : Value → Result (Data.Set Value)
  | .set s => ok s
  | _ => error Error.typeError

def Value.asBool : Value → Result Bool
  | .prim (.bool b) => ok b
  | _ => error Error.typeError

def Value.asString : Value →  Result String
  | .prim (.string s) => ok s
  | _ => error Error.typeError

def Value.asInt : Value →  Result Int64
  | .prim (.int i) => ok i
  | _ => error Error.typeError

def Result.as {α} (β) [Coe α (Result β)] : Result α → Result β
  | ok v    => v
  | error e => error e

instance : Coe Bool Value where
  coe b := .prim (.bool b)

instance : Coe Int64 Value where
  coe i := .prim (.int i)

instance : Coe String Value where
  coe s := .prim (.string s)

instance : Coe EntityUID Value where
  coe e := .prim (.entityUID e)

instance : Coe Prim Value where
  coe p := .prim p

instance : Coe Ext Value where
  coe x := .ext x

instance : Coe (Data.Set Value) Value where
  coe s := .set s

instance : Coe (Map Attr Value) Value where
  coe r := .record r

instance : Coe Value (Result Bool) where
  coe v := v.asBool

instance : Coe Value (Result Int64) where
  coe v := v.asInt

instance : Coe Value (Result String) where
  coe v := v.asString

instance : Coe Value (Result EntityUID) where
  coe v := v.asEntityUID

instance : Coe Value (Result (Data.Set Value)) where
  coe v := v.asSet

----- Derivations -----

deriving instance Repr, DecidableEq, BEq for Except
deriving instance Repr, DecidableEq for Error
deriving instance Repr, DecidableEq, Inhabited, Lean.ToJson for Name
deriving instance Repr, DecidableEq, Inhabited for EntityType
deriving instance Repr, DecidableEq, Inhabited for EntityUID
deriving instance Repr, DecidableEq, Inhabited for Prim
deriving instance Repr, Inhabited for Value

mutual

def decValue (a b : Value) : Decidable (a = b) := by
  cases a <;> cases b
  case prim.prim pa pb => exact match decEq pa pb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set sa sb => exact match decValueSet sa sb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record ra rb => exact match decValueRecord ra rb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ext.ext xa xb => exact match decEq xa xb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  all_goals {
    apply isFalse
    intro h
    injection h
  }

def decValueList (as bs : List Value) : Decidable (as = bs) :=
  match as, bs with
  | [], [] => isTrue rfl
  | _::_, [] => isFalse (by intro; contradiction)
  | [], _::_ => isFalse (by intro; contradiction)
  | a::as, b::bs =>
    match decValue a b with
    | isTrue h₁ => match decValueList as bs with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrValue (as bs : Attr × Value) : Decidable (as = bs) :=
  match as, bs with
  | (a1, a2), (b1, b2) => match decEq a1 b1 with
    | isTrue h₀ => match decValue a2 b2 with
      | isTrue h₁ => isTrue (by rw [h₀, h₁])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrValueList (as bs : List (Attr × Value)) : Decidable (as = bs) :=
  match as, bs with
  | [], [] => isTrue rfl
  | _::_, [] => isFalse (by intro; contradiction)
  | [], _::_ => isFalse (by intro; contradiction)
  | a::as, b::bs =>
    match decProdAttrValue a b with
    | isTrue h₁ => match decProdAttrValueList as bs with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decValueSet (a b : Set Value) : Decidable (a = b) := by
  match a, b with
  | .mk la, .mk lb => exact match decValueList la lb with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  done

def decValueRecord (as bs : Map Attr Value) : Decidable (as = bs) := by
  match as, bs with
  | .mk ma, .mk mb => exact match decProdAttrValueList ma mb with
  | isTrue h => isTrue (by rw [h])
  | isFalse _ => isFalse (by intro h; injection h; contradiction)
end

instance : DecidableEq Value :=
  decValue

def Name.lt (a b : Name) : Bool :=
  (a.id :: a.path) < (b.id :: b.path)

instance : LT Name where
  lt a b := Name.lt a b

instance Name.decLt (a b : Name) : Decidable (a < b) :=
  if h : Name.lt a b then isTrue h else isFalse h

def EntityUID.lt (a b : EntityUID) : Bool :=
  (a.ty < b.ty) ∨ (a.ty = b.ty ∧ a.eid < b.eid)

instance : LT EntityUID where
  lt a b := EntityUID.lt a b

instance EntityUID.decLt (a b : EntityUID) : Decidable (a < b) :=
  if h : EntityUID.lt a b then isTrue h else isFalse h

def Prim.lt : Prim → Prim → Bool
  | .bool nb, .bool mb => nb < mb
  | .int ni, .int mi => ni < mi
  | .string ns, .string ms => ns < ms
  | .entityUID nuid, .entityUID muid => nuid < muid
  | .bool _, .int _ => true
  | .bool _, .string _ => true
  | .bool _, .entityUID _ => true
  | .int _, .string _ => true
  | .int _, .entityUID _ => true
  | .string _, .entityUID _ => true
  | _,_ => false

instance : LT Prim where
lt := fun x y => Prim.lt x y

instance Prim.decLt (a b : Prim) : Decidable (a < b) :=
if  h : Prim.lt a b then isTrue h else isFalse h

mutual
def Value.lt : Value → Value → Bool
  | .prim x, .prim y => x < y
  | .set (.mk lx), .set (.mk ly) => Values.lt lx ly lx.length
  | .record (.mk lx), .record (.mk ly) => ValueAttrs.lt lx ly lx.length
  | .ext x, .ext y => x < y
  | .prim _, .set _ => true
  | .prim _, .record _ => true
  | .prim _, .ext _ => true
  | .set _, .record _ => true
  | .set _, .ext _ => true
  | .set _, .prim _ => false
  | .record _, .ext _ => true
  | .record _, .prim _ => false
  | .record _, .set _ => false
  | .ext _, .prim _ => false
  | .ext _, .set _ => false
  | .ext _, .record _ => false

def Values.lt (n m : List Value) (i : Nat): Bool :=
  match n, m with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | n::ns, m::ms => Value.lt n m || (n = m && Values.lt ns ms (i-1))

def ValueAttrs.lt (n m : List (Attr × Value)) (i : Nat) : Bool :=
  match n, m with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | (na, nv)::ns, (ma, mv)::ms =>
    na < ma || (na = ma && Value.lt nv mv) ||
    (na = ma && nv = mv && ValueAttrs.lt ns ms (i-1))
end
termination_by
Value.lt as₁ as₂ => (sizeOf as₁, 0)
Values.lt as₁ as₂ i => (sizeOf as₁, as₁.length - i)
ValueAttrs.lt as₁ as₂ i => (sizeOf as₁, as₁.length - i)

instance : LT Value where
  lt := fun x y => Value.lt x y

instance Value.decLt (n m : Value) : Decidable (n < m) :=
if h : Value.lt n m then isTrue h else isFalse h

end Cedar.Spec
