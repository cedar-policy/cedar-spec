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

import Cedar.Data
import Cedar.Spec.Ext

/-! This file defines Cedar values and results. -/

namespace Cedar.Spec

open Cedar.Data

----- Definitions -----

inductive Error where
  | entityDoesNotExist
  | attrDoesNotExist
  | tagDoesNotExist
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
  | .prim (.entityUID uid) => .ok uid
  | _ => .error Error.typeError

def Value.asSet : Value → Result (Data.Set Value)
  | .set s => .ok s
  | _ => .error Error.typeError

def Value.asBool : Value → Result Bool
  | .prim (.bool b) => .ok b
  | _ => .error Error.typeError

def Value.asString : Value →  Result String
  | .prim (.string s) => .ok s
  | _ => .error Error.typeError

def Value.asInt : Value →  Result Int64
  | .prim (.int i) => .ok i
  | _ => .error Error.typeError

def Result.as {α} (β) [Coe α (Result β)] : Result α → Result β
  | .ok v    => v
  | .error e => .error e

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

def decValue (v₁ v₂ : Value) : Decidable (v₁ = v₂) := by
  cases v₁ <;> cases v₂ <;>
  try { apply isFalse ; intro h ; injection h }
  case prim.prim w₁ w₂ | ext.ext w₁ w₂ =>
    exact match decEq w₁ w₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set s₁ s₂ =>
    cases s₁ ; cases s₂ ; rename_i s₁ s₂
    exact match decValueList s₁ s₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse h₁ => isFalse (by intro h₂; simp [h₁] at h₂)
  case record.record r₁ r₂ =>
    cases r₁ ; cases r₂ ; rename_i r₁ r₂
    exact match decProdAttrValueList r₁ r₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse h₁ => isFalse (by intro h₂; simp [h₁] at h₂)

def decValueList (vs₁ vs₂ : List Value) : Decidable (vs₁ = vs₂) :=
  match vs₁, vs₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | v₁ :: vs₁, v₂ :: vs₂ =>
    match decValue v₁ v₂, decValueList vs₁ vs₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _ , _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrValueList (avs₁ avs₂ : List (Attr × Value)) : Decidable (avs₁ = avs₂):=
  match avs₁, avs₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a₁, v₁) :: vs₁, (a₂, v₂) :: vs₂ =>
    match decEq a₁ a₂, decValue v₁ v₂, decProdAttrValueList vs₁ vs₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

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
  | .bool b₁, .bool b₂ => b₁ < b₂
  | .int i₁, .int i₂ => i₁ < i₂
  | .string s₁, .string s₂ => s₁ < s₂
  | .entityUID uid₁, .entityUID uid₂ => uid₁ < uid₂
  | .bool _, .int _ => true
  | .bool _, .string _ => true
  | .bool _, .entityUID _ => true
  | .int _, .string _ => true
  | .int _, .entityUID _ => true
  | .string _, .entityUID _ => true
  | _, _ => false

instance : LT Prim where
  lt := fun x y => Prim.lt x y

instance Prim.decLt (a b : Prim) : Decidable (a < b) :=
  if h : Prim.lt a b then isTrue h else isFalse h

mutual
def Value.lt : Value → Value → Bool
  | .prim p₁, .prim p₂ => p₁ < p₂
  | .set (.mk vs₁), .set (.mk vs₂) => Values.lt vs₁ vs₂
  | .record (.mk avs₁), .record (.mk avs₂) => ValueAttrs.lt avs₁ avs₂
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

def Values.lt : List Value → List Value → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | v₁ :: vs₁, v₂ :: vs₂ => Value.lt v₁ v₂ || (v₁ = v₂ && Values.lt vs₁ vs₂)

def ValueAttrs.lt : List (Attr × Value) → List (Attr × Value) → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | (a₁, v₁) :: avs₁, (a₂, v₂) :: avs₂ =>
    a₁ < a₂ || (a₁ = a₂ && Value.lt v₁ v₂) ||
    (a₁ = a₂ && v₁ = v₂ && ValueAttrs.lt avs₁ avs₂)
end

instance : LT Value where
  lt := fun x y => Value.lt x y

instance Value.decLt (a b : Value) : Decidable (a < b) :=
  if h : Value.lt a b then isTrue h else isFalse h

end Cedar.Spec
