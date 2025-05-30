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
import Cedar.SymCC.Data
import Cedar.SymCC.Result
import Cedar.Validation.Types

/-!
This file defines the types of Cedar Terms.  See `Term.lean` for the
definition of the Term language.
-/

namespace Cedar.SymCC

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

inductive TermPrimType where
  | bool
  | bitvec (n : Nat)
  | string
  | entity (ety : EntityType)
  | ext (xty : ExtType)

inductive TermType where
  | prim (pty : TermPrimType)
  | option (ty : TermType)
  | set (ty : TermType)
  | record (rty : Map Attr TermType)

abbrev TermType.bool : TermType := .prim .bool
abbrev TermType.bitvec (n : Nat) : TermType := .prim (.bitvec n)
abbrev TermType.string : TermType := .prim .string
abbrev TermType.entity (ety : EntityType) : TermType := .prim (.entity ety)
abbrev TermType.ext (xty : ExtType) : TermType := .prim (.ext xty)

abbrev TermType.tagFor (ety : EntityType) : TermType :=
  .record (EntityTag.mk (.entity ety) .string)

-- instance : Coe TermPrimType TermType where
--   coe pty := .prim pty

def TermType.isPrimType : TermType → Bool
  | .prim _ => true
  | _       => false

def TermType.isEntityType : TermType → Bool
  | .prim (.entity _) => true
  | _                 => false

def TermType.isBitVecType : TermType → Bool
  | .prim (.bitvec _) => true
  | _                 => false

def TermType.isRecordType : TermType → Bool
  | .record _ => true
  | _         => false

def TermType.isOptionType : TermType → Bool
  | .option _ => true
  | _         => false

def TermType.isOptionEntityType : TermType → Bool
  | .option (.entity _) => true
  | _                   => false

mutual

def TermType.ofType (ty : CedarType) : TermType :=
  match ty with
  | .bool _           => .prim (.bool)
  | .int              => .prim (.bitvec 64)
  | .string           => .prim (.string)
  | .entity ety       => .prim (.entity ety)
  | .ext xty          => .prim (.ext xty)
  | .set ty           => .set (ofType ty)
  | .record (.mk rty) => .record (.mk (ofRecordType rty))

def TermType.ofRecordType : List (Attr × QualifiedType) → List (Attr × TermType)
  | [] => []
  | (a, qty)::rty => (a, ofQualifiedType qty) :: ofRecordType rty

def TermType.ofQualifiedType : QualifiedType → TermType
  | .optional ty => .option (ofType ty)
  | .required ty => ofType ty

end

deriving instance Repr, Inhabited, DecidableEq for TermPrimType
deriving instance Repr, Inhabited for TermType

mutual

def TermType.hasDecEq (ty₁ ty₂ : TermType) : Decidable (ty₁ = ty₂) := by
  cases ty₁ <;> cases ty₂ <;>
  try { apply isFalse ; intro h ; injection h }
  case prim.prim v₁ v₂ =>
    exact match decEq v₁ v₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case option.option ty₁ ty₂ | set.set ty₁ ty₂ =>
    exact match TermType.hasDecEq ty₁ ty₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record rty₁ rty₂ =>
    cases rty₁ ; cases rty₂ ; rename_i rty₁ rty₂
    simp only [record.injEq, Map.mk.injEq]
    exact TermType.hasListProdDec rty₁ rty₂

def TermType.hasListProdDec (atys₁ atys₂ : List (Attr × TermType)) : Decidable (atys₁ = atys₂) :=
  match atys₁, atys₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a₁, ty₁) :: tl₁, (a₂, ty₂) :: tl₂ =>
    match decEq a₁ a₂, TermType.hasDecEq ty₁ ty₂ with
    | isTrue h₁, isTrue h₂ =>
        match TermType.hasListProdDec tl₁ tl₂ with
        | isTrue h₃ => isTrue (by subst h₁ h₂ h₃; rfl)
        | isFalse _ => isFalse (by simp; intros; assumption)
    | isFalse _, _ | _, isFalse _ => isFalse (by simp; intros; contradiction)

end

instance : DecidableEq TermType := TermType.hasDecEq

def TermPrimType.mkName : TermPrimType → String
  | .bool     => "bool"
  | .bitvec _ => "bitvec"
  | .string   => "string"
  | .entity _ => "entity"
  | .ext _    => "ext"

def TermType.mkName : TermType → String
  | .prim _   => "prim"
  | .option _ => "option"
  | .set _    => "set"
  | .record _ => "record"

end Cedar.SymCC
namespace Cedar.Validation

def ExtType.lt : ExtType → ExtType → Bool
  | .decimal, .ipAddr    => true
  | .decimal, .datetime  => true
  | .decimal, .duration  => true
  | .ipAddr, .datetime   => true
  | .ipAddr, .duration   => true
  | .datetime, .duration => true
  | _, _                 => false

instance : LT ExtType where
  lt := fun x y => ExtType.lt x y

instance ExtType.decLt (x y : ExtType) : Decidable (x < y) :=
  if h : ExtType.lt x y then isTrue h else isFalse h

end Cedar.Validation
namespace Cedar.SymCC

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

def TermPrimType.lt : TermPrimType → TermPrimType → Bool
  | .bitvec n₁, .bitvec n₂     => n₁ < n₂
  | .entity ety₁, .entity ety₂ => ety₁ < ety₂
  | .ext xty₁, .ext xty₂       => xty₁ < xty₂
  | ty₁, ty₂                   => ty₁.mkName < ty₂.mkName

instance : LT TermPrimType where
  lt := fun x y => TermPrimType.lt x y

instance TermPrimType.decLt (x y : TermPrimType) : Decidable (x < y) :=
  if h : TermPrimType.lt x y then isTrue h else isFalse h

mutual

def TermType.lt : TermType → TermType → Bool
  | .prim pty₁, .prim pty₂                 => pty₁ < pty₂
  | .option ty₁, .option ty₂               => TermType.lt ty₁ ty₂
  | .set ty₁, .set ty₂                     => TermType.lt ty₁ ty₂
  | .record (.mk rty₁), .record (.mk rty₂) => TermType.ltListProd rty₁ rty₂
  | ty₁, ty₂                               => ty₁.mkName < ty₂.mkName
termination_by ty _ => sizeOf ty

def TermType.ltListProd : List (Attr × TermType) → List (Attr × TermType) → Bool
  | [], []    => false
  | [], _::_  => true
  | _::_, []  => false
  | (a₁, ty₁) :: tl₁, (a₂, ty₂) :: tl₂ =>
    a₁ < a₂ || (a₁ = a₂ && TermType.lt ty₁ ty₂) ||
    (a₁ = a₂ && ty₁ = ty₂ && TermType.ltListProd tl₁ tl₂)
termination_by atys _ => sizeOf atys

end

instance : LT TermType where
  lt := fun x y => TermType.lt x y

instance TermType.decLt (x y : TermType) : Decidable (x < y) :=
  if h : TermType.lt x y then isTrue h else isFalse h

end Cedar.SymCC
