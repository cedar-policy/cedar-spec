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
import Cedar.SymCC.Op
import Init.Data.BitVec.Basic

/-!
This file defines the Cedar Term language, a strongly and simply typed IR to
which we compile Cedar expressions. The Term language has a straightforward
translation to SMTLib. It is designed to reduce the semantic gap between Cedar
and SMTLib, and to faciliate proofs of soundness and completeness of the Cedar
symbolic compiler.

Terms should _not_ be created directly using `Term` constructors. Instead, they
should be created using the factory functions defined in `Factory.lean`.
The factory functions check the types of their arguments, perform optimizations,
and ensure that applying them to well-formed terms results in well-formed terms.

See `TermType.lean` and `Op.lean` for definition of Term types and
operators.
-/

namespace Cedar.SymCC

open Cedar.Data
open Cedar.Spec

structure TermVar where
  id : String
  ty : TermType

inductive TermPrim : Type where
  | bool   : Bool → TermPrim
  | bitvec : ∀ {n}, BitVec n → TermPrim
  | string : String → TermPrim
  | entity : EntityUID → TermPrim
  | ext    : Ext → TermPrim

inductive Term : Type where
  | prim    : TermPrim → Term
  | var     : TermVar → Term
  | none    : TermType → Term
  | some    : Term → Term
  | set     : (elts: Set Term) → (eltsTy: TermType) → Term
  | record  : Map Attr Term → Term
  | app     : Op → (args: List Term) → (retTy: TermType) → Term

abbrev Term.bool (b : Bool) : Term := .prim (.bool b)
abbrev Term.bitvec {n : Nat} (bv : BitVec n) : Term := .prim (.bitvec bv)
abbrev Term.string (s : String) : Term := .prim (.string s)
abbrev Term.entity (uid : EntityUID) : Term := .prim (.entity uid)
abbrev Term.ext (xv : Ext) : Term := .prim (.ext xv)

def TermPrim.typeOf : TermPrim → TermType
  | .bool _           => .bool
  | .bitvec b         => .bitvec b.width
  | .string _         => .string
  | .entity uid       => .entity uid.ty
  | .ext (.decimal _) => .ext .decimal
  | .ext (.ipaddr _)  => .ext .ipAddr
  | .ext (.duration _) => .ext .duration
  | .ext (.datetime _) => .ext .datetime

def Term.typeOf : Term → TermType
  | .prim l       => l.typeOf
  | .var v        => v.ty
  | .none ty      => .option ty
  | .some t       => .option t.typeOf
  | .app _ _ ty   => ty
  | .set _ ty     => .set ty
  | .record (Map.mk atrs) =>
    .record (Map.mk (atrs.attach₃.map λ ⟨(a, t), _⟩ => (a, t.typeOf)))

def Term.isLiteral : Term → Bool
  | .prim _
  | .none _               => true
  | .some t               => t.isLiteral
  | .set (Set.mk ts) _    => ts.attach.all (λ ⟨t, _⟩ => t.isLiteral)
  | .record (Map.mk atrs) => atrs.attach₃.all (λ ⟨(_, t), _⟩ => t.isLiteral)
  | _                     => false

instance : Coe Bool Term where
  coe b := .prim (.bool b)

instance : Coe Int64 Term where
  coe i := .prim (.bitvec i.toBitVec)

instance : CoeOut (BitVec n) Term where
  coe b := .prim (.bitvec b)

instance : Coe String Term where
  coe s := .prim (.string s)

instance : Coe EntityUID Term where
  coe e := .prim (.entity e)

instance : Coe Ext Term where
  coe x := .prim (.ext x)

instance : Coe TermVar Term where
  coe v := .var v

deriving instance Repr, DecidableEq, Inhabited for TermVar
deriving instance Repr, DecidableEq, Inhabited for TermPrim
deriving instance Repr, Inhabited for Term

mutual

def Term.hasDecEq (t t' : Term) : Decidable (t = t') := by
  cases t <;> cases t' <;>
  try { apply isFalse ; intro h ; injection h }
  case prim.prim v₁ v₂ | none.none v₁ v₂ | var.var v₁ v₂ =>
    exact match decEq v₁ v₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case some.some t t' =>
    exact match Term.hasDecEq t t' with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case app.app op ts ty op' ts' ty' =>
    exact match decEq op op', Term.hasListDec ts ts', decEq ty ty' with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h₁, _, _ | _, isFalse h₁, _ | _, _, isFalse h₁ =>
      isFalse (by intro h₂; simp [h₁] at h₂)
  case set.set s ty s' ty' =>
    cases s ; cases s' ; rename_i s s'
    exact match decEq ty ty', Term.hasListDec s s' with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h₁, _ | _, isFalse h₁ => isFalse (by intro h₂; simp [h₁] at h₂)
  case record.record r r' =>
    cases r ; cases r' ; rename_i r r'
    simp only [record.injEq, Map.mk.injEq]
    exact Term.hasListProdDec r r'

def Term.hasListDec (ts₁ ts₂ : List Term) : Decidable (ts₁ = ts₂) :=
  match ts₁, ts₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | t₁ :: tl₁, t₂ :: tl₂ =>
    match Term.hasDecEq t₁ t₂ with
    | isTrue h₁ =>
        match Term.hasListDec tl₁ tl₂ with
        | isTrue h₂ => isTrue (by subst h₁ h₂; rfl)
        | isFalse _ => isFalse (by simp; intros; assumption)
    | isFalse _ => isFalse (by simp; intros; contradiction)

def Term.hasListProdDec (ats₁ ats₂ : List (Attr × Term)) : Decidable (ats₁ = ats₂) :=
  match ats₁, ats₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a₁, t₁) :: tl₁, (a₂, t₂) :: tl₂ =>
    match decEq a₁ a₂, Term.hasDecEq t₁ t₂ with
    | isTrue h₁, isTrue h₂ =>
        match Term.hasListProdDec tl₁ tl₂ with
        | isTrue h₃ => isTrue (by subst h₁ h₂ h₃; rfl)
        | isFalse _ => isFalse (by simp; intros; assumption)
    | isFalse _, _ | _, isFalse _ => isFalse (by simp; intros; contradiction)

end

instance : DecidableEq Term := Term.hasDecEq

def TermVar.lt (v v' : TermVar) : Bool :=
  v.id < v'.id || (v.id = v'.id && v.ty < v'.ty)

instance : LT TermVar where
  lt := fun x y => TermVar.lt x y

instance TermVar.decLt (x y : TermVar) : Decidable (x < y) :=
  if h : TermVar.lt x y then isTrue h else isFalse h

def TermPrim.mkName : TermPrim → String
  | .bool _   => "bool"
  | .bitvec _ => "bitvec"
  | .string _ => "string"
  | .entity _ => "entity"
  | .ext _    => "ext"

def TermPrim.lt : TermPrim → TermPrim → Bool
  | .bool b₁, .bool b₂         => b₁ < b₂
  | @TermPrim.bitvec n₁ bv₁,
    @TermPrim.bitvec n₂ bv₂    => n₁ < n₂ || (n₁ = n₂ && bv₁.toNat < bv₂.toNat)
  | .string s₁, .string s₂     => s₁ < s₂
  | .entity uid₁, .entity uid₂ => uid₁ < uid₂
  | .ext x₁, .ext x₂           => x₁ < x₂
  | p₁, p₂                     => p₁.mkName < p₂.mkName

instance : LT TermPrim where
  lt := fun x y => TermPrim.lt x y

instance TermPrim.decLt (x y : TermPrim) : Decidable (x < y) :=
  if h : TermPrim.lt x y then isTrue h else isFalse h

def Term.mkName : Term → String
  | .prim _     => "prim"
  | .var _      => "var"
  | .none _     => "none"
  | .some _     => "some"
  | .set _ _    => "set"
  | .record _   => "record"
  | .app _ _ _  => "app"

mutual

def Term.lt : Term → Term → Bool
  | .prim p₁, .prim p₂                     => p₁ < p₂
  | .var v₁, .var v₂                       => v₁ < v₂
  | .none ty₁, .none ty₂                   => ty₁ < ty₂
  | .some t₁, .some t₂                     => Term.lt t₁ t₂
  | .app o ts ty, .app o' ts' ty'          =>
    o < o' ||
    (o = o' && Term.ltList ts ts') ||
    (o = o' && ts = ts' && ty < ty')
  | .set (.mk ts₁) ty₁, .set (.mk ts₂) ty₂ =>
    ty₁ < ty₂ ||
    (ty₁ = ty₂ && Term.ltList ts₁ ts₂)
  | .record (.mk ats₁), .record (.mk ats₂) => Term.ltListProd ats₁ ats₂
  | t₁, t₂                                 => t₁.mkName < t₂.mkName
termination_by t _ => sizeOf t

def Term.ltList : List Term → List Term → Bool
  | [], []    => false
  | [], _::_  => true
  | _::_, []  => false
  | t₁ :: ts₁, t₂ :: ts₂ => Term.lt t₁ t₂ || (t₁ = t₂ && Term.ltList ts₁ ts₂)
termination_by ts _ => sizeOf ts

def Term.ltListProd : List (Attr × Term) → List (Attr × Term) → Bool
  | [], []    => false
  | [], _::_  => true
  | _::_, []  => false
  | (a₁, t₁) :: ts₁, (a₂, t₂) :: ts₂ =>
    a₁ < a₂ || (a₁ = a₂ && Term.lt t₁ t₂) ||
    (a₁ = a₂ && t₁ = t₂ && Term.ltListProd ts₁ ts₂)
termination_by ats _ => sizeOf ats

end

instance : LT Term where
  lt := fun x y => Term.lt x y

instance Term.decLt (x y : Term) : Decidable (x < y) :=
  if h : Term.lt x y then isTrue h else isFalse h

end Cedar.SymCC
