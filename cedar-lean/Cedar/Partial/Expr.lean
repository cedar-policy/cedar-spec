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
import Cedar.Spec.Expr

/-! This file defines abstract syntax for Cedar partial expressions. -/

namespace Cedar.Partial

open Cedar.Data
open Cedar.Spec (Attr BinaryOp ExtFun Prim UnaryOp Var)

-- Unknowns are currently represented by a string name
abbrev Unknown := String

/--
  Identical to `Spec.Expr` except that it has an `unknown` case, and the recursive
  elements are also all `Partial.Expr` instead of `Spec.Expr`
-/
inductive Expr where
  | lit (p : Prim)
  | var (v : Var)
  | ite (cond : Partial.Expr) (thenExpr : Partial.Expr) (elseExpr : Partial.Expr)
  | and (a : Partial.Expr) (b : Partial.Expr)
  | or (a : Partial.Expr) (b : Partial.Expr)
  | unaryApp (op : UnaryOp) (expr : Partial.Expr)
  | binaryApp (op : BinaryOp) (a : Partial.Expr) (b : Partial.Expr)
  | getAttr (expr : Partial.Expr) (attr : Attr)
  | hasAttr (expr : Partial.Expr) (attr : Attr)
  | set (ls : List Partial.Expr)
  | record (map : List (Attr × Partial.Expr))
  | call (xfn : ExtFun) (args : List Partial.Expr)
  | unknown (u : Unknown)

deriving instance Repr, Inhabited for Expr

/--
  A version of `Partial.Expr`, but only allows "restricted expressions" -- no
  vars, no expressions that require entity data to evaluate, no operators at all,
  just literals, unknowns, extension values, and sets/records of those things
-/
inductive RestrictedExpr where
  | lit (p : Prim)
  | set (ls : List Partial.RestrictedExpr)
  | record (map : List (Attr × Partial.RestrictedExpr))
  | call (xfn : ExtFun) (args : List Spec.Value) -- this requires that all arguments to extension functions in Partial.RestrictedExpr are concrete. TODO do we need to relax this?
  | unknown (u : Unknown)

deriving instance Repr, Inhabited for RestrictedExpr

mutual

-- We should be able to get rid of this manual deriviation eventually.
-- There is work in progress on making these mutual derivations automatic.

def decPartialExpr (x y : Partial.Expr) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case lit.lit x₁ y₁ | var.var x₁ y₁ | unknown.unknown x₁ y₁ =>
    exact match decEq x₁ y₁ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ite.ite x₁ x₂ x₃ y₁ y₂ y₃ =>
    exact match decPartialExpr x₁ y₁, decPartialExpr x₂ y₂, decPartialExpr x₃ y₃ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case and.and x₁ x₂ y₁ y₂ | or.or x₁ x₂ y₁ y₂ =>
    exact match decPartialExpr x₁ y₁, decPartialExpr x₂ y₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unaryApp.unaryApp o x₁ o' y₁ =>
    exact match decEq o o', decPartialExpr x₁ y₁ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case binaryApp.binaryApp o x₁ x₂ o' y₁ y₂ =>
    exact match decEq o o', decPartialExpr x₁ y₁, decPartialExpr x₂ y₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case getAttr.getAttr x₁ a y₁ a' | hasAttr.hasAttr x₁ a y₁ a' =>
    exact match decPartialExpr x₁ y₁, decEq a a' with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set xs ys =>
    exact match decPartialExprList xs ys with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record axs ays =>
    exact match decProdAttrPartialExprList axs ays with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case call.call f xs f' ys =>
    exact match decEq f f', decPartialExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrPartialExprList (axs ays : List (Attr × Partial.Expr)) : Decidable (axs = ays) :=
  match axs, ays with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a, x)::axs, (a', y)::ays =>
    match decEq a a', decPartialExpr x y, decProdAttrPartialExprList axs ays with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

def decPartialExprList (xs ys : List Partial.Expr) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | x::xs, y::ys =>
    match decPartialExpr x y, decPartialExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
end

instance : DecidableEq Partial.Expr := decPartialExpr

end Cedar.Partial

namespace Cedar.Spec

open Cedar.Data

def Value.asPartialExpr : Spec.Value → Partial.Expr
  | .prim p => .lit p
  | .set (Set.mk elts) => .set (elts.map₁ λ ⟨v, _⟩ => v.asPartialExpr)
  | .record m => .record (m.kvs.attach₃.map λ ⟨(k, v), _⟩ => (k, v.asPartialExpr))
  | .ext (.decimal d) => .call ExtFun.decimal [Partial.Expr.lit (.string (toString d))]
  | .ext (.ipaddr ip) => .call ExtFun.ip [Partial.Expr.lit (.string (toString ip))]

def Value.asPartialRestrictedExpr : Spec.Value → Partial.RestrictedExpr
  | .prim p => .lit p
  | .set s => .set (s.elts.map₁ λ ⟨v, _⟩ =>
      have := Set.sizeOf_lt_of_elts (s := s)
      v.asPartialRestrictedExpr)
  | .record m => .record (m.kvs.attach₂.map λ ⟨(k, v), h₁⟩ => (k, v.asPartialRestrictedExpr))
  | .ext (.decimal d) => .call ExtFun.decimal [Value.prim (.string (toString d))]
  | .ext (.ipaddr ip) => .call ExtFun.ip [Value.prim (.string (toString ip))]
decreasing_by all_goals sorry

def Expr.asPartialExpr : Spec.Expr → Partial.Expr
  | .lit p => .lit p
  | .var v => .var v
  | .ite x₁ x₂ x₃ =>
      .ite x₁.asPartialExpr x₂.asPartialExpr x₃.asPartialExpr
  | .and x₁ x₂ =>
      .and x₁.asPartialExpr x₂.asPartialExpr
  | .or x₁ x₂ =>
      .or x₁.asPartialExpr x₂.asPartialExpr
  | .unaryApp op x₁ =>
      .unaryApp op x₁.asPartialExpr
  | .binaryApp op x₁ x₂ =>
      .binaryApp op x₁.asPartialExpr x₂.asPartialExpr
  | .getAttr x₁ attr =>
      .getAttr x₁.asPartialExpr attr
  | .hasAttr x₁ attr =>
      .hasAttr x₁.asPartialExpr attr
  | .set xs =>
      .set (xs.map₁ λ ⟨x, _⟩ => x.asPartialExpr)
  | .record attrs =>
      .record (attrs.attach₂.map λ ⟨(k, v), _⟩ => (k, v.asPartialExpr))
  | .call xfn args =>
      .call xfn (args.map₁ λ ⟨x, _⟩ => x.asPartialExpr)

instance : Coe Spec.Expr Partial.Expr where
  coe := Spec.Expr.asPartialExpr

end Cedar.Spec

namespace Cedar.Partial

def RestrictedExpr.asPartialExpr : Partial.RestrictedExpr → Partial.Expr
  | .lit p => .lit p
  | .set xs => .set (xs.map₁ λ ⟨x, _⟩ => x.asPartialExpr)
  | .record attrs => .record (attrs.attach₂.map λ ⟨(k, v), _⟩ => (k, v.asPartialExpr))
  | .call xfn args => .call xfn (args.map Spec.Value.asPartialExpr)
  | .unknown u => .unknown u

/--
  Is this a literal "unknown".
  (Doesn't check if it recursively contains unknowns; for that, use
  `Partial.Expr.containsUnknown`)
-/
def Expr.isUnknown (x : Partial.Expr) : Bool :=
  match x with
  | .unknown _ => true
  | _ => false

/--
  Get a list of all the subexpressions of a given expression.
  Every expression is also a subexpression of itself.
-/
def Expr.subexpressions (x : Partial.Expr) : List Partial.Expr :=
  match x with
  | .lit _ => [x]
  | .var _ => [x]
  | .ite x₁ x₂ x₃ => [x] ++ x₁.subexpressions ++ x₂.subexpressions ++ x₃.subexpressions
  | .and x₁ x₂ => [x] ++ x₁.subexpressions ++ x₂.subexpressions
  | .or x₁ x₂ => [x] ++ x₁.subexpressions ++ x₂.subexpressions
  | .unaryApp _ x₁ => [x] ++ x₁.subexpressions
  | .binaryApp _ x₁ x₂ => [x] ++ x₁.subexpressions ++ x₂.subexpressions
  | .getAttr x₁ _ => [x] ++ x₁.subexpressions
  | .hasAttr x₁ _ => [x] ++ x₁.subexpressions
  | .set xs => [x] ++ List.join (xs.map₁ λ ⟨x, _⟩ => x.subexpressions)
  | .record pairs => [x] ++ List.join (pairs.attach₂.map λ ⟨(_, x₁), _⟩ => x₁.subexpressions)
  | .call _ xs => [x] ++ List.join (xs.map₁ λ ⟨x, _⟩ => x.subexpressions)
  | .unknown _ => [x]

/--
  Does a given Partial.Expr contain an Unknown, perhaps recursively
-/
def Expr.containsUnknown (x : Partial.Expr) : Bool :=
  x.subexpressions.any Expr.isUnknown

/--
  Is a given Partial.Expr fully concrete (no Unknowns even recursively)
-/
def Expr.fullyConcrete (x : Partial.Expr) : Bool :=
  ¬ x.containsUnknown

/--
  Is this a literal "unknown".
  (Doesn't check if it recursively contains unknowns; for that, use
  `Partial.RestrictedExpr.containsUnknown`)
-/
def RestrictedExpr.isUnknown (x : Partial.RestrictedExpr) : Bool :=
  match x with
  | .unknown _ => true
  | _ => false

/--
  Get a list of all the subexpressions of a given Partial.RestrictedExpr.
  Every expression is also a subexpression of itself.
-/
def RestrictedExpr.subexpressions (x : Partial.RestrictedExpr) : List Partial.RestrictedExpr :=
  match x with
  | .lit _ => [x]
  | .set xs => [x] ++ List.join (xs.map₁ λ ⟨x, _⟩ => x.subexpressions)
  | .record pairs => [x] ++ List.join (pairs.attach₂.map λ ⟨(_, x₁), _⟩ => x₁.subexpressions)
  | .call _ xs => [x] -- in Partial.RestrictedExpr, call arguments are values and cannot contain unknowns
  | .unknown _ => [x]

/--
  Does a given Partial.RestrictedExpr contain an Unknown, perhaps recursively
-/
def RestrictedExpr.containsUnknown (x : Partial.RestrictedExpr) : Bool :=
  x.subexpressions.any Partial.RestrictedExpr.isUnknown

/--
  any expression is a subexpression of itself
-/
theorem Expr.subexpression_refl {x : Partial.Expr} :
  x ∈ x.subexpressions
:= by
  unfold Partial.Expr.subexpressions
  cases x <;> simp

/--
  any expression is a subexpression of itself
-/
theorem RestrictedExpr.subexpression_refl {x : Partial.RestrictedExpr} :
  x ∈ x.subexpressions
:= by
  unfold Partial.RestrictedExpr.subexpressions
  cases x <;> simp

/--
  `isUnknown` remains true across conversions
  TODO: this is duplicated in GetAttr.lean
-/
theorem isUnknown_asPartialExpr {x : Partial.RestrictedExpr} :
  x.isUnknown ↔ x.asPartialExpr.isUnknown
:= by
  unfold Partial.RestrictedExpr.asPartialExpr Partial.RestrictedExpr.isUnknown Partial.Expr.isUnknown
  cases x <;> simp

/--
  `containsUnknown` remains true across conversions
  TODO: this is duplicated in GetAttr.lean
-/
theorem containsUnknown_asPartialExpr {x : Partial.RestrictedExpr} :
  x.containsUnknown ↔ x.asPartialExpr.containsUnknown
:= by
  unfold Partial.RestrictedExpr.asPartialExpr Partial.RestrictedExpr.containsUnknown Partial.Expr.containsUnknown Partial.RestrictedExpr.subexpressions Partial.Expr.subexpressions
  cases x <;> simp [isUnknown_asPartialExpr, Partial.RestrictedExpr.asPartialExpr]
  all_goals sorry

/--
  `subexpressions` is preserved across conversions
-/
theorem subexpressions_asPartialExpr {x₁ x₂ : Partial.RestrictedExpr} :
  x₁ ∈ x₂.subexpressions → x₁.asPartialExpr ∈ x₂.asPartialExpr.subexpressions
:= by
  sorry
