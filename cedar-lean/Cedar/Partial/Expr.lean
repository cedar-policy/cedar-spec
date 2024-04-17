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
