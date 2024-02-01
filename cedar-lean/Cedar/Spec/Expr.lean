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
import Cedar.Spec.ExtFun
import Cedar.Spec.Wildcard

/-! This file defines abstract syntax for Cedar expressions. -/

namespace Cedar.Spec

open Cedar.Data

----- Definitions -----

inductive Var where
  | principal
  | action
  | resource
  | context

inductive UnaryOp where
  | not
  | neg
  | mulBy (i : Int64)
  | like (p : Pattern)
  | is (ety : EntityType)

inductive BinaryOp where
  | eq
  | mem -- represents Cedar's in operator
  | less
  | lessEq
  | add
  | sub
  | contains
  | containsAll
  | containsAny

/- the α here represents the type of subexpressions -/
inductive Expr α where
  | lit (p : Prim)
  | var (v : Var)
  | ite (cond: α) (thenExpr : α) (elseExpr : α)
  | and (a : α) (b : α)
  | or (a : α) (b : α)
  | unaryApp (op : UnaryOp) (expr: α)
  | binaryApp (op : BinaryOp) (a : α) (b : α)
  | getAttr (expr : α) (attr : Attr)
  | hasAttr (expr : α) (attr : Attr)
  | set (ls : List α)
  | record (map : List (Attr × α))
  | call (xfn : ExtFun) (args : List α)

/- the problem with this one is that `Expr α` still never has an `unknown` case, for any α
/- the α here represents the type of subexpressions -/
inductive Expr : (α : Type) -> Type where
  | lit (p : Prim) : Expr α
  | var (v : Var) : Expr α
  | ite (cond: Expr α) (thenExpr : Expr α) (elseExpr : Expr α) : Expr α
  | and (a : Expr α) (b : Expr α) : Expr α
  | or (a : Expr α) (b : Expr α) : Expr α
  | unaryApp (op : UnaryOp) (expr: Expr α) : Expr α
  | binaryApp (op : BinaryOp) (a : Expr α) (b : Expr α) : Expr α
  | getAttr (expr : Expr α) (attr : Attr) : Expr α
  | hasAttr (expr : Expr α) (attr : Attr) : Expr α
  | set (ls : List (Expr α)) : Expr α
  | record (map : List (Attr × Expr α)) : Expr α
  | call (xfn : ExtFun) (args : List (Expr α)) : Expr α
-/

----- Derivations -----

deriving instance Repr, DecidableEq, Inhabited for Var
deriving instance Repr, DecidableEq, Inhabited for UnaryOp
deriving instance Repr, DecidableEq, Inhabited for BinaryOp
-- deriving instance Repr, Inhabited for Expr

mutual

-- We should be able to get rid of this manual deriviation eventually.
-- There is work in progress on making these mutual derivations automatic.

def decExpr [DecidableEq α] (x y : Expr α) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case lit.lit x₁ y₁ | var.var x₁ y₁ =>
    exact match decEq x₁ y₁ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ite.ite x₁ x₂ x₃ y₁ y₂ y₃ =>
    exact match decEq x₁ y₁, decEq x₂ y₂, decEq x₃ y₃ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case and.and x₁ x₂ y₁ y₂ | or.or x₁ x₂ y₁ y₂ =>
    exact match decEq x₁ y₁, decEq x₂ y₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unaryApp.unaryApp o x₁ o' y₁ =>
    exact match decEq o o', decEq x₁ y₁ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case binaryApp.binaryApp o x₁ x₂ o' y₁ y₂ =>
    exact match decEq o o', decEq x₁ y₁, decEq x₂ y₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case getAttr.getAttr x₁ a y₁ a' | hasAttr.hasAttr x₁ a y₁ a' =>
    exact match decEq x₁ y₁, decEq a a' with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set xs ys =>
    exact match decEq xs ys with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record axs ays =>
    exact match decEq axs ays with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case call.call f xs f' ys =>
    exact match decEq f f', decEq xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrExprList [DecidableEq α] (axs ays : List (Attr × (Expr α))) : Decidable (axs = ays) :=
  match axs, ays with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a, x)::axs, (a', y)::ays =>
    match decEq a a', decExpr x y, decProdAttrExprList axs ays with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

def decExprList [DecidableEq α] (xs ys : List (Expr α)) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | x::xs, y::ys =>
    match decExpr x y, decExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)

end

instance [DecidableEq α] : DecidableEq (Expr α) := decExpr

end Cedar.Spec
