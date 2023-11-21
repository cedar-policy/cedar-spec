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

inductive Expr where
  | lit (p : Prim)
  | var (v : Var)
  | ite (cond : Expr) (thenExpr : Expr) (elseExpr : Expr)
  | and (a : Expr) (b : Expr)
  | or (a : Expr) (b : Expr)
  | unaryApp (op : UnaryOp) (expr : Expr)
  | binaryApp (op : BinaryOp) (a : Expr) (b : Expr)
  | getAttr (expr : Expr) (attr : Attr)
  | hasAttr (expr : Expr) (attr : Attr)
  | set (ls : List Expr)
  | record (map : List (Prod Attr Expr))
  | call (xfn : ExtFun) (args : List Expr)

----- Derivations -----

deriving instance Repr, DecidableEq, Inhabited for Var
deriving instance Repr, DecidableEq, Inhabited for UnaryOp
deriving instance Repr, DecidableEq, Inhabited for BinaryOp
deriving instance Repr, Inhabited for Expr

mutual

-- We should be able to get rid of this manual deriviation eventually.
-- There is work in progress on making these mutual derivations automatic.

def decExpr (a b : Expr) : Decidable (a = b) := by
  cases a <;> cases b
  case lit.lit pa pb => exact match decEq pa pb with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case var.var va vb => exact match decEq va vb with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ite.ite c1 t1 e1 c2 t2 e2 => exact match decExpr c1 c2 with
    | isTrue h₁ => match decExpr t1 t2 with
      | isTrue h₂ => match decExpr e1 e2 with
        | isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
        | isFalse _ => isFalse (by intro h; injection h; contradiction)
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ =>  isFalse (by intro h; injection h; contradiction)
  case and.and a1 a2 b1 b2 => exact match decExpr a1 b1 with
    | isTrue h₁ => match decExpr a2 b2 with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case or.or a1 a2 b1 b2 => exact match decExpr a1 b1 with
    | isTrue h₁ => match decExpr a2 b2 with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unaryApp.unaryApp op1 e1 op2 e2 => exact match decEq op1 op2 with
    | isTrue h₁ => match decExpr e1 e2 with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case binaryApp.binaryApp op1 a1 b1 op2 a2 b2 => exact match decEq op1 op2 with
    | isTrue h₁ => match decExpr a1 a2 with
      | isTrue h₂ => match decExpr b1 b2 with
        | isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
        | isFalse _ => isFalse (by intro h; injection h; contradiction)
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case getAttr.getAttr e1 a1 e2 a2 => exact match decExpr e1 e2 with
    | isTrue h₁ => match decEq a1 a2 with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case hasAttr.hasAttr e1 a1 e2 a2 => exact match decExpr e1 e2 with
    | isTrue h₁ => match decEq a1 a2 with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set l1 l2 => exact match decExprList l1 l2 with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record r1 r2 => exact match decProdAttrExprList r1 r2 with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case call.call n1 a1 n2 a2 => exact match decEq n1 n2 with
    | isTrue h₁ => match decExprList a1 a2 with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  all_goals apply isFalse; intro h; injection h

def decProdAttrExpr (a b : Prod Attr Expr) : Decidable (a = b) :=
  match a, b with
  | (aa, ae), (ba,be) => match decEq aa ba with
    | isTrue h₁ => match decExpr ae be with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrExprList (as bs : List (Prod Attr Expr)) : Decidable (as = bs) :=
  match as, bs with
  | [], [] => isTrue rfl
  | _::_, [] => isFalse (by intro; contradiction)
  | [], _::_ => isFalse (by intro; contradiction)
  | a::as, b::bs => match decProdAttrExpr a b with
    | isTrue h₁ => match decProdAttrExprList as bs with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decExprList (as bs : List Expr) : Decidable (as = bs) :=
  match as, bs with
  | [], [] => isTrue rfl
  | _::_, [] => isFalse (by intro; contradiction)
  | [], _::_ => isFalse (by intro; contradiction)
  | a::as, b::bs =>
    match decExpr a b with
    | isTrue h₁ => match decExprList as bs with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
end

instance : DecidableEq Expr := decExpr

end Cedar.Spec
