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
import Cedar.Spec.Expr

/-! This file defines abstract syntax for Cedar expressions. -/

namespace Cedar.Spec

open Cedar.Data

/--
  Identical to `Expr` except that it has an `unknown` case, and the recursive
  elements are also all `PartialExpr` instead of `Expr`
-/
inductive PartialExpr where
  | lit (p : Prim)
  | var (v : Var)
  | ite (cond : PartialExpr) (thenExpr : PartialExpr) (elseExpr : PartialExpr)
  | and (a : PartialExpr) (b : PartialExpr)
  | or (a : PartialExpr) (b : PartialExpr)
  | unaryApp (op : UnaryOp) (expr : PartialExpr)
  | binaryApp (op : BinaryOp) (a : PartialExpr) (b : PartialExpr)
  | getAttr (expr : PartialExpr) (attr : Attr)
  | hasAttr (expr : PartialExpr) (attr : Attr)
  | set (ls : List PartialExpr)
  | record (map : List (Attr × PartialExpr))
  | call (xfn : ExtFun) (args : List PartialExpr)
  | unknown (name : String)

deriving instance Repr, Inhabited for PartialExpr

def Value.asPartialExpr (v : Value) : PartialExpr :=
  match v with
  | .prim p => .lit p
  | .set s => .set (s.elts.map Value.asPartialExpr)
  | .record m => .record (m.kvs.map fun (k, v) => (k, v.asPartialExpr))
  | .ext (.decimal d) => .call ExtFun.decimal [PartialExpr.lit (.string d.unParse)]
  | .ext (.ipaddr ip) => .call ExtFun.ip [PartialExpr.lit (.string (Cedar.Spec.Ext.IPAddr.unParse ip))]
decreasing_by all_goals sorry

/--
  A version of `PartialExpr`, but only allows "restricted expressions" -- no
  vars, no expressions that require entity data to evaluate, no operators at all,
  just literals, unknowns, extension values, and sets/records of those things
-/
inductive RestrictedPartialExpr where
  | lit (p : Prim)
  | set (ls : List RestrictedPartialExpr)
  | record (map : List (Attr × RestrictedPartialExpr))
  | call (xfn : ExtFun) (args : List Value) -- this requires that all arguments to extension functions in RestrictedPartialExpr are concrete. TODO do we need to relax this?
  | unknown (name : String)

deriving instance Repr, Inhabited for RestrictedPartialExpr

def Value.asRestrictedPartialExpr (v : Value) : RestrictedPartialExpr :=
  match v with
  | .prim p => .lit p
  | .set s => .set (s.elts.map Value.asRestrictedPartialExpr)
  | .record m => .record (m.kvs.map λ (k, v) => (k, v.asRestrictedPartialExpr))
  | .ext (.decimal d) => .call ExtFun.decimal [Value.prim (.string d.unParse)]
  | .ext (.ipaddr ip) => .call ExtFun.ip [Value.prim (.string (Cedar.Spec.Ext.IPAddr.unParse ip))]
decreasing_by all_goals sorry

mutual

-- We should be able to get rid of this manual deriviation eventually.
-- There is work in progress on making these mutual derivations automatic.

def decPartialExpr (x y : PartialExpr) : Decidable (x = y) := by
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

def decProdAttrPartialExprList (axs ays : List (Attr × PartialExpr)) : Decidable (axs = ays) :=
  match axs, ays with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a, x)::axs, (a', y)::ays =>
    match decEq a a', decPartialExpr x y, decProdAttrPartialExprList axs ays with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

def decPartialExprList (xs ys : List PartialExpr) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | x::xs, y::ys =>
    match decPartialExpr x y, decPartialExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
end

instance : DecidableEq PartialExpr := decPartialExpr

def Expr.asPartialExpr (x : Expr) : PartialExpr :=
  match x with
  | .lit p => .lit p
  | .var v => .var v
  | .ite x₁ x₂ x₃ => .ite x₁.asPartialExpr x₂.asPartialExpr x₃.asPartialExpr
  | .and x₁ x₂ => .and x₁.asPartialExpr x₂.asPartialExpr
  | .or x₁ x₂ => .or x₁.asPartialExpr x₂.asPartialExpr
  | .unaryApp op x₁ => .unaryApp op x₁.asPartialExpr
  | .binaryApp op x₁ x₂ => .binaryApp op x₁.asPartialExpr x₂.asPartialExpr
  | .getAttr x₁ attr => .getAttr x₁.asPartialExpr attr
  | .hasAttr x₁ attr => .hasAttr x₁.asPartialExpr attr
  | .set xs => .set (xs.map Expr.asPartialExpr)
  | .record attrs => .record (attrs.map λ (k, v) => (k, v.asPartialExpr))
  | .call xfn args => .call xfn (args.map Expr.asPartialExpr)
decreasing_by all_goals sorry

instance : Coe Expr PartialExpr where
  coe := Expr.asPartialExpr

def RestrictedPartialExpr.asPartialExpr (x : RestrictedPartialExpr) : PartialExpr :=
  match x with
  | .lit p => .lit p
  | .set xs => .set (xs.map RestrictedPartialExpr.asPartialExpr)
  | .record attrs => .record (attrs.map λ (k, v) => (k, v.asPartialExpr))
  | .call xfn args => .call xfn (args.map Value.asPartialExpr)
  | .unknown name => .unknown name
decreasing_by all_goals sorry
