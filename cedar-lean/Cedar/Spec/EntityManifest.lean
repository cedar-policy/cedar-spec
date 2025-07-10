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

import Cedar.Spec.Expr
import Cedar.Spec.Evaluator
import Cedar.Spec.Entities
import Cedar.Spec.Expr
import Cedar.Spec.ExtFun
import Cedar.Spec.Request
import Cedar.Data
import Cedar.Spec.Ext


import Cedar.Data.List
import Std.Data

namespace Cedar.Spec


open Cedar.Data
open Error

/--
A SLExpr or Straight Line Expr is like a Cedar Expr, but without if statements.
Instead, we have assertTrue and assertFalse, and these
  error out.

For a given entity store,
a cedar expression is the same as evaluating a SLExpr, with if statements replaced with asserts.
-/
inductive SLExpr : Type where
  | lit (p : Prim)
  | var (v : Var)
  | assertTrue (cond : SLExpr) (return_val : SLExpr)
  | assertFalse (cond : SLExpr) (return_val : SLExpr)
  | and (a : SLExpr) (b : SLExpr)
  | or (a : SLExpr) (b : SLExpr)
  | unaryApp (op : UnaryOp) (expr : SLExpr)
  | binaryApp (op : BinaryOp) (a : SLExpr) (b : SLExpr)
  | getAttr (expr : SLExpr) (attr : Attr)
  | hasAttr (expr : SLExpr) (attr : Attr)
  | set (ls : List SLExpr)
  | record (map : List (Attr × SLExpr))
  | call (xfn : ExtFun) (args : List SLExpr)

def SLExprs : Type := Set SLExpr


deriving instance Repr, Inhabited for SLExpr
deriving instance Repr, Inhabited for SLExprs


mutual
def decSExpr (x y : SLExpr) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case lit.lit x₁ y₁ | var.var x₁ y₁ =>
    exact match decEq x₁ y₁ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case and.and x₁ x₂ y₁ y₂ | or.or x₁ x₂ y₁ y₂ =>
    exact match decSExpr x₁ y₁, decSExpr x₂ y₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unaryApp.unaryApp o x₁ o' y₁ =>
    exact match decEq o o', decSExpr x₁ y₁ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case binaryApp.binaryApp o x₁ x₂ o' y₁ y₂ =>
    exact match decEq o o', decSExpr x₁ y₁, decSExpr x₂ y₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case getAttr.getAttr x₁ a y₁ a' | hasAttr.hasAttr x₁ a y₁ a' =>
    exact match decSExpr x₁ y₁, decEq a a' with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set xs ys =>
    exact match decSExprList xs ys with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record axs ays =>
    exact match decProdAttrSExprList axs ays with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case call.call f xs f' ys =>
    exact match decEq f f', decSExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case _ => sorry

def decProdAttrSExprList (axs ays : List (Prod Attr SLExpr)) : Decidable (axs = ays) :=
  match axs, ays with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a, x)::axs, (a', y)::ays =>
    match decEq a a', decSExpr x y, decProdAttrSExprList axs ays with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

def decSExprList (xs ys : List SLExpr) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | x::xs, y::ys =>
    match decSExpr x y, decSExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
end

instance : DecidableEq SLExpr := decSExpr



mutual
  def to_straight_line_map_list (exprList: List (Attr × Expr)) : List (List SLExpr) :=
    match exprList with
    | [] => []
    | [(_attr, ele)] => [(to_straight_line_exprs ele).toList]
    | (_attr, ele) :: rest =>
      (to_straight_line_exprs ele).toList :: (to_straight_line_map_list rest)

  def to_straight_line_list (exprList : List Expr) : List (List SLExpr) :=
    match exprList with
    | [] => []
    | [x] => [(to_straight_line_exprs x).toList]
    | ele :: rest =>
      (to_straight_line_exprs ele).toList :: (to_straight_line_list rest)
  /--
  Converts an expr to a set of straight line exprs,
  exploring all possibilities when an if statement is encountered.
  -/
  def to_straight_line_exprs (expr: Expr) : SLExprs :=
    match expr with
    | .ite cond then_expr else_expr =>
      let cond_exprs := to_straight_line_exprs cond
      let then_exprs := to_straight_line_exprs then_expr
      let else_exprs := to_straight_line_exprs else_expr

      let then_with_cond := List.productTR cond_exprs.toList then_exprs.toList
      let else_with_cond := List.productTR cond_exprs.toList else_exprs.toList

      let then_results := then_with_cond.map (fun pair => .assertTrue pair.1 pair.2)
      let else_results := else_with_cond.map (fun pair => .assertFalse pair.1 pair.2)

      .mk (then_results ++ else_results)
    | .lit p =>
      .mk [.lit p]
    | .var v =>
      .mk [.var v]
    | .and a b =>
      let product := List.productTR (to_straight_line_exprs a).toList (to_straight_line_exprs b).toList
      .mk (product.map (fun pair => .and pair.1 pair.2))
    | .or a b =>
      let product := List.productTR (to_straight_line_exprs a).toList (to_straight_line_exprs b).toList
      .mk (product.map (fun pair => .or pair.1 pair.2))
    | .unaryApp op expr =>
      let exprs := to_straight_line_exprs expr
      .mk (exprs.toList.map (fun e => .unaryApp op e))
    | .binaryApp op a b =>
      let a_exprs := to_straight_line_exprs a
      let b_exprs := to_straight_line_exprs b
      let product := List.productTR a_exprs.toList b_exprs.toList
      .mk (product.map (fun pair => .binaryApp op pair.1 pair.2))
    | .getAttr expr attr =>
      let exprs := to_straight_line_exprs expr
      .mk (exprs.toList.map (fun e => .getAttr e attr))
    | .hasAttr expr attr =>
      let exprs := to_straight_line_exprs expr
      .mk (exprs.toList.map (fun e => .hasAttr e attr))
    | .set ls =>
      let exprs_lists := to_straight_line_list ls
      let all_combinations := List.cartesianProduct exprs_lists
      .mk (all_combinations.map (fun combo => .set combo))
    | .record map =>
      let expr_lists := to_straight_line_map_list map
      let attrs := map.map (fun pair => pair.1)
      let all_combinations := List.cartesianProduct expr_lists
      .mk (all_combinations.map (fun combo =>
        .record (List.zipWith (fun attr expr => (attr, expr)) attrs combo)))
    | .call xfn args =>
      let args_exprs := args.map (fun e => (to_straight_line_exprs e).toList)
      let all_combinations := List.cartesianProduct args_exprs
      .mk (all_combinations.map (fun combo => .call xfn combo))
end


-- A simple slicer given a set of straight line exprs
-- Loads entire entities from one entity store to the other
def simple_slice_entities_straight_line (_exprs: SLExprs) (store: Entities) : Entities :=
  store

inductive SLError where
| assertError
| interpError (e: Error)

abbrev SLResult (α) := Except SLError α

def SLResult.as {α} (β) [Coe α (SLResult β)] : SLResult α → SLResult β
  | .ok v    => v
  | .error e => .error e

def Result.toSLResult (β) (r: (Result β)) : (SLResult β) :=
match r with
| .ok v    => .ok v
| .error e => .error (.interpError e)

deriving instance Repr, DecidableEq, Inhabited for SLError

instance : Coe Value (SLResult Bool) where
  coe v := v.asBool.toSLResult

instance : Coe Value (SLResult Int64) where
  coe v := v.asInt.toSLResult

instance : Coe Value (SLResult String) where
  coe v := v.asString.toSLResult

instance : Coe Value (SLResult EntityUID) where
  coe v := v.asEntityUID.toSLResult

instance : Coe Value (SLResult (Data.Set Value)) where
  coe v := v.asSet.toSLResult



-- Like evaluate but returns None if any asserts failed
def evaluate_sl(x : SLExpr) (req : Request) (es : Entities) : SLResult Value :=
  match x with
  | .lit l           => .ok l
  | .var v           => match v with
    | .principal     => .ok req.principal
    | .action        => .ok req.action
    | .resource      => .ok req.resource
    | .context       => .ok req.context
  | .assertTrue cond e => do
    let b ← (evaluate_sl cond req es).as Bool
    if b then (evaluate_sl e req es) else (.error .assertError)
  | .assertFalse cond e => do
    let b ← (evaluate_sl cond req es).as Bool
    if !b then (evaluate_sl e req es) else (.error .assertError)
  | .and x₁ x₂       => do
    let b ← (evaluate_sl x₁ req es).as Bool
    if !b then .ok b else (evaluate_sl x₂ req es).as Bool
  | .or x₁ x₂        => do
    let b ← (evaluate_sl x₁ req es).as Bool
    if b then .ok b else (evaluate_sl x₂ req es).as Bool
  | .unaryApp op₁ x₁ => do
    let v₁ ← evaluate_sl x₁ req es
    (apply₁ op₁ v₁).toSLResult
  | .binaryApp op₂ x₁ x₂ => do
    let v₁ ← evaluate_sl x₁ req es
    let v₂ ← evaluate_sl x₂ req es
    (apply₂ op₂ v₁ v₂ es).toSLResult
  | .hasAttr x₁ a    => do
    let v₁ ← evaluate_sl x₁ req es
    (hasAttr v₁ a es).toSLResult
  | .getAttr x₁ a    => do
    let v₁ ← evaluate_sl x₁ req es
    (getAttr v₁ a es).toSLResult
  | .set xs          => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate_sl x₁ req es)
    .ok (Set.make vs)
  | .record axs      => do
    let avs ← axs.mapM₂ (fun ⟨(a₁, x₁), _⟩ => bindAttr a₁ (evaluate_sl x₁ req es))
    .ok (Map.make avs)
  | .call xfn xs     => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate_sl x₁ req es)
    (call xfn vs).toSLResult


end Cedar.Spec
