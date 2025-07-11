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
/-- very similar to decExpr
Can be removed when these derivations are automatic.
-/
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
  case assertTrue.assertTrue c1 e1 c2 e2 | assertFalse.assertFalse c1 e1 c2 e2 =>
    exact match decSExpr c1 c2, decSExpr e1 e2 with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)

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


inductive SLError where
| assertError
| interpError (e: Error)

-- Like a Result but can also throw assert errors.
abbrev SLResult (α) := Except SLError α

def SLResult.as {α} (β) [Coe α (SLResult β)] : SLResult α → SLResult β
  | .ok v    => v
  | .error e => .error e

def Result.toSLResult (β) (r: (Result β)) : (SLResult β) :=
match r with
| .ok v    => .ok v
| .error e => .error (.interpError e)

def SLResult.toResult (β) (r: (SLResult β)) : Option (Result β) :=
match r with
| .ok v    => .some (.ok v)
| .error .assertError => .none
| .error (.interpError e) => .some (.error e)

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


/--
Converts an expr to a set of straight line exprs,
exploring all possibilities when an if statement is encountered.
-/
def all_sl_exprs (expr: Expr) : SLExprs :=
  match expr with
  | .ite cond then_expr else_expr =>
    let cond_exprs := all_sl_exprs cond
    let then_exprs := all_sl_exprs then_expr
    let else_exprs := all_sl_exprs else_expr

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
    let product := List.productTR (all_sl_exprs a).toList (all_sl_exprs b).toList
    .mk (product.map (fun pair => .and pair.1 pair.2))
  | .or a b =>
    let product := List.productTR (all_sl_exprs a).toList (all_sl_exprs b).toList
    .mk (product.map (fun pair => .or pair.1 pair.2))
  | .unaryApp op expr =>
    let exprs := all_sl_exprs expr
    .mk (exprs.toList.map (fun e => .unaryApp op e))
  | .binaryApp op a b =>
    let a_exprs := all_sl_exprs a
    let b_exprs := all_sl_exprs b
    let product := List.productTR a_exprs.toList b_exprs.toList
    .mk (product.map (fun pair => .binaryApp op pair.1 pair.2))
  | .getAttr expr attr =>
    let exprs := all_sl_exprs expr
    .mk (exprs.toList.map (fun e => .getAttr e attr))
  | .hasAttr expr attr =>
    let exprs := all_sl_exprs expr
    .mk (exprs.toList.map (fun e => .hasAttr e attr))
  | .set ls =>
    let exprs_lists := ls.map (fun ele =>
      Set.toList (all_sl_exprs ele))
    let all_combinations := List.cartesianProduct exprs_lists
    .mk (all_combinations.map (fun combo => .set combo))
  | .record map =>
    let expr_lists := map.map (fun pair => Set.toList (all_sl_exprs pair.2))
    let attrs := map.map (fun pair => pair.1)
    let all_combinations := List.cartesianProduct expr_lists
    .mk (all_combinations.map (fun combo =>
      .record (List.zipWith (fun attr expr => (attr, expr)) attrs combo)))
  | .call xfn args =>
    let args_exprs := args.map (fun e => (all_sl_exprs e).toList)
    let all_combinations := List.cartesianProduct args_exprs
    .mk (all_combinations.map (fun combo => .call xfn combo))
termination_by sizeOf expr
decreasing_by
  repeat case _ =>
    simp [*]; try omega
    -- Set
  · rename_i h
    simp_wf
    let so := @List.sizeOf_lt_of_mem Expr ele inferInstance ls
    specialize so h
    omega
  -- Record
  · simp_wf
    rename_i h
    let so := @List.sizeOf_lt_of_mem (Attr × Expr) pair inferInstance map
    specialize so h
    have h2: sizeOf pair.snd < sizeOf pair := by {
      cases pair with
      | mk a b =>
        simp; omega
    }
    omega
  -- Call
  · simp [*]
    have h := List.sizeOf_lt_of_mem hx
    omega





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



-- gets all subexpressions, including expr
mutual
/-- Returns a list of all sub-expressions of the given SLExpr, including the expression itself. -/
def all_sub_slexpr (expr: SLExpr) : List SLExpr :=
  match expr with
  | .lit _ | .var _ => [expr]
  | .assertTrue cond ret => expr :: (all_sub_slexpr cond ++ all_sub_slexpr ret)
  | .assertFalse cond ret => expr :: (all_sub_slexpr cond ++ all_sub_slexpr ret)
  | .and a b => expr :: (all_sub_slexpr a ++ all_sub_slexpr b)
  | .or a b => expr :: (all_sub_slexpr a ++ all_sub_slexpr b)
  | .unaryApp _ e => expr :: all_sub_slexpr e
  | .binaryApp _ a b => expr :: (all_sub_slexpr a ++ all_sub_slexpr b)
  | .getAttr e _ => expr :: all_sub_slexpr e
  | .hasAttr e _ => expr :: all_sub_slexpr e
  | .set ls => expr :: all_sub_slexpr_list ls
  | .record map => expr :: all_sub_slexpr_attr_list map
  | .call _ args => expr :: all_sub_slexpr_list args

/-- Helper function to get all sub-expressions from a list of SLExpr. -/
def all_sub_slexpr_list (exprs: List SLExpr) : List SLExpr :=
  match exprs with
  | [] => []
  | e :: es => all_sub_slexpr e ++ all_sub_slexpr_list es

/-- Helper function to get all sub-expressions from a list of (Attr × SLExpr). -/
def all_sub_slexpr_attr_list (attrs: List (Attr × SLExpr)) : List SLExpr :=
  match attrs with
  | [] => []
  | (_, e) :: rest => all_sub_slexpr e ++ all_sub_slexpr_attr_list rest
end


-- evaluate the SLExpr, gathing all entity ids required
-- evaluates each subexpression
def get_all_entities_touched (expr: SLExpr) (store: Entities) (request: Request) : Set EntityUID :=
  let subexprs := all_sub_slexpr expr
  let eval_results := subexprs.map (fun expr => evaluate_sl expr request store)

  -- Extract entity UIDs from successful evaluations
  let entity_uids := eval_results.filterMap (fun result =>
    match result with
    | .ok (.prim (.entityUID uid)) => some uid
    | _ => none)
  Set.mk entity_uids


-- A simple slicer given a set of straight line exprs
-- Loads entire entities from one entity store to the other
def simple_slice_sl (exprs: SLExprs) (store: Entities) (request: Request) : Entities :=
  let entities_needed := Data.Set.union_all (exprs.toList.map (fun expr => get_all_entities_touched expr store request))
  store.filter (fun uid _ => entities_needed.contains uid)



end Cedar.Spec
