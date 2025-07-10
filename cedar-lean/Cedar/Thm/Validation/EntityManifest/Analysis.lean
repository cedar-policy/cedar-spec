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

import Cedar.Validation.Types
import Cedar.Data.List

namespace Cedar.Validation.EntityManifest

open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/--
Stores the access term's constructor and children.

Includes leaf nodes (literals, variables, and strings)
as well as attribute accesses, tag accesses, and ancestor accesses.
-/
inductive AccessTerm : Type where
  -- Literal entity ids
  | literal (euid : EntityUID)
  -- A Cedar variable
  | var (v : Var)
  -- A literal Cedar string
  | string (s : String)
  -- A record or entity attribute
  | attribute (of : AccessTerm) (attr : Attr)
  -- An entity tag access
  | tag (of : AccessTerm) (tag : AccessTerm)
  -- Whether this entity has a particular ancestor is requested
  | ancestor (of : AccessTerm) (ancestor : AccessTerm)
deriving Inhabited, Repr, DecidableEq



/--
Like a Cedar Expr, but without if statements.
Instead, we have droppedCondition, which record the fact that a condition
was evaluated on the side.

Every Cedar expression is the same as evaluating a StraitLineExpr, with
if statements replaced with the then or else branch that gets evaluated.
-/
inductive StraightLineExpr : Type where
  | lit (p : Prim)
  | var (v : Var)
  | droppedCondition (cond : StraightLineExpr) (branchTaken : StraightLineExpr)
  | and (a : StraightLineExpr) (b : StraightLineExpr)
  | or (a : StraightLineExpr) (b : StraightLineExpr)
  | unaryApp (op : UnaryOp) (expr : StraightLineExpr)
  | binaryApp (op : BinaryOp) (a : StraightLineExpr) (b : StraightLineExpr)
  | getAttr (expr : StraightLineExpr) (attr : Attr)
  | hasAttr (expr : StraightLineExpr) (attr : Attr)
  | set (ls : List StraightLineExpr)
  | record (map : List (Attr × StraightLineExpr))
  | call (xfn : ExtFun) (args : List StraightLineExpr)

def StraitLineExprs : Type := Set StraightLineExpr


deriving instance Repr, Inhabited for StraightLineExpr
deriving instance Repr, Inhabited for StraitLineExprs

namespace WrappedAccessTerms



mutual
  def to_straight_line_map_list (exprList: List (Attr × Expr)) : List (List StraightLineExpr) :=
    match exprList with
    | [] => []
    | [x] => [(to_straight_line_exprs x.2).toList]
    | ele :: rest =>
      (to_straight_line_exprs ele.2).toList :: (to_straight_line_map_list rest)

  def to_strait_line_list (exprList : List Expr) : List (List StraitLineExpr) :=
    match exprList with
    | [] => []
    | [x] => [(to_straight_line_exprs x).toList]
    | ele :: rest =>
      (to_straight_line_exprs ele).toList :: (to_straight_line_map_list rest)
  /--
  Converts an expr to a set of strait line exprs,
  exploring all possibilities when an if statement is encountered.
  -/
  def to_straight_line_exprs (expr: Expr) : StraitLineExprs :=
    match expr with
    | .ite cond then_expr else_expr =>
      let cond_exprs := to_straight_line_exprs cond
      let then_exprs := to_straight_line_exprs then_expr
      let else_exprs := to_straight_line_exprs else_expr

      let then_with_cond := List.productTR cond_exprs.toList then_exprs.toList
      let else_with_cond := List.productTR cond_exprs.toList else_exprs.toList

      let then_results := then_with_cond.map (fun pair => .droppedCondition pair.1 pair.2)
      let else_results := else_with_cond.map (fun pair => .droppedCondition pair.1 pair.2)

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
      let exprs_lists := ls.map (fun sete => (to_straight_line_exprs sete).toList)
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




end WrappedAccessTerms

end Cedar.Validation.EntityManifest
