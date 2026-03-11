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
import Cedar.Spec.Policy

/-! This file defines concrete syntax tree (CST) types for Cedar expressions. -/

namespace Cedar.Spec.CST

open Cedar.Spec

----- Definitions -----

/-- Addition/subtraction operator tag -/
inductive AddOp where
  | plus
  | minus

/-- Relational operators available in the CST (superset of AST) -/
inductive RelOp where
  | eq
  | notEq
  | less
  | lessEq
  | greater
  | greaterEq
  | mem

/-- Unary operator kind in the CST -/
inductive UnaryOp where
  | not
  | neg

/-- CST expression type mirroring Cedar's concrete grammar -/
inductive Expr where
  | lit (p : Prim)
  | var (v : Var)
  | ite (cond : Expr) (thenExpr : Expr) (elseExpr : Expr)
  | or (initial : Expr) (extended : List Expr)
  | and (initial : Expr) (extended : List Expr)
  | rel (op : RelOp) (lhs : Expr) (rhs : Expr)
  | has (expr : Expr) (attr : Attr)
  | extendedHas (expr : Expr) (attrs : List Attr)
  | like (expr : Expr) (pat : Pattern)
  | is (expr : Expr) (ety : EntityType)
  | isIn (expr : Expr) (ety : EntityType) (inExpr : Expr)
  | add (initial : Expr) (extended : List (AddOp × Expr))
  | mult (initial : Expr) (extended : List Expr)
  | unary (ops : List UnaryOp) (expr : Expr)
  | getAttr (expr : Expr) (attr : Attr)
  | hasAttr (expr : Expr) (attr : Attr)
  | set (elems : List Expr)
  | record (pairs : List (Attr × Expr))
  | call (fn : ExtFun) (args : List Expr)
  | methodCall (recv : Expr) (fn : ExtFun) (args : List Expr)

/-- CST-level condition -/
structure Condition where
  kind : ConditionKind
  body : Expr

/-- CST-level policy -/
structure Policy where
  id : PolicyID
  effect : Effect
  principalScope : PrincipalScope
  actionScope : ActionScope
  resourceScope : ResourceScope
  conditions : List Condition

----- Derivations -----

deriving instance Repr, DecidableEq, Inhabited for AddOp
deriving instance Repr, DecidableEq, Inhabited for RelOp
deriving instance Repr, DecidableEq, Inhabited for UnaryOp
deriving instance Repr, Inhabited for Expr

end Cedar.Spec.CST
