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

import Cedar.Data.Map
import Cedar.Partial.Expr
import Cedar.Partial.Value
import Cedar.Spec.Expr
import Cedar.Thm.Data.List

/-! ## Lemmas about `subst` operations -/

namespace Cedar.Thm.Partial

open Cedar.Data
open Cedar.Partial (Unknown)

/--
  subst on a concrete expression is that expression
-/
theorem subst_concrete_expr (expr : Spec.Expr) (subsmap : Map Unknown Partial.Value) :
  expr.asPartialExpr.subst subsmap = expr.asPartialExpr
:= by
  unfold Partial.Expr.subst Spec.Expr.asPartialExpr
  cases expr
  case lit | var => simp only
  case unaryApp op x₁ | getAttr x₁ attr | hasAttr x₁ attr =>
    simp only [Partial.Expr.unaryApp.injEq, Partial.Expr.getAttr.injEq, Partial.Expr.hasAttr.injEq, true_and, and_true]
    exact subst_concrete_expr x₁ subsmap
  case and x₁ x₂ | or x₁ x₂ | binaryApp op x₁ x₂ =>
    simp only [Partial.Expr.and.injEq, Partial.Expr.or.injEq, Partial.Expr.binaryApp.injEq, true_and, and_true]
    constructor
    · exact subst_concrete_expr x₁ subsmap
    · exact subst_concrete_expr x₂ subsmap
  case ite x₁ x₂ x₃ =>
    simp only [Partial.Expr.ite.injEq]
    repeat any_goals apply And.intro
    · exact subst_concrete_expr x₁ subsmap
    · exact subst_concrete_expr x₂ subsmap
    · exact subst_concrete_expr x₃ subsmap
  case set xs | call xfn xs =>
    simp only [Partial.Expr.set.injEq, Partial.Expr.call.injEq, true_and, and_true]
    simp only [List.map₁_eq_map, List.map_map]
    apply List.map_congr
    intro x _
    exact subst_concrete_expr x subsmap
  case record attrs =>
    simp only [Partial.Expr.record.injEq, Partial.Expr.record.injEq, true_and, and_true]
    simp only [List.map_attach₂_snd, List.map_map]
    apply List.map_congr
    intro (a, x) h₁
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    have := List.sizeOf_snd_lt_sizeOf_list h₁
    exact subst_concrete_expr x subsmap
termination_by expr
