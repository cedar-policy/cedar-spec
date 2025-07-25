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

import Cedar.Spec.Evaluator
import Cedar.TPE.Residual
import Cedar.TPE.Evaluator
import Cedar.Validation.TypedExpr
import Cedar.Thm.Data.List.Lemmas

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Theorem stating that converting a TypedExpr to a Residual preserves evaluation semantics.
That is, evaluating the original TypedExpr (converted to Expr) gives the same result
as evaluating the converted Residual.
-/
theorem conversion_preserves_evaluation (te : TypedExpr) (req : Request) (es : Entities) :
  Spec.evaluate te.toExpr req es = (TypedExpr.toResidual te).evaluate req es := by
  cases te with
  | lit p ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
  | var v ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    cases v <;> simp [Spec.evaluate, Residual.evaluate]
  | ite cond thenExpr elseExpr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_cond := conversion_preserves_evaluation cond req es
    have ih_then := conversion_preserves_evaluation thenExpr req es
    have ih_else := conversion_preserves_evaluation elseExpr req es
    rw [←ih_cond]
    simp [Result.as, Value.asBool]
    rw [←ih_then, ←ih_else]
    cases Spec.evaluate cond.toExpr req es
    case ite.error =>
      simp
    case ite.ok =>
      simp
      rename_i a
      cases a
      case prim =>
        simp [bind, Coe.coe, Value.asBool]
      all_goals {
        simp [Coe.coe, Value.asBool]
      }
  | and a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | or a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | unaryApp op expr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | binaryApp op a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | getAttr expr attr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | hasAttr expr attr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | set ls ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1
    rw [List.mapM₁_eq_mapM, List.mapM₁_eq_mapM]
    congr 1
    ext x
    exact conversion_preserves_evaluation x req es
  | record map ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1
    rw [List.mapM₂_eq_mapM, List.mapM₂_eq_mapM]
    congr 1
    ext ⟨a, x⟩
    simp [Spec.bindAttr]
    congr 1
    exact conversion_preserves_evaluation x req es
  | call xfn args ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 2
    rw [Cedar.Thm.Data.List.mapM₁_eq_mapM, Cedar.Thm.Data.List.mapM₁_eq_mapM]
    congr 1
    ext x
    exact conversion_preserves_evaluation x req es

end Cedar.TPE
