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
    sorry
  | and a b ty =>
    sorry
  | or a b ty =>
    sorry
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
    sorry
  | record map ty =>
    sorry
  | call xfn args ty =>
    sorry

end Cedar.TPE
