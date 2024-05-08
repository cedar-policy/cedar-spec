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

import Cedar.Partial.Evaluator
import Cedar.Spec.Evaluator
import Cedar.Thm.Data.Control
import Cedar.Thm.Partial.Evaluation.Basic

namespace Cedar.Thm.Partial.Evaluation.Ite

open Cedar.Spec (Result)

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.ite`
  expression gives the same output as concrete-evaluating the `Spec.Expr.ite`
  with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {x₁ x₂ x₃ : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval x₂ request entities →
  PartialEvalEquivConcreteEval x₃ request entities →
  PartialEvalEquivConcreteEval (Spec.Expr.ite x₁ x₂ x₃) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁ ih₂ ih₃
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only [ih₁, ih₂, ih₃]
  simp only [Except.map, Result.as, Coe.coe]
  cases Spec.evaluate x₁ request entities <;> simp only [Except.bind_err, Except.bind_ok]
  case ok v₁ =>
    simp only [Spec.Value.asBool]
    cases v₁ <;> try simp only [Except.bind_err]
    case prim p =>
      cases p <;> simp only [Except.bind_ok, Except.bind_err]
      case bool b => cases b <;> simp

end Cedar.Thm.Partial.Evaluation.Ite
