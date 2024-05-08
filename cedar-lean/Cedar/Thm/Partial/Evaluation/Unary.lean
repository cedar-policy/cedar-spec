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

namespace Cedar.Thm.Partial.Evaluation.Unary

open Cedar.Spec (UnaryOp)

/--
  `Partial.apply₁` on concrete arguments gives the same output as `Spec.apply₁`
  on the same arguments
-/
theorem apply₁_on_concrete_eqv_concrete {op : UnaryOp} {v : Spec.Value} :
  Partial.apply₁ op v = (Spec.apply₁ op v).map Partial.Value.value
:= by
  rfl

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.unaryApp`
  expression gives the same output as concrete-evaluating the
  `Spec.Expr.unaryApp` with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {x₁ : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {op : UnaryOp} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval (Spec.Expr.unaryApp op x₁) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only [ih₁]
  cases Spec.evaluate x₁ request entities <;> simp only [Except.bind_err, Except.bind_ok]
  case error e => simp [Except.map]
  case ok v₁ => rfl

end Cedar.Thm.Partial.Evaluation.Unary
