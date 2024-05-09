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
import Cedar.Tactic.Csimp
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Partial.Evaluation.Basic
import Cedar.Thm.Partial.Evaluation.Set

namespace Cedar.Thm.Partial.Evaluation.Call

open Cedar.Spec (Error ExtFun Result)

/--
  `Partial.evaluateCall` on concrete arguments gives the same output as
  `Spec.call` on those same arguments
-/
theorem evaluateCall_on_concrete_eqv_concrete {vs : List Spec.Value} {xfn : ExtFun} :
  Partial.evaluateCall xfn (vs.map Partial.Value.value) = (Spec.call xfn vs).map Partial.Value.value
:= by
  unfold Partial.evaluateCall
  simp only [List.mapM_map, List.mapM_some]
  cases Spec.call xfn vs <;> simp [Except.map]

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.call`
  expression gives the same output as concrete-evaluating the `Spec.Expr.call`
  with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {xs : List Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {xfn : ExtFun} :
  (∀ x ∈ xs, PartialEvalEquivConcreteEval x request entities) →
  PartialEvalEquivConcreteEval (Spec.Expr.call xfn xs) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only
  rw [List.map₁_eq_map Spec.Expr.asPartialExpr]
  rw [List.mapM₁_eq_mapM (Partial.evaluate · request entities)]
  rw [List.mapM₁_eq_mapM (Spec.evaluate · request entities)]
  rw [List.mapM_map]
  rw [Set.mapM_partial_eval_eqv_concrete_eval ih₁]
  cases xs.mapM (Spec.evaluate · request entities) <;> csimp
  case error e => simp [Except.map]
  case ok vs => exact evaluateCall_on_concrete_eqv_concrete

end Cedar.Thm.Partial.Evaluation.Call
