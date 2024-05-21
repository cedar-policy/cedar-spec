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

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (UnaryOp)

/--
  `Partial.apply₁` on concrete arguments gives the same output as `Spec.apply₁`
  on the same arguments
-/
theorem apply₁_on_concrete_eqv_concrete (op : UnaryOp) (v : Spec.Value) :
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

/--
  If `Partial.apply₁` produces `ok` with a concrete value, then so would
  partial-evaluating its operand
-/
theorem partialApply₁_returns_concrete_then_operand_evals_to_concrete {pval₁ : Partial.Value} {op : UnaryOp} :
  Partial.apply₁ op pval₁ = .ok (.value v) →
  ∃ v₁, pval₁ = .value v₁
:= by
  unfold Partial.apply₁
  intro h₁
  cases pval₁
  case value v₁ => exists v₁
  case residual r₁ => simp only [Except.ok.injEq] at h₁

/--
  If partial-evaluating a `Partial.Expr.unaryApp` produces `ok` with a concrete
  value, then so would partial-evaluating its operand
-/
theorem evals_to_concrete_then_operand_evals_to_concrete {x₁ : Partial.Expr} {op : UnaryOp} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Partial.Expr.unaryApp op x₁) request entities →
  EvaluatesToConcrete x₁ request entities
:= by
  unfold EvaluatesToConcrete
  intro h₁
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  cases hx₁ : Partial.evaluate x₁ request entities
  <;> simp only [hx₁, Except.bind_err, Except.bind_ok] at h₁
  case ok pval₁ =>
    have ⟨v₁, hv₁⟩ := partialApply₁_returns_concrete_then_operand_evals_to_concrete h₁
    subst pval₁
    exists v₁

/--
  Inductive argument that if partial-evaluation of a `Partial.Expr.unaryApp`
  returns a concrete value, then it returns the same value after any
  substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ : Partial.Expr} {op : UnaryOp} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value}
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Partial.Expr.unaryApp op x₁) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete at *
  unfold Partial.evaluate Spec.Value.asBool
  intro h_req v
  specialize ih₁ h_req
  unfold Partial.Expr.subst
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> simp only [hx₁, Except.ok.injEq, Except.bind_ok, Except.bind_err, false_implies, forall_const] at *
  case ok pval₁ =>
    cases pval₁
    case value v₁ => simp only [Partial.Value.value.injEq, forall_eq'] at * ; simp [ih₁]
    case residual r₁ => simp [Partial.apply₁]

end Cedar.Thm.Partial.Evaluation.Unary
