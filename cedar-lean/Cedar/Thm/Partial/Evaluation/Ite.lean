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
import Cedar.Thm.Partial.Evaluation.Props

namespace Cedar.Thm.Partial.Evaluation.Ite

open Cedar.Data
open Cedar.Partial (Unknown)
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

/--
  If partial-evaluating a `Partial.Expr.ite` produces `ok` with a concrete
  value, then partial-evaluating the guard produces either concrete `true` or
  `false`, and partial-evaluating whichever operand isn't short-circuited out
  produces `ok` with a concrete value
-/
theorem evals_to_concrete_then_operands_eval_to_concrete {x₁ x₂ x₃ : Partial.Expr} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Partial.Expr.ite x₁ x₂ x₃) request entities →
  (Partial.evaluate x₁ request entities = .ok (.value (.prim (.bool true))) ∧ EvaluatesToConcrete x₂ request entities) ∨
  (Partial.evaluate x₁ request entities = .ok (.value (.prim (.bool false))) ∧ EvaluatesToConcrete x₃ request entities)
:= by
  unfold EvaluatesToConcrete
  intro h₁
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  cases hx₁ : Partial.evaluate x₁ request entities
  <;> simp only [hx₁, Spec.Value.asBool, Except.bind_err, Except.bind_ok] at h₁
  case ok pval₁ =>
    cases pval₁ <;> simp only [Except.ok.injEq] at h₁
    case value v₁ =>
      cases v₁
      case prim p₁ =>
        cases p₁ <;> simp only [Except.bind_ok, Except.bind_err] at h₁
        case bool b₁ =>
          cases b₁ <;> simp only [reduceIte] at h₁
          case true =>
            left
            cases hx₂ : Partial.evaluate x₂ request entities
            <;> simp only [hx₂, Except.ok.injEq] at h₁
            case ok v₂ => subst h₁ ; simp
          case false =>
            right
            cases hx₃ : Partial.evaluate x₃ request entities
            <;> simp only [hx₃, Except.ok.injEq] at h₁
            case ok v₃ => subst h₁ ; simp
      case set | record => simp at h₁
      case ext x => cases x <;> simp at h₁

/--
  Inductive argument that if partial-evaluation of a `Partial.Expr.ite` returns
  a concrete value, then it returns the same value after any substitution of
  unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ x₂ x₃ : Partial.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value}
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap)
  (ih₂₃ :
    (Partial.evaluate x₁ req entities = .ok (.value (.prim (.bool true))) ∧ SubstPreservesEvaluationToConcrete x₂ req req' entities subsmap) ∨
    (Partial.evaluate x₁ req entities = .ok (.value (.prim (.bool false))) ∧ SubstPreservesEvaluationToConcrete x₃ req req' entities subsmap)
  ) :
  SubstPreservesEvaluationToConcrete (Partial.Expr.ite x₁ x₂ x₃) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete Partial.evaluate Spec.Value.asBool
  intro h_req v
  specialize ih₁ h_req
  rcases ih₂₃ with ⟨hx₁, ih₂⟩ | ⟨hx₁, ih₃⟩
  · specialize ih₂ h_req
    specialize ih₁ (.prim (.bool true)) hx₁
    unfold Partial.Expr.subst
    simp only [hx₁, Except.bind_ok, reduceIte]
    intro h₁
    simp only [ih₁, Except.bind_ok, reduceIte]
    exact ih₂ v h₁
  · specialize ih₃ h_req
    specialize ih₁ (.prim (.bool false)) hx₁
    unfold Partial.Expr.subst
    simp only [hx₁, Except.bind_ok, reduceIte]
    intro h₁
    simp only [ih₁, Except.bind_ok, reduceIte]
    exact ih₃ v h₁

end Cedar.Thm.Partial.Evaluation.Ite
