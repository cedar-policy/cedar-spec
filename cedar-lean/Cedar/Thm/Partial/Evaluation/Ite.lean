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
import Cedar.Thm.Partial.WellFormed
import Cedar.Thm.Partial.Subst

namespace Cedar.Thm.Partial.Evaluation.Ite

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Expr Result)

/--
  Inductive argument that, for an `Expr.ite` with concrete request/entities,
  partial evaluation and concrete evaluation give the same output
-/
theorem on_concrete_eqv_concrete_eval {x₁ x₂ x₃ : Expr} {request : Spec.Request} {entities : Spec.Entities} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval x₂ request entities →
  PartialEvalEquivConcreteEval x₃ request entities →
  PartialEvalEquivConcreteEval (Expr.ite x₁ x₂ x₃) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁ ih₂ ih₃
  unfold Partial.evaluate Spec.evaluate
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
  Inductive argument that if partial-evaluating an `Expr.ite` expression
  produces `ok` with some value, that value is well-formed as well
-/
theorem partial_eval_wf {x₁ x₂ x₃ : Expr} {request : Partial.Request} {entities : Partial.Entities}
  (ih₂ : EvaluatesToWellFormed x₂ request entities)
  (ih₃ : EvaluatesToWellFormed x₃ request entities) :
  EvaluatesToWellFormed (Expr.ite x₁ x₂ x₃) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  cases hx₁ : Partial.evaluate x₁ request entities <;> simp [hx₁]
  case ok pval₁ =>
    cases pval₁ <;> simp only [Except.ok.injEq, forall_eq']
    case residual r₁ => simp only [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
    case value v₁ =>
      cases v₁ <;> simp only [Spec.Value.asBool, Except.bind_err, false_implies, implies_true]
      case prim p₁ =>
        cases p₁ <;> simp only [Except.bind_ok, Except.bind_err, false_implies, implies_true]
        case bool b₁ =>
          cases b₁ <;> simp only [Bool.false_eq_true, reduceIte]
          case true =>
            cases hx₂ : Partial.evaluate x₂ request entities <;> simp [hx₂]
            case ok pval => exact ih₂ pval hx₂
          case false =>
            cases hx₃ : Partial.evaluate x₃ request entities <;> simp [hx₃]
            case ok pval => exact ih₃ pval hx₃

/--
  If partial-evaluating an `Expr.ite` produces `ok` with a concrete
  value, then partial-evaluating the guard produces either concrete `true` or
  `false`, and partial-evaluating whichever operand isn't short-circuited out
  produces `ok` with a concrete value
-/
theorem evals_to_concrete_then_operands_eval_to_concrete {x₁ x₂ x₃ : Expr} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Expr.ite x₁ x₂ x₃) request entities →
  (Partial.evaluate x₁ request entities = .ok (.value true) ∧ EvaluatesToConcrete x₂ request entities) ∨
  (Partial.evaluate x₁ request entities = .ok (.value false) ∧ EvaluatesToConcrete x₃ request entities)
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
  Inductive argument that if partial-evaluation of an `Expr.ite` returns
  a concrete value, then it returns the same value after any substitution of
  unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ x₂ x₃ : Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap)
  (ih₂₃ :
    (Partial.evaluate x₁ req entities = .ok (.value true) ∧ SubstPreservesEvaluationToConcrete x₂ req req' entities subsmap) ∨
    (Partial.evaluate x₁ req entities = .ok (.value false) ∧ SubstPreservesEvaluationToConcrete x₃ req req' entities subsmap)
  ) :
  SubstPreservesEvaluationToConcrete (Expr.ite x₁ x₂ x₃) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete Partial.evaluate Spec.Value.asBool
  intro h_req v
  specialize ih₁ h_req
  rcases ih₂₃ with ⟨hx₁, ih₂⟩ | ⟨hx₁, ih₃⟩
  · specialize ih₂ h_req
    specialize ih₁ (.prim (.bool true)) hx₁
    simp only [hx₁, Except.bind_ok, reduceIte]
    intro h₁
    simp only [ih₁, Except.bind_ok, reduceIte]
    exact ih₂ v h₁
  · specialize ih₃ h_req
    specialize ih₁ (.prim (.bool false)) hx₁
    simp only [hx₁, Except.bind_ok, reduceIte]
    intro h₁
    simp only [ih₁, Except.bind_ok, reduceIte]
    exact ih₃ v h₁

/--
  Inductive argument that if partial-evaluation of an `Expr.ite` returns
  an error, then it also returns an error (not necessarily the same error) after
  any substitution of unknowns

  The proof of `subst_preserves_evaluation_to_value` for this
  request/entities/subsmap is passed in as an argument, because this file can't
  import `Thm/Partial/Evaluation.lean` to access it.
  See #372.
-/
theorem subst_preserves_errors {x₁ x₂ x₃ : Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (h_spetv : ∀ x, SubstPreservesEvaluationToConcrete x req req' entities subsmap)
  (ih₁ : SubstPreservesEvaluationToError x₁ req req' entities subsmap)
  (ih₂ : SubstPreservesEvaluationToError x₂ req req' entities subsmap)
  (ih₃ : SubstPreservesEvaluationToError x₃ req req' entities subsmap) :
  SubstPreservesEvaluationToError (Expr.ite x₁ x₂ x₃) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToError at *
  unfold Partial.evaluate
  intro h_req ; specialize ih₁ h_req ; specialize ih₂ h_req ; specialize ih₃ h_req
  exact match hx₁ : Partial.evaluate x₁ req entities with
  | .error e₁ => by
    replace ⟨e₁', ih₁⟩ := ih₁ e₁ hx₁
    simp only [ih₁, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
  | .ok (.residual r₁) => by simp only [Except.bind_ok, false_implies, implies_true]
  | .ok (.value v₁) => by
    simp only [h_spetv x₁ h_req v₁ hx₁, Except.bind_ok]
    cases v₁
    <;> simp only [Spec.Value.asBool, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
    case prim p₁ =>
      cases p₁
      <;> simp only [Except.bind_ok, Except.bind_err, Except.error.injEq, exists_eq', implies_true] at *
      case bool b₁ =>
        cases b₁ <;> simp only [Bool.false_eq_true, reduceIte] at *
        case true =>
          exact match hx₂ : Partial.evaluate x₂ req entities with
          | .error e' => by simp [hx₂, ih₂ e']
          | .ok (.residual r₂) => by simp only [false_implies, implies_true]
          | .ok (.value v₂) => by simp [h_spetv x₂ h_req v₂ hx₂, hx₂]
        case false =>
          exact match hx₃ : Partial.evaluate x₃ req entities with
          | .error e' => by simp [hx₃, ih₃ e']
          | .ok (.residual r₃) => by simp only [false_implies, implies_true]
          | .ok (.value v₃) => by simp [h_spetv x₃ h_req v₃ hx₃, hx₃]

end Cedar.Thm.Partial.Evaluation.Ite
