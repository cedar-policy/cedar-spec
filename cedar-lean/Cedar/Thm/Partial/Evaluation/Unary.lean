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
import Cedar.Thm.Partial.Evaluation.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Unary

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Prim UnaryOp)

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
  if `Spec.apply₁` returns `ok` with some value, that is a well-formed value as
  well

  This theorem does not actually require that the input value is WellFormed
-/
theorem specApply₁_wf {v : Spec.Value} {op : UnaryOp} :
  Spec.apply₁ op v = .ok v' → v'.WellFormed
:= by
  unfold Spec.apply₁
  intro h
  split at h <;> try simp at h <;> subst h
  · simp [Spec.Value.WellFormed, Prim.WellFormed]
  · unfold Spec.intOrErr at h
    split at h <;> simp at h
    subst h ; simp [Spec.Value.WellFormed, Prim.WellFormed]
  · simp [Spec.Value.WellFormed, Prim.WellFormed]
  · simp [Spec.Value.WellFormed, Prim.WellFormed]

/--
  if `Partial.apply₁` on a well-formed value returns `ok` with some value, that is
  a well-formed value as well

  This theorem does not actually require that the input value is WellFormed
-/
theorem partialApply₁_wf {pval : Partial.Value} {op : UnaryOp} :
  Partial.apply₁ op pval = .ok pval' → pval'.WellFormed
:= by
  unfold Partial.apply₁
  cases pval <;> simp
  case residual r => intro h₁ ; subst h₁ ; simp [Partial.Value.WellFormed]
  case value v =>
    cases h₁ : Spec.apply₁ op v <;> simp
    case ok v' =>
      intro h ; subst h ; simp [Partial.Value.WellFormed] at *
      exact specApply₁_wf h₁

/--
  Inductive argument that if partial-evaluating a `Partial.Expr.unaryApp`
  produces `ok` with some value, that value is well-formed

  This theorem does not actually require that x₁ is WellFormed
-/
theorem partial_eval_wf {x₁ : Partial.Expr} {op : UnaryOp} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToWellFormed (Partial.Expr.unaryApp op x₁) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  intro pval
  cases hx₁ : Partial.evaluate x₁ request entities <;> simp [hx₁]
  case ok pval₁ => exact partialApply₁_wf

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
theorem subst_preserves_evaluation_to_value {x₁ : Partial.Expr} {op : UnaryOp} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
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

/--
  Inductive argument that if partial-evaluation of a `Partial.Expr.unaryApp`
  returns an error, then it also returns an error (not necessarily the same
  error) after any substitution of unknowns

  The proof of `subst_preserves_evaluation_to_value` for this
  request/entities/subsmap is passed in as an argument, because this file can't
  import `Thm/Partial/Evaluation.lean` to access it.
  See #372.
-/
theorem subst_preserves_errors {x₁ : Partial.Expr} {op : UnaryOp} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (h_spetv : ∀ x, SubstPreservesEvaluationToConcrete x req req' entities subsmap)
  (ih₁ : SubstPreservesEvaluationToError x₁ req req' entities subsmap) :
  SubstPreservesEvaluationToError (Partial.Expr.unaryApp op x₁) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToError at *
  unfold Partial.evaluate Partial.Expr.subst
  intro h_req ; specialize ih₁ h_req
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> simp only [hx₁, false_implies, implies_true, Except.error.injEq] at ih₁
  case error e₁ =>
    replace ⟨e₁', ih₁⟩ := ih₁ e₁ rfl
    simp [ih₁]
  case ok pval₁ =>
    simp only [Except.bind_ok]
    intro e₁ h₁
    cases hx₁' : Partial.evaluate (x₁.subst subsmap) req' (entities.subst subsmap)
    case error e₁' => exists e₁'
    case ok pval₁' =>
      simp only [Except.bind_ok]
      cases pval₁
      case value v₁ =>
        simp only [h_spetv x₁ h_req v₁ hx₁, Except.ok.injEq] at hx₁' ; subst pval₁'
        exists e₁
      case residual r₁ => exists e₁


end Cedar.Thm.Partial.Evaluation.Unary
