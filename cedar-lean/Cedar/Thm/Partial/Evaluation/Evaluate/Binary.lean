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
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.EvaluateBinaryApp
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Evaluate.Binary

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (BinaryOp EntityUID Expr intOrErr Prim Result)

/--
  Inductive argument that, for an `Expr.binaryApp` with concrete
  request/entities, partial evaluation and concrete evaluation give the same
  output
-/
theorem on_concrete_eqv_concrete_eval {x₁ x₂ : Expr} {request : Spec.Request} {entities : Spec.Entities} {op : BinaryOp} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval x₂ request entities →
  PartialEvalEquivConcreteEval (Expr.binaryApp op x₁ x₂) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁ ih₂
  unfold Partial.evaluate Spec.evaluate
  simp only [ih₁, ih₂, Except.map]
  cases h₁ : Spec.evaluate x₁ request entities <;> simp only [h₁, Except.bind_err, Except.bind_ok]
  case ok v₁ =>
    cases h₂ : Spec.evaluate x₂ request entities <;> simp only [h₂, Except.bind_err, Except.bind_ok]
    case ok v₂ => simp only [EvaluateBinaryApp.on_concrete_eqv_concrete, Except.map]

/--
  Inductive argument that if evaluating an `Expr.binaryApp` on
  well-formed arguments produces `ok` with some value, that is a well-formed
  value as well
-/
theorem partial_eval_wf {x₁ x₂ : Expr} {op : BinaryOp} {request : Partial.Request} {entities : Partial.Entities}
  (ih₁ : EvaluatesToWellFormed x₁ request entities)
  (ih₂ : EvaluatesToWellFormed x₂ request entities) :
  EvaluatesToWellFormed (Expr.binaryApp op x₁ x₂) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  intro pval
  cases hx₁ : Partial.evaluate x₁ request entities
  <;> cases hx₂ : Partial.evaluate x₂ request entities
  <;> simp [hx₁, hx₂]
  case ok.ok pval₁ pval₂ =>
    exact EvaluateBinaryApp.evaluateBinaryApp_wf (ih₁ pval₁ hx₁) (ih₂ pval₂ hx₂) pval

/--
  If partial-evaluating an `Expr.binaryApp` produces `ok` with a concrete
  value, then so would partial-evaluating either of the operands
-/
theorem evals_to_concrete_then_operands_eval_to_concrete {x₁ x₂ : Expr} {op : BinaryOp} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Expr.binaryApp op x₁ x₂) request entities →
  (EvaluatesToConcrete x₁ request entities ∧ EvaluatesToConcrete x₂ request entities)
:= by
  unfold EvaluatesToConcrete
  intro h₁
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  cases hx₁ : Partial.evaluate x₁ request entities
  <;> cases hx₂ : Partial.evaluate x₂ request entities
  <;> simp only [hx₁, hx₂, Except.bind_ok, Except.bind_err] at h₁
  case ok.ok pval₁ pval₂ =>
    have ⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ := EvaluateBinaryApp.returns_concrete_then_operands_eval_to_concrete h₁
    subst pval₁ pval₂
    exact And.intro (by exists v₁) (by exists v₂)

/--
  Inductive argument that if partial-evaluation of an `Expr.binaryApp`
  returns a concrete value, then it returns the same value after any
  substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ x₂ : Expr} {op : BinaryOp} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap)
  (ih₂ : SubstPreservesEvaluationToConcrete x₂ req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Expr.binaryApp op x₁ x₂) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete at *
  unfold Partial.evaluate
  intro h_req v
  specialize ih₁ h_req
  specialize ih₂ h_req
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> cases hx₂ : Partial.evaluate x₂ req entities
  <;> simp only [hx₁, hx₂, Except.ok.injEq, false_implies, forall_const,
    Except.bind_err, Except.bind_ok] at *
  case ok.ok pval₁ pval₂ =>
    cases pval₁ <;> cases pval₂
    <;> simp only [Partial.Value.value.injEq, forall_eq', false_implies, forall_const] at *
    case value.value v₁ v₂ =>
      simp only [ih₁, ih₂, Except.bind_ok]
      exact EvaluateBinaryApp.subst_preserves_evaluation_to_value
    all_goals simp only [Partial.evaluateBinaryApp, Except.ok.injEq, false_implies]

/--
  Inductive argument that if partial-evaluation of an `Expr.binaryApp`
  returns an error, then it also returns an error (not necessarily the same
  error) after any substitution of unknowns

  The proof of `subst_preserves_evaluation_to_value` for this
  request/entities/subsmap is passed in as an argument, because this file can't
  import `Thm/Partial/Evaluation.lean` to access it.
  See #372.
-/
theorem subst_preserves_errors {x₁ x₂ : Expr} {op : BinaryOp} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (h_spetv : ∀ x, SubstPreservesEvaluationToConcrete x req req' entities subsmap)
  (ih₁ : SubstPreservesEvaluationToError x₁ req req' entities subsmap)
  (ih₂ : SubstPreservesEvaluationToError x₂ req req' entities subsmap) :
  SubstPreservesEvaluationToError (Expr.binaryApp op x₁ x₂) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToError at *
  unfold Partial.evaluate
  intro h_req ; specialize ih₁ h_req ; specialize ih₂ h_req
  cases hx₁ : Partial.evaluate x₁ req entities
  <;> cases hx₂ : Partial.evaluate x₂ req entities
  <;> simp only [hx₁, hx₂, false_implies, implies_true, Except.error.injEq] at ih₁ ih₂
  case error.error e₁ e₂ | error.ok e₁ pval₂ =>
    replace ⟨e₁', ih₁⟩ := ih₁ e₁ rfl
    simp [ih₁]
  case ok.error pval₁ e₂ =>
    replace ⟨e₂', ih₂⟩ := ih₂ e₂ rfl
    simp [ih₂]
    cases Partial.evaluate x₁ req' (entities.subst subsmap)
    case error e₁' => exists e₁'
    case ok => exists e₂'
  case ok.ok pval₁ pval₂ =>
    simp only [Except.bind_ok]
    intro e h₁
    have ⟨e', h₂⟩ := EvaluateBinaryApp.subst_preserves_errors subsmap h₁
    cases hx₁' : Partial.evaluate x₁ req' (entities.subst subsmap)
    case error e₁' => exists e₁'
    case ok pval₁' =>
      cases hx₂' : Partial.evaluate x₂ req' (entities.subst subsmap)
      case error e₂' => exists e₂'
      case ok pval₂' =>
        simp only [Except.bind_ok]
        cases pval₁ <;> cases pval₂
        case value.value v₁ v₂ =>
          simp only [h_spetv x₁ h_req v₁ hx₁, Except.ok.injEq] at hx₁' ; subst pval₁'
          simp only [h_spetv x₂ h_req v₂ hx₂, Except.ok.injEq] at hx₂' ; subst pval₂'
          exists e'
        case value.residual v₁ r₂ => exists e
        case residual.value r₁ v₂ => exists e'
        case residual.residual r₁ r₂ => exists e

end Cedar.Thm.Partial.Evaluation.Evaluate.Binary
