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
import Cedar.Thm.Data.Control
import Cedar.Thm.Partial.Evaluation.Basic

namespace Cedar.Thm.Partial.Evaluation.AndOr

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (Result)

/- ## Lemmas shared by And.lean and Or.lean -/

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.and` or
  `Partial.Expr.or` gives the same output as concrete-evaluating the
  `Spec.Expr.and` or `Spec.Expr.or` with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {x₁ x₂ : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval x₂ request entities →
  PartialEvalEquivConcreteEval (Spec.Expr.and x₁ x₂) request entities ∧
  PartialEvalEquivConcreteEval (Spec.Expr.or x₁ x₂) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁ ih₂
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only [ih₁, ih₂]
  simp only [Except.map, pure, Except.pure, Result.as, Coe.coe]
  constructor
  all_goals {
    cases h₁ : Spec.evaluate x₁ request entities <;> simp only [Bool.not_eq_true', Except.bind_err, Except.bind_ok]
    case ok v₁ =>
      simp only [Spec.Value.asBool]
      cases v₁ <;> try simp only [Except.bind_err]
      case prim p =>
        cases p <;> simp only [Except.bind_ok, Except.bind_err]
        case bool b =>
          cases b <;> simp only [ite_true, ite_false]
          split <;> simp only [Except.bind_ok, Except.bind_err]
          case h_1 e h₂ => simp only [h₂, Except.bind_err]
          case h_2 v h₂ =>
            simp only [h₂]
            cases v <;> try simp only [Except.bind_err]
            case prim p => cases p <;> simp
  }

/--
  Inductive argument that if partial-evaluation of a `Partial.Expr.and` or
  `Partial.Expr.or` returns a concrete value, then it returns the same value
  after any substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ x₂ : Partial.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.Value}
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap)
  (ih₂ : SubstPreservesEvaluationToConcrete x₂ req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Partial.Expr.and x₁ x₂) req req' entities subsmap ∧
  SubstPreservesEvaluationToConcrete (Partial.Expr.or x₁ x₂) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete at *
  unfold Partial.evaluate Spec.Value.asBool
  constructor
  all_goals {
    intro h_req v
    specialize ih₁ h_req
    specialize ih₂ h_req
    unfold Partial.Expr.subst
    cases hx₁ : Partial.evaluate x₁ req entities
    <;> cases hx₂ : Partial.evaluate x₂ req entities
    <;> simp only [hx₁, false_implies, forall_const, hx₂, Except.ok.injEq, Bool.not_eq_true',
      Except.bind_ok, Except.bind_err] at *
    case ok.ok pval₁ pval₂ =>
      cases pval₁ <;> cases pval₂
      <;> simp only [Partial.Value.value.injEq, Except.ok.injEq, forall_eq', false_implies, forall_const] at *
      case value.value v₁ v₂ =>
        simp only [ih₁, ih₂, Except.bind_ok, imp_self]
      case value.residual v₁ r₂ =>
        simp only [ih₁, Except.bind_ok]
        cases v₁
        case prim p₁ =>
          cases p₁ <;> simp only [Except.bind_ok, Except.bind_err, imp_self]
          case bool b₁ => cases b₁ <;> simp
        case set | record => simp
        case ext x => cases x <;> simp
    case ok.error pval₁ e₂ =>
      cases pval₁
      case residual r₁ => simp only [false_implies, forall_const, Except.ok.injEq]
      case value v₁ =>
        simp only [Partial.Value.value.injEq, forall_eq'] at *
        cases v₁
        case prim p₁ =>
          cases p₁ <;> simp only [Except.bind_ok, Except.bind_err, false_implies]
          case bool b₁ =>
            cases b₁
            <;> simp only [reduceIte, Except.ok.injEq, Partial.Value.value.injEq, false_implies]
            <;> intro h₁ <;> subst v
            simp only [ih₁, Except.bind_ok, reduceIte]
        case set | record => simp
        case ext x => cases x <;> simp
  }

end Cedar.Thm.Partial.Evaluation.AndOr
