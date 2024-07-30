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
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.Evaluate.AndOr

open Cedar.Data
open Cedar.Partial (Subsmap Unknown)
open Cedar.Spec (Expr Prim Result)

/- ## Lemmas shared by `Expr.and` and `Expr.or` -/

/--
  Inductive argument that, for an `Expr.and` or `Expr.or` with concrete
  request/entities, partial evaluation and concrete evaluation give the same
  output
-/
theorem on_concrete_eqv_concrete_eval {x₁ x₂ : Expr} {request : Spec.Request} {entities : Spec.Entities} :
  PartialEvalEquivConcreteEval x₁ request entities →
  PartialEvalEquivConcreteEval x₂ request entities →
  PartialEvalEquivConcreteEval (Expr.and x₁ x₂) request entities ∧
  PartialEvalEquivConcreteEval (Expr.or x₁ x₂) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁ ih₂
  unfold Partial.evaluate Spec.evaluate
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
  If partial-evaluating an `Expr.and` or `Expr.or` produces `ok`
  with some value, that value is well-formed.
-/
theorem partial_eval_wf (x₁ x₂ : Expr) (request : Partial.Request) (entities : Partial.Entities) :
  EvaluatesToWellFormed (Expr.and x₁ x₂) request entities ∧
  EvaluatesToWellFormed (Expr.or x₁ x₂) request entities
:= by
  unfold EvaluatesToWellFormed Partial.evaluate
  constructor
  all_goals {
    cases hx₁ : Partial.evaluate x₁ request entities
    case error => simp
    case ok pval₁ =>
      cases pval₁
      case residual r₁ => simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
      case value v₁ =>
        cases v₁ <;> simp [Spec.Value.asBool]
        case prim p₁ =>
          cases p₁ <;> simp
          case bool b₁ =>
            cases b₁ <;> simp
            all_goals try {
              -- this dispatches the `false` case for `and`, and the `true` case for `or`
              simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
            }
            intro pval
            cases hx₂ : Partial.evaluate x₂ request entities <;> simp [hx₂]
            case ok pval₂ =>
              cases pval₂ <;> simp
              case residual r₂ => intro h₁ ; subst h₁ ; simp [Partial.Value.WellFormed, Partial.ResidualExpr.WellFormed]
              case value v₂ =>
                cases v₂ <;> try simp
                case prim p₂ =>
                  cases p₂ <;> simp
                  case bool b₂ => intro h₁ ; subst h₁ ; simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
  }

/--
  Inductive argument that if partial-evaluation of an `Expr.and` or
  `Expr.or` returns a concrete value, then it returns the same value
  after any substitution of unknowns
-/
theorem subst_preserves_evaluation_to_value {x₁ x₂ : Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (ih₁ : SubstPreservesEvaluationToConcrete x₁ req req' entities subsmap)
  (ih₂ : SubstPreservesEvaluationToConcrete x₂ req req' entities subsmap) :
  SubstPreservesEvaluationToConcrete (Expr.and x₁ x₂) req req' entities subsmap ∧
  SubstPreservesEvaluationToConcrete (Expr.or x₁ x₂) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToConcrete at *
  unfold Partial.evaluate Spec.Value.asBool
  constructor
  all_goals {
    intro h_req v
    specialize ih₁ h_req
    specialize ih₂ h_req
    cases hx₁ : Partial.evaluate x₁ req entities
    <;> cases hx₂ : Partial.evaluate x₂ req entities
    <;> simp only [hx₁, hx₂, false_implies, forall_const, Except.ok.injEq, Bool.not_eq_true',
      Except.bind_ok, Except.bind_err] at *
    case ok.ok pval₁ pval₂ =>
      cases pval₁
      case residual r₁ => simp only [Except.ok.injEq, false_implies]
      case value v₁ =>
        cases pval₂
        case value v₂ => simp only [ih₁ v₁, ih₂ v₂, Except.bind_ok, imp_self]
        case residual r₂ =>
          simp only [ih₁ v₁, Except.bind_ok]
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

/--
  Inductive argument that if partial-evaluation of an `Expr.and` or
  `Expr.or` returns an error, then it also returns an error (not
  necessarily the same error) after any substitution of unknowns

  The proof of `subst_preserves_evaluation_to_value` for this
  request/entities/subsmap is passed in as an argument, because this file can't
  import `Thm/Partial/Evaluation.lean` to access it.
  See #372.
-/
theorem subst_preserves_errors {x₁ x₂ : Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (h_spetv : ∀ x, SubstPreservesEvaluationToConcrete x req req' entities subsmap)
  (ih₁ : SubstPreservesEvaluationToError x₁ req req' entities subsmap)
  (ih₂ : SubstPreservesEvaluationToError x₂ req req' entities subsmap) :
  SubstPreservesEvaluationToError (Expr.and x₁ x₂) req req' entities subsmap ∧
  SubstPreservesEvaluationToError (Expr.or x₁ x₂) req req' entities subsmap
:= by
  unfold SubstPreservesEvaluationToError at *
  unfold Partial.evaluate
  constructor
  all_goals {
    intro h_req ; specialize ih₁ h_req ; specialize ih₂ h_req
    exact match hx₁ : Partial.evaluate x₁ req entities with
    | .error e₁ => by
      replace ⟨e₁', ih₁⟩ := ih₁ e₁ hx₁
      simp only [ih₁, Bool.not_eq_true', Except.bind_err, Except.error.injEq, exists_eq', implies_true]
    | .ok (.residual r₁) => by
      simp only [Bool.not_eq_true', Except.bind_ok, false_implies, implies_true]
    | .ok (.value v₁) => by
      simp only [h_spetv x₁ h_req v₁ hx₁, Except.bind_ok]
      cases v₁ <;> simp [hx₁, Spec.Value.asBool]
      case prim p₁ =>
        cases p₁ <;> simp at *
        case bool b₁ =>
          cases b₁ <;> simp at *
          all_goals {
            exact match hx₂ : Partial.evaluate x₂ req entities with
            | .error e₂ => by
              replace ⟨e₂', ih₂⟩ := ih₂ e₂ hx₂
              simp only [ih₂, Except.bind_err, Except.error.injEq, exists_eq', implies_true]
            | .ok (.residual r₂) => by simp only [Except.bind_ok, false_implies, implies_true]
            | .ok (.value v₂) => by
              simp only [h_spetv x₂ h_req v₂ hx₂, Except.bind_ok]
              intro e _ ; exists e
          }
  }

end Cedar.Thm.Partial.Evaluation.Evaluate.AndOr
