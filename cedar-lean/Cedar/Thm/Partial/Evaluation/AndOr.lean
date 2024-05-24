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
import Cedar.Thm.Partial.Evaluation.WellFormed

namespace Cedar.Thm.Partial.Evaluation.AndOr

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (Prim)

/- ## Lemmas shared by And.lean and Or.lean -/

/--
  If partial-evaluating a `Partial.Expr.and` or `Partial.Expr.or` produces `ok`
  with some value, that value is well-formed.
-/
theorem partial_eval_wf (x₁ x₂ : Partial.Expr) (request : Partial.Request) (entities : Partial.Entities) :
  (∀ pval, Partial.evaluate (Partial.Expr.and x₁ x₂) request entities = .ok pval → pval.WellFormed) ∧
  (∀ pval, Partial.evaluate (Partial.Expr.or x₁ x₂) request entities = .ok pval → pval.WellFormed)
:= by
  unfold Partial.evaluate
  constructor
  all_goals {
    cases hx₁ : Partial.evaluate x₁ request entities
    case error => simp
    case ok pval₁ =>
      cases pval₁ <;> simp
      case residual r₁ => simp [Partial.Value.WellFormed]
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
              case residual r₂ => intro h₁ ; subst h₁ ; simp [Partial.Value.WellFormed]
              case value v₂ =>
                cases v₂ <;> try simp
                case prim p₂ =>
                  cases p₂ <;> simp
                  case bool b₂ => intro h₁ ; subst h₁ ; simp [Partial.Value.WellFormed, Spec.Value.WellFormed, Prim.WellFormed]
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
    <;> simp only [hx₁, hx₂, false_implies, forall_const, Except.ok.injEq, Bool.not_eq_true',
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
