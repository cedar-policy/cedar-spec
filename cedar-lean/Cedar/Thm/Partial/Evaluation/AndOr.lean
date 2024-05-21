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

/- ## Lemmas shared by And.lean and Or.lean -/

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
    <;> simp [hx₁, hx₂] at *
    case ok.ok pval₁ pval₂ =>
      cases pval₁ <;> cases pval₂ <;> simp at *
      case value.value v₁ v₂ =>
        simp [ih₁, ih₂]
      case value.residual v₁ r₂ =>
        simp [ih₁]
        cases v₁
        case prim p₁ =>
          cases p₁ <;> simp
          case bool b₁ => cases b₁ <;> simp
        case set s | record m => simp
        case ext x => cases x <;> simp
    case ok.error pval₁ e₂ =>
      cases pval₁ <;> simp at *
      case value v₁ =>
        cases v₁
        case prim p₁ =>
          cases p₁ <;> simp
          case bool b₁ =>
            cases b₁ <;> simp <;> intro h₁ <;> subst v
            simp [ih₁]
        case set s | record m => simp
        case ext x => cases x <;> simp
  }

end Cedar.Thm.Partial.Evaluation.AndOr
