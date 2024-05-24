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

namespace Cedar.Thm.Partial.Evaluation.Or

open Cedar.Data

/--
  If partial-evaluating a `Partial.Expr.or` produces `ok` with a concrete
  value, then so would partial-evaluating either of the operands, unless the
  `or` short-circuits
-/
theorem evals_to_concrete_then_operands_eval_to_concrete {x₁ x₂ : Partial.Expr} {request : Partial.Request} {entities : Partial.Entities} :
  EvaluatesToConcrete (Partial.Expr.or x₁ x₂) request entities →
  Partial.evaluate x₁ request entities = .ok (.value (.prim (.bool true))) ∨
  (EvaluatesToConcrete x₁ request entities ∧ EvaluatesToConcrete x₂ request entities)
:= by
  unfold EvaluatesToConcrete
  intro h₁
  unfold Partial.evaluate at h₁
  replace ⟨v, h₁⟩ := h₁
  cases hx₁ : Partial.evaluate x₁ request entities
  <;> cases hx₂ : Partial.evaluate x₂ request entities
  <;> simp only [hx₁, hx₂, Spec.Value.asBool, Except.bind_ok, Except.bind_err] at h₁
  case ok.ok pval₁ pval₂ =>
    cases pval₁ <;> cases pval₂
    <;> simp only [Except.ok.injEq] at h₁
    case value.value v₁ v₂ =>
      right ; exact And.intro (by exists v₁) (by exists v₂)
    case value.residual v₁ r₂ =>
      cases v₁
      case prim p =>
        cases p <;> simp only [Except.bind_ok, Except.bind_err] at h₁
        case bool b => cases b <;> simp at *
      case set | record => simp at h₁
      case ext x => cases x <;> simp at h₁
  case ok.error pval e =>
    cases pval <;> simp only [Except.ok.injEq] at h₁
    case value v =>
      cases v
      case prim p =>
        cases p <;> simp only [Except.bind_ok, Except.bind_err] at h₁
        case bool b =>
          cases b
          <;> simp only [reduceIte, Except.ok.injEq, Partial.Value.value.injEq] at h₁
          <;> simp [h₁]
      case set | record => simp at h₁
      case ext x => cases x <;> simp at h₁

end Cedar.Thm.Partial.Evaluation.Or
