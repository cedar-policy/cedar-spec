/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
import Cedar.Spec.Policy
import Cedar.Thm.Data.Control
import Cedar.Thm.Partial.Evaluation.Basic

namespace Cedar.Thm.Partial.Evaluation.Or

open Cedar.Spec
open Except

/--
  helper lemma: any subexpression of x₁ is a subexpression of (x₁ || x₂)
-/
theorem lhs_subexpression {x₁ x₂ x : Partial.Expr} :
  x ∈ x₁.subexpressions → x ∈ (Partial.Expr.or x₁ x₂).subexpressions
:= by
  intro h₁
  unfold Partial.Expr.subexpressions
  simp [List.append_eq_append]
  right ; left ; assumption

/--
  helper lemma: if LHS of a `Partial.Expr.or` contains an unknown, the whole expression does
-/
theorem lhs_unknown {x₁ x₂ : Partial.Expr} :
  x₁.containsUnknown → (Partial.Expr.or x₁ x₂).containsUnknown
:= by
  unfold Partial.Expr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁
  replace ⟨subx, h₁⟩ := h₁
  exists subx
  constructor
  case left => apply lhs_subexpression h₁.left
  case right => exact h₁.right

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.or`
  expression gives the same output as concrete-evaluating the `Expr.or` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {x₁ x₂ : Expr} {request : Request} {entities : Entities} :
  Partial.evaluate x₁ request entities = (evaluate x₁ request entities).map Partial.Value.value →
  Partial.evaluate x₂ request entities = (evaluate x₂ request entities).map Partial.Value.value →
  Partial.evaluate (Partial.Expr.or x₁ x₂) request entities = (evaluate (Expr.or x₁ x₂) request entities).map Partial.Value.value
:= by
  intro ih₁ ih₂
  unfold Partial.evaluate evaluate
  simp [ih₁, ih₂]
  simp [Except.map, pure, Except.pure, Result.as, Coe.coe, Lean.Internal.coeM, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
  split <;> simp
  case h_1 e h₁ => simp [h₁]
  case h_2 v h₁ =>
    simp [h₁, Value.asBool]
    cases v <;> try simp only [bind_err]
    case prim p =>
      cases p <;> simp only [bind_ok, bind_err]
      case bool b =>
        cases b <;> simp only [ite_true, ite_false]
        case false =>
          split <;> simp only [bind_ok, bind_err]
          case h_1 e h₂ => simp only [h₂, bind_err]
          case h_2 v h₂ =>
            simp only [h₂]
            cases v <;> try simp only [bind_err]
            case prim p => cases p <;> simp only [bind_ok, bind_err, pure, Except.pure]

/--
  Inductive argument for `ResidualsContainUnknowns` for `Partial.Expr.or`
-/
theorem residuals_contain_unknowns {x₁ x₂ : Partial.Expr} {request : Partial.Request} {entities : Partial.Entities}
  (ih₁ : @Partial.Expr.ResidualsContainUnknowns x₁ request entities)
  (ih₂ : @Partial.Expr.ResidualsContainUnknowns x₂ request entities) :
  @Partial.Expr.ResidualsContainUnknowns (Partial.Expr.or x₁ x₂) request entities
:= by
  unfold Partial.Expr.ResidualsContainUnknowns at *
  intro r h₁
  unfold Partial.evaluate at h₁
  cases h₂ : (Partial.evaluate x₁ request entities) <;> simp [h₂] at h₁
  case ok pval₁ =>
    cases pval₁ <;> simp at h₁
    case residual r₁ =>
      -- partial evaluating the LHS produced a residual
      subst h₁
      apply lhs_unknown
      apply @ih₁ r₁ h₂
    case value v₁ =>
      -- partial evaluating the LHS produced a value v₁
      cases v₁ <;> simp [Value.asBool] at h₁
      case prim p₁ =>
        cases p₁
        case int | string | entityUID => cases h₁
        case bool b₁ =>
          cases b₁ <;> simp at h₁
          case false =>
            -- partial evaluating the LHS produced ok-false
            cases h₃ : (Partial.evaluate x₂ request entities) <;> simp [h₃] at h₁
            case ok pval₂ =>
              cases pval₂ <;> simp at h₁
              case residual r₂ =>
                -- partial evaluating the RHS produced a residual
                subst h₁
                apply @ih₂ r₂ h₃
              case value v₂ =>
                -- partial evaluating the RHS produced a value v₂
                cases v₂ <;> try simp at h₁
                case prim p₂ => cases p₂ <;> cases h₁

/--
  Partial-evaluating a `Partial.Expr.or` expression produces either .ok bool, a residual,
  or an error
-/
theorem partialexpror_produces_bool_residual_or_error {e₁ e₂ : Partial.Expr} {request : Partial.Request} {entities : Partial.Entities} :
  match (Partial.evaluate (Partial.Expr.or e₁ e₂) request entities) with
  | .ok (.value (.prim (.bool _))) => true
  | .ok (.residual _) => true
  | .error _ => true
  | _ => false
:= by
  cases h : Partial.evaluate (Partial.Expr.or e₁ e₂) request entities <;> simp
  case ok val =>
    cases val <;> simp [Partial.evaluate] at h <;>
    generalize (Partial.evaluate e₁ request entities) = res₁ at h <;>
    generalize (Partial.evaluate e₂ request entities) = res₂ at h
    case residual r => simp
    case value v =>
      simp [Value.asBool] at h
      cases res₁ <;> cases res₂ <;> try cases h
      case ok.error pval₁ err₂ =>
        cases pval₁ <;> try cases h
        case value v₁ =>
          cases v₁ <;> try cases h
          case prim p₁ =>
            cases p₁ <;> try cases h
            case bool b =>
              cases b <;> cases h
              split <;> trivial
      case ok.ok pval₁ pval₂ =>
        cases pval₁ <;> cases pval₂ <;> try cases h
        case value.value v₁ v₂ =>
          cases v₁ <;> cases v₂ <;> try cases h
          case prim.prim p₁ p₂ =>
            cases p₁ <;> cases p₂ <;> try cases h
            case bool.bool b₁ b₂ =>
              cases b₁ <;> cases b₂ <;> cases h
              all_goals {
                split <;> trivial
              }
            case bool.int b₁ _ | bool.string b₁ _ | bool.entityUID b₁ _ =>
              cases b₁ <;> cases h
              split <;> trivial
          case prim.set p₁ _ | prim.record p₁ _ | prim.ext p₁ _ =>
            cases p₁ <;> try cases h
            case bool b₁ =>
              cases b₁ <;> cases h
              split <;> trivial
        case value.residual v₁ r₂ =>
          cases v₁ <;> try cases h
          case prim p₁ =>
            cases p₁ <;> try cases h
            case bool b₁ =>
              cases b₁ <;> cases h
              split <;> trivial

/--
  Corollary to the above: Partial-evaluating an `Expr.or` expression
  produces either .ok bool, a residual, or an error
-/
theorem expror_produces_bool_residual_or_error {e₁ e₂ : Expr} {request : Partial.Request} {entities : Partial.Entities} :
  match (Partial.evaluate (Expr.or e₁ e₂) request entities) with
  | .ok (.value (.prim (.bool _))) => true
  | .ok (.residual _) => true
  | .error _ => true
  | _ => false
:= by
  unfold Expr.asPartialExpr
  exact @partialexpror_produces_bool_residual_or_error e₁.asPartialExpr e₂.asPartialExpr request entities

end Cedar.Thm.Partial.Evaluation.Or
