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

import Cedar.Spec.PartialEvaluator
import Cedar.Thm.PartialEval.Basic

namespace Cedar.Thm

open Cedar.Spec
open Except

/--
  helper lemma: any subexpression of x₁ is a subexpression of (x₁ && x₂)
-/
theorem and_lhs_subexpression {x₁ x₂ x : PartialExpr}
  (h₁ : x ∈ x₁.subexpressions) :
  x ∈ (PartialExpr.and x₁ x₂).subexpressions
:= by
  unfold PartialExpr.subexpressions
  simp [List.append_eq_append]
  right ; left ; assumption

/--
  helper lemma: if LHS of a `PartialExpr.and` contains an unknown, the whole expression does
-/
theorem and_lhs_unknown {x₁ x₂ : PartialExpr}
  (h₁ : x₁.containsUnknown) :
  (PartialExpr.and x₁ x₂).containsUnknown
:= by
  unfold PartialExpr.containsUnknown at *
  rw [List.any_eq_true] at *
  replace ⟨subx, h₁⟩ := h₁
  exists subx
  constructor
  case left => apply and_lhs_subexpression h₁.left
  case right => exact h₁.right

/--
  Inductive argument for `ResidualsContainUnknowns` for `PartialExpr.and`
-/
theorem and_residuals_contain_unknowns {x₁ x₂ : PartialExpr}
  (ih₁ : ResidualsContainUnknowns x₁)
  (ih₂ : ResidualsContainUnknowns x₂) :
  ResidualsContainUnknowns (PartialExpr.and x₁ x₂)
:= by
  unfold ResidualsContainUnknowns at *
  intro req es r
  specialize @ih₁ req es
  specialize @ih₂ req es
  unfold partialEvaluate
  cases h₁ : (partialEvaluate x₁ req es) <;> simp <;> intro h₂
  case error e => cases h₂
  case ok pval₁ =>
    cases pval₁
    case residual r₁ =>
      -- partial evaluating the LHS produced a residual
      specialize ih₁ h₁
      cases h₂
      apply and_lhs_unknown
      assumption
    case value v₁ =>
      -- partial evaluating the LHS produced a value v₁
      cases v₁
      case set | record | ext => cases h₂
      case prim p₁ =>
        cases p₁
        case int | string | entityUID => cases h₂
        case bool b₁ =>
          unfold Value.asBool at h₂
          cases b₁
          case false => cases h₂
          case true =>
            -- partial evaluating the LHS produced ok-true
            cases h₃ : (partialEvaluate x₂ req es) <;> simp [h₃] at h₂
            case error e => cases h₂
            case ok pval₂ =>
              cases pval₂
              case residual r₂ =>
                -- partial evaluating the RHS produced a residual
                specialize ih₂ h₃
                cases h₂
                assumption
              case value v₂ =>
                -- partial evaluating the RHS produced a value v₂
                cases v₂
                case set | record | ext => cases h₂
                case prim p₂ => cases p₂ <;> cases h₂

/--
  Partial-evaluating a `PartialExpr.and` expression produces either .ok bool, a residual,
  or an error
-/
theorem partialexprand_produces_bool_residual_or_error {e₁ e₂ : PartialExpr} {request : PartialRequest} {entities : PartialEntities} :
  match (partialEvaluate (PartialExpr.and e₁ e₂) request entities) with
  | .ok (.value (.prim (.bool _))) => true
  | .ok (.residual _) => true
  | .error _ => true
  | _ => false
:= by
  cases h : partialEvaluate (PartialExpr.and e₁ e₂) request entities <;> simp
  case ok val =>
    cases val <;> simp [partialEvaluate] at h <;>
    generalize (partialEvaluate e₁ request entities) = res₁ at h <;>
    generalize (partialEvaluate e₂ request entities) = res₂ at h
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
  Corollary to the above: Partial-evaluating an `Expr.and` expression
  produces either .ok bool, a residual, or an error
-/
theorem partial_exprand_produces_bool_residual_or_error {e₁ e₂ : Expr} {request : PartialRequest} {entities : PartialEntities} :
  match (partialEvaluate (Expr.and e₁ e₂) request entities) with
  | .ok (.value (.prim (.bool _))) => true
  | .ok (.residual _) => true
  | .error _ => true
  | _ => false
:= by
  unfold Expr.asPartialExpr
  exact @partialexprand_produces_bool_residual_or_error e₁.asPartialExpr e₂.asPartialExpr request entities

end Cedar.Thm
