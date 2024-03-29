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
import Cedar.Spec.Policy
import Cedar.Thm.Data.Control
import Cedar.Thm.PartialEval.Basic

namespace Cedar.Thm.PartialEval.And

open Cedar.Spec
open Except

/--
  helper lemma: any subexpression of x₁ is a subexpression of (x₁ && x₂)
-/
theorem lhs_subexpression {x₁ x₂ x : PartialExpr} :
  x ∈ x₁.subexpressions → x ∈ (PartialExpr.and x₁ x₂).subexpressions
:= by
  intro h₁
  unfold PartialExpr.subexpressions
  simp [List.append_eq_append]
  right ; left ; assumption

/--
  helper lemma: if LHS of a `PartialExpr.and` contains an unknown, the whole expression does
-/
theorem lhs_unknown {x₁ x₂ : PartialExpr} :
  x₁.containsUnknown → (PartialExpr.and x₁ x₂).containsUnknown
:= by
  unfold PartialExpr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁
  replace ⟨subx, h₁⟩ := h₁
  exists subx
  constructor
  case left => apply lhs_subexpression h₁.left
  case right => exact h₁.right

/--
  Inductive argument that partial evaluating a concrete `PartialExpr.and`
  expression gives the same output as concrete-evaluating the `Expr.and` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {x₁ x₂ : Expr} {request : Request} {entities : Entities} :
  partialEvaluate x₁ request entities = (evaluate x₁ request entities).map PartialValue.value →
  partialEvaluate x₂ request entities = (evaluate x₂ request entities).map PartialValue.value →
  partialEvaluate (PartialExpr.and x₁ x₂) request entities = (evaluate (Expr.and x₁ x₂) request entities).map PartialValue.value
:= by
  intro ih₁ ih₂
  unfold partialEvaluate evaluate
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
        case true =>
          split <;> simp only [bind_ok, bind_err]
          case h_1 e h₂ => simp only [h₂, bind_err]
          case h_2 v h₂ =>
            simp only [h₂]
            cases v <;> try simp only [bind_err]
            case prim p => cases p <;> simp only [bind_ok, bind_err, pure, Except.pure]

/--
  Inductive argument for `ResidualsContainUnknowns` for `PartialExpr.and`
-/
theorem residuals_contain_unknowns {x₁ x₂ : PartialExpr} {request : PartialRequest} {entities : PartialEntities}
  (ih₁ : @PartialExpr.ResidualsContainUnknowns x₁ request entities)
  (ih₂ : @PartialExpr.ResidualsContainUnknowns x₂ request entities) :
  @PartialExpr.ResidualsContainUnknowns (PartialExpr.and x₁ x₂) request entities
:= by
  unfold PartialExpr.ResidualsContainUnknowns at *
  intro r h₁
  unfold partialEvaluate at h₁
  cases h₂ : (partialEvaluate x₁ request entities) <;> simp [h₂] at h₁
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
          case true =>
            -- partial evaluating the LHS produced ok-true
            cases h₃ : (partialEvaluate x₂ request entities) <;> simp [h₃] at h₁
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
theorem exprand_produces_bool_residual_or_error {e₁ e₂ : Expr} {request : PartialRequest} {entities : PartialEntities} :
  match (partialEvaluate (Expr.and e₁ e₂) request entities) with
  | .ok (.value (.prim (.bool _))) => true
  | .ok (.residual _) => true
  | .error _ => true
  | _ => false
:= by
  unfold Expr.asPartialExpr
  exact @partialexprand_produces_bool_residual_or_error e₁.asPartialExpr e₂.asPartialExpr request entities

/--
  Corollary to the above: Partial-evaluating a policy produces either
  .ok bool, a residual, or an error
-/
theorem policy_produces_bool_residual_or_error {p : Policy} {request : PartialRequest} {entities : PartialEntities} :
  match (partialEvaluate p.toExpr request entities) with
  | .ok (.value (.prim (.bool _))) => true
  | .ok (.residual _) => true
  | .error _ => true
  | _ => false
:= by
  unfold Policy.toExpr
  apply exprand_produces_bool_residual_or_error

end Cedar.Thm.PartialEval.And
