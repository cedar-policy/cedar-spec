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

namespace Cedar.Thm.PartialEval.Ite

open Cedar.Spec
open Except

/--
  helper lemma: any subexpression of x₁ is a subexpression of (if x₁ then x₂ else x₃)
-/
theorem guard_subexpression {x₁ x₂ x₃ x : PartialExpr} :
  x ∈ x₁.subexpressions → x ∈ (PartialExpr.ite x₁ x₂ x₃).subexpressions
:= by
  intro h₁
  unfold PartialExpr.subexpressions
  simp [List.append_eq_append]
  right ; left ; assumption

/--
  helper lemma: if guard of a `PartialExpr.ite` contains an unknown, the whole expression does
-/
theorem guard_unknown {x₁ x₂ x₃ : PartialExpr} :
  x₁.containsUnknown → (PartialExpr.ite x₁ x₂ x₃).containsUnknown
:= by
  unfold PartialExpr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁
  replace ⟨subx, h₁⟩ := h₁
  exists subx
  constructor
  case left => apply guard_subexpression h₁.left
  case right => exact h₁.right

/--
  Inductive argument that partial evaluating a concrete `PartialExpr.ite`
  expression gives the same output as concrete-evaluating the `Expr.ite` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {x₁ x₂ x₃ : Expr} {request : Request} {entities : Entities} :
  partialEvaluate x₁ request entities = (evaluate x₁ request entities).map PartialValue.value →
  partialEvaluate x₂ request entities = (evaluate x₂ request entities).map PartialValue.value →
  partialEvaluate x₃ request entities = (evaluate x₃ request entities).map PartialValue.value →
  partialEvaluate (PartialExpr.ite x₁ x₂ x₃) request entities = (evaluate (Expr.ite x₁ x₂ x₃) request entities).map PartialValue.value
:= by
  intro ih₁ ih₂ ih₃
  unfold partialEvaluate evaluate
  simp [ih₁, ih₂, ih₃]
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

/--
  Inductive argument for `ResidualsContainUnknowns` for `PartialExpr.ite`
-/
theorem residuals_contain_unknowns {x₁ x₂ x₃ : PartialExpr} {request : PartialRequest} {entities : PartialEntities} :
  @ResidualsContainUnknowns x₁ request entities →
  @ResidualsContainUnknowns x₂ request entities →
  @ResidualsContainUnknowns x₃ request entities →
  @ResidualsContainUnknowns (PartialExpr.ite x₁ x₂ x₃) request entities
:= by
  unfold ResidualsContainUnknowns
  intro ih₁ ih₂ ih₃ r h₁
  unfold partialEvaluate at h₁
  cases h₂ : (partialEvaluate x₁ request entities) <;> simp [h₂] at h₁
  case ok pval₁ =>
    cases pval₁ <;> simp at h₁
    case residual r₁ =>
      -- partial evaluating the guard produced a residual
      subst h₁
      apply guard_unknown
      apply @ih₁ r₁ h₂
    case value v₁ =>
      -- partial evaluating the guard produced a value v₁
      cases v₁ <;> simp [Value.asBool] at h₁
      case prim p₁ =>
        cases p₁
        case int | string | entityUID => cases h₁
        case bool b₁ =>
          cases b₁ <;> simp at h₁
          case false =>
            -- partial evaluating the guard produced ok-false
            cases h₃ : (partialEvaluate x₃ request entities) <;> simp [h₃] at h₁
            case ok pval₂ =>
              cases pval₂ <;> simp at h₁
              case residual r₂ =>
                -- partial evaluating the else-expr produced a residual
                subst h₁
                apply @ih₃ r₂ h₃
          case true =>
            -- partial evaluating the guard produced ok-true
            cases h₃ : (partialEvaluate x₂ request entities) <;> simp [h₃] at h₁
            case ok pval₂ =>
              cases pval₂ <;> simp at h₁
              case residual r₂ =>
                -- partial evaluating the then-expr produced a residual
                subst h₁
                apply @ih₂ r₂ h₃

end Cedar.Thm.PartialEval.Ite
