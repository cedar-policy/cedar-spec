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

namespace Cedar.Thm.Partial.Evaluation.Unary

open Cedar.Spec
open Except

/--
  helper lemma: any subexpression of x₁ is a subexpression of (unaryApp op x₁)
-/
theorem operand_subexpression {x₁ x : Partial.Expr} {op : UnaryOp} :
  x ∈ x₁.subexpressions → x ∈ (Partial.Expr.unaryApp op x₁).subexpressions
:= by
  intro h₁
  unfold Partial.Expr.subexpressions
  simp [List.append_eq_append]
  right ; assumption

/--
  helper lemma: if the operand of a `unaryApp` contains an unknown, the whole
  expression does
-/
theorem operand_unknown {x₁ : Partial.Expr} {op : UnaryOp} :
  x₁.containsUnknown → (Partial.Expr.unaryApp op x₁).containsUnknown
:= by
  unfold Partial.Expr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁
  replace ⟨subx, h₁⟩ := h₁
  exists subx
  constructor
  case left => apply operand_subexpression h₁.left
  case right => exact h₁.right

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.unaryApp`
  expression gives the same output as concrete-evaluating the `Expr.unaryApp` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {x₁ : Expr} {request : Request} {entities : Entities} {op : UnaryOp} :
  Partial.evaluate x₁ request entities = (evaluate x₁ request entities).map Partial.Value.value →
  Partial.evaluate (Partial.Expr.unaryApp op x₁) request entities = (evaluate (Expr.unaryApp op x₁) request entities).map Partial.Value.value
:= by
  intro ih₁
  unfold Partial.evaluate evaluate
  simp [ih₁]
  simp [Except.map, pure, Except.pure, Result.as, Coe.coe, Lean.Internal.coeM, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
  split <;> simp
  case h_1 e h₁ => simp [h₁]
  case h_2 v h₁ =>
    simp [h₁]
    split
    case h_1 h₂ | h_2 h₂ => simp [h₂]

/--
  Inductive argument for `ResidualsContainUnknowns` for `Partial.Expr.unaryApp`
-/
theorem residuals_contain_unknowns {x₁ : Partial.Expr} {request : Partial.Request} {entities : Partial.Entities} {op : UnaryOp} :
  @Partial.Expr.ResidualsContainUnknowns x₁ request entities →
  @Partial.Expr.ResidualsContainUnknowns (Partial.Expr.unaryApp op x₁) request entities
:= by
  unfold Partial.Expr.ResidualsContainUnknowns
  intro ih₁ r h₁
  unfold Partial.evaluate at h₁
  cases h₂ : (Partial.evaluate x₁ request entities) <;> simp [h₂] at h₁
  case ok pval₁ =>
    cases pval₁ <;> simp at h₁
    case residual r₁ =>
      -- partial evaluating the operand produced a residual
      subst h₁
      apply operand_unknown
      apply @ih₁ r₁ h₂
    case value v₁ =>
      -- partial evaluating the operand produced a value v₁
      cases h₃ : apply₁ op v₁ <;> simp [h₃] at h₁

end Cedar.Thm.Partial.Evaluation.Unary
