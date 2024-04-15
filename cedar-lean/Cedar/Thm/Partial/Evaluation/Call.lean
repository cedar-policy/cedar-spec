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
import Cedar.Thm.Utils

namespace Cedar.Thm.Partial.Evaluation.Call

open Cedar.Spec (Error ExtFun Result)
open Except

/--
  helper lemma: any subexpression of x is a subexpression of any call with x as an argument
-/
theorem operand_subexpression {x₁ x₂ : Partial.Expr} {xs : List Partial.Expr} {xfn : ExtFun} :
  x₁ ∈ xs → x₂ ∈ x₁.subexpressions → x₂ ∈ (Partial.Expr.call xfn xs).subexpressions
:= by
  intro h₁ h₂
  unfold Partial.Expr.subexpressions
  simp [List.append_eq_append]
  right
  have h₃ := List.mem_map_of_mem Partial.Expr.subexpressions h₁
  apply List.mem_join_of_mem h₃ h₂

/--
  helper lemma: if any argument to a `call` contains an unknown, the whole
  expression does
-/
theorem operand_unknown {x : Partial.Expr} {xs : List Partial.Expr} {xfn : ExtFun} :
  x ∈ xs → x.containsUnknown → (Partial.Expr.call xfn xs).containsUnknown
:= by
  unfold Partial.Expr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁ h₂
  replace ⟨subx, h₂⟩ := h₂
  exists subx
  constructor
  case left => apply operand_subexpression h₁ h₂.left
  case right => exact h₂.right

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.call`
  expression gives the same output as concrete-evaluating the `Expr.call` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {xs : List Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} {xfn : ExtFun} :
  (∀ x ∈ xs, Partial.evaluate x request entities = (Spec.evaluate x request entities).map Partial.Value.value) →
  Partial.evaluate (Partial.Expr.call xfn (xs.map₁ λ x => Spec.Expr.asPartialExpr x.val)) request entities = (Spec.evaluate (Spec.Expr.call xfn xs) request entities).map Partial.Value.value
:= by
  intro ih₁
  unfold Partial.evaluate Spec.evaluate
  simp [Except.map, pure, Except.pure, Result.as, Coe.coe, Lean.Internal.coeM, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
  cases h₁ : xs.mapM₁ λ x => Spec.evaluate x.val request entities
  case error e =>
    sorry
  case ok vs =>
    sorry

/--
  Inductive argument for `ResidualsContainUnknowns` for `Partial.Expr.call`
-/
theorem residuals_contain_unknowns {xs : List Partial.Expr} {request : Partial.Request} {entities : Partial.Entities} {xfn : ExtFun} :
  (∀ x ∈ xs, @Partial.Expr.ResidualsContainUnknowns x request entities) →
  @Partial.Expr.ResidualsContainUnknowns (Partial.Expr.call xfn xs) request entities
:= by
  unfold Partial.Expr.ResidualsContainUnknowns
  intro ih₁ r h₁
  -- the entire call evaluated to `.residual r`. we must show that `r` contains
  -- an unknown
  unfold Partial.evaluate at h₁
  cases h₂ : (xs.mapM₁ λ x => Partial.evaluate x.val request entities) <;> simp [h₂] at h₁
  case ok pvals =>
    split at h₁ <;> try simp at h₁
    case h_1 vs _ => cases h₃ : Spec.call xfn vs <;> simp [h₃] at h₁
    case h_2 h₃ =>
      -- naturally, the residual `r` which the call evaluated to, is itself a
      -- `.call` with arguments `pvals.map Partial.Value.asPartialExpr`
      subst h₁
      -- so now we have to show that
      -- `(.call xfn (pvals.map Partial.Value.asPartialExpr))` contains an unknown

      -- in this case (the only remaining case), some argument to the call
      -- evaluated to a residual
      rw [mapM_none_iff_f_none_on_some_element] at h₃
      replace ⟨pval, h₃, h₄⟩ := h₃
      split at h₄ <;> simp at h₄
      case h_2 r =>
        -- `.residual r` is the residual we got when evaluating some argument to
        -- the call
        apply operand_unknown (x := r)
        case _ =>
          simp [List.mem_map]
          exists (Partial.Value.residual r)
        case _ =>
          unfold List.mapM₁ at h₂
          have ⟨⟨arg, h₄⟩, _, h₆⟩ := mem_mapM_ok h₂ h₃
          simp at h₆
          -- `arg` is the argument which evaluated to `.residual r`
          exact ih₁ arg h₄ r h₆

end Cedar.Thm.Partial.Evaluation.Call
