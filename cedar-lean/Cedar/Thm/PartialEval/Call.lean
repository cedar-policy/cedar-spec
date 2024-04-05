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
import Cedar.Thm.Utils

namespace Cedar.Thm.PartialEval.Call

open Cedar.Spec
open Except

/--
  helper lemma: any subexpression of x is a subexpression of any call with x as an argument
-/
theorem operand_subexpression {x₁ x₂ : PartialExpr} {xs : List PartialExpr} {xfn : ExtFun} :
  x₁ ∈ xs → x₂ ∈ x₁.subexpressions → x₂ ∈ (PartialExpr.call xfn xs).subexpressions
:= by
  intro h₁ h₂
  unfold PartialExpr.subexpressions
  simp [List.append_eq_append]
  right
  have h₃ := List.mem_map_of_mem PartialExpr.subexpressions h₁
  apply List.mem_join_of_mem h₃ h₂

/--
  helper lemma: if any argument to a `call` contains an unknown, the whole
  expression does
-/
theorem operand_unknown {x : PartialExpr} {xs : List PartialExpr} {xfn : ExtFun} :
  x ∈ xs → x.containsUnknown → (PartialExpr.call xfn xs).containsUnknown
:= by
  unfold PartialExpr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁ h₂
  replace ⟨subx, h₂⟩ := h₂
  exists subx
  constructor
  case left => apply operand_subexpression h₁ h₂.left
  case right => exact h₂.right

/--
  Inductive argument that partial evaluating a concrete `PartialExpr.call`
  expression gives the same output as concrete-evaluating the `Expr.call` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {xs : List Expr} {request : Request} {entities : Entities} {xfn : ExtFun} :
  (∀ x ∈ xs, partialEvaluate x request entities = (evaluate x request entities).map PartialValue.value) →
  partialEvaluate (PartialExpr.call xfn (xs.map Expr.asPartialExpr)) request entities = (evaluate (Expr.call xfn xs) request entities).map PartialValue.value
:= by
  intro ih₁
  unfold partialEvaluate evaluate
  simp [Except.map, pure, Except.pure, Result.as, Coe.coe, Lean.Internal.coeM, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
  cases h₁ : xs.mapM₁ λ x => evaluate x.val request entities
  case error e =>
    sorry
  case ok vs =>
    sorry

/--
  Inductive argument for `ResidualsContainUnknowns` for `PartialExpr.call`
-/
theorem residuals_contain_unknowns {xs : List PartialExpr} {request : PartialRequest} {entities : PartialEntities} {xfn : ExtFun} :
  (∀ x ∈ xs, @PartialExpr.ResidualsContainUnknowns x request entities) →
  @PartialExpr.ResidualsContainUnknowns (PartialExpr.call xfn xs) request entities
:= by
  unfold PartialExpr.ResidualsContainUnknowns
  intro ih₁ r h₁
  -- the entire call evaluated to `.residual r`. we must show that `r` contains
  -- an unknown
  unfold partialEvaluate at h₁
  cases h₂ : (xs.mapM₁ λ x => partialEvaluate x.val request entities) <;> simp [h₂] at h₁
  case ok pvals =>
    split at h₁ <;> try simp at h₁
    case h_1 vs _ => cases h₃ : ExtFun.call xfn vs <;> simp [h₃] at h₁
    case h_2 h₃ =>
      -- naturally, the residual `r` which the call evaluated to, is itself a
      -- `.call` with arguments `pvals.map PartialValue.asPartialExpr`
      subst h₁
      -- so now we have to show that
      -- `(.call xfn (pvals.map PartialValue.asPartialExpr))` contains an unknown

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
          exists (PartialValue.residual r)
        case _ =>
          unfold List.mapM₁ at h₂
          have ⟨⟨arg, h₄⟩, _, h₆⟩ := mem_mapM_ok h₂ h₃
          simp at h₆
          -- `arg` is the argument which evaluated to `.residual r`
          exact ih₁ arg h₄ r h₆

end Cedar.Thm.PartialEval.Call
