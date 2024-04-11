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

namespace Cedar.Thm.PartialEval.Set

open Cedar.Spec
open Except

/--
  helper lemma: any subexpression of x is a subexpression of any set containing x
-/
theorem operand_subexpression {x₁ x₂ : PartialExpr} {xs : List PartialExpr} :
  x₁ ∈ xs → x₂ ∈ x₁.subexpressions → x₂ ∈ (PartialExpr.set xs).subexpressions
:= by
  intro h₁ h₂
  unfold PartialExpr.subexpressions
  simp [List.append_eq_append]
  right
  have h₃ := List.mem_map_of_mem PartialExpr.subexpressions h₁
  apply List.mem_join_of_mem h₃ h₂

/--
  helper lemma: if any component of a `set` contains an unknown, the whole
  expression does
-/
theorem operand_unknown {x : PartialExpr} {xs : List PartialExpr} :
  x ∈ xs → x.containsUnknown → (PartialExpr.set xs).containsUnknown
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
  Inductive argument that partial evaluating a concrete `PartialExpr.set`
  expression gives the same output as concrete-evaluating the `Expr.set` with
  the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {xs : List Expr} {request : Request} {entities : Entities} :
  (∀ x ∈ xs, partialEvaluate x request entities = (evaluate x request entities).map PartialValue.value) →
  partialEvaluate (PartialExpr.set (xs.map Expr.asPartialExpr)) request entities = (evaluate (Expr.set xs) request entities).map PartialValue.value
:= by
  intro ih₁
  unfold partialEvaluate evaluate
  simp [Except.map, pure, Except.pure, Result.as, Coe.coe, Lean.Internal.coeM, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
  rw [List.mapM₁_eq_mapM (λ x => partialEvaluate x request entities) (xs.map Expr.asPartialExpr)]
  rw [List.mapM₁_eq_mapM (λ x => evaluate x request entities) xs]
  cases h₁ : xs.mapM λ x => evaluate x request entities
  <;> cases h₂ : (xs.map Expr.asPartialExpr).mapM λ x => partialEvaluate x request entities
  <;> simp [h₁, h₂]
  case error.error e₁ e₂ =>
    rw [← Except.error.injEq]
    rw [← h₁]
    sorry
    -- rw [← h₂]
  case ok.ok vals pvals =>
    cases h₃ : pvals.mapM λ pval => match pval with | .value v => some v | .residual _ => none
    case some vals' =>
      have : vals = vals' := by
        -- have to use ih₁
        sorry
      subst vals'
      -- unsure why `rw [h₃]` fails here
      sorry
    case none =>
      simp [mapM_none_iff_f_none_on_some_element] at h₃
      replace ⟨pval, h₃, h₄⟩ := h₃
      cases pval <;> simp at h₄
      case residual r =>
        -- in this case, `partialEvaluate` returned a residual, which shouldn't
        -- be possible on concrete inputs
        have ⟨pexpr, h₄, h₅⟩ := mem_mapM_ok h₂ h₃
        have ⟨x, h₆, h₇⟩ := List.exists_of_mem_map h₄
        subst h₇
        specialize ih₁ x h₆
        simp [ih₁, Except.map] at h₅
        cases h₈ : evaluate x request entities <;> simp [h₈] at h₅
  case ok.error vals e =>
    sorry
  case error.ok e pvals =>
    sorry

/--
  Inductive argument for `ResidualsContainUnknowns` for `PartialExpr.set`
-/
theorem residuals_contain_unknowns {xs : List PartialExpr} {request : PartialRequest} {entities : PartialEntities} :
  (∀ x ∈ xs, @PartialExpr.ResidualsContainUnknowns x request entities) →
  @PartialExpr.ResidualsContainUnknowns (PartialExpr.set xs) request entities
:= by
  unfold PartialExpr.ResidualsContainUnknowns
  intro ih₁ r h₁
  -- the entire set evaluated to `.residual r`. we must show that `r` contains
  -- an unknown
  unfold partialEvaluate at h₁
  cases h₂ : (xs.mapM₁ λ x => partialEvaluate x.val request entities) <;> simp [h₂] at h₁
  case ok pvals =>
    split at h₁ <;> simp at h₁
    -- naturally, the residual `r` which the set evaluated to, is itself a `.set`
    -- with elements `pvals.map PartialValue.asPartialExpr`
    all_goals subst h₁
    -- so now we have to show that `(.set (pvals.map PartialValue.asPartialExpr))`
    -- contains an unknown
    case h_2 h₃ =>
      -- in this case, some element of the set evaluated to a residual
      rw [mapM_none_iff_f_none_on_some_element] at h₃
      replace ⟨pval, h₃, h₄⟩ := h₃
      split at h₄ <;> simp at h₄
      case h_2 r =>
        -- `.residual r` is the residual we got when evaluating some element of
        -- the set
        apply operand_unknown (x := r)
        case _ =>
          simp [List.mem_map]
          exists (PartialValue.residual r)
        case _ =>
          unfold List.mapM₁ at h₂
          have ⟨⟨x, h₄⟩, _, h₆⟩ := mem_mapM_ok h₂ h₃
          simp at h₆
          -- `x` is the set element which evaluated to `.residual r`
          exact ih₁ x h₄ r h₆

end Cedar.Thm.PartialEval.Set
