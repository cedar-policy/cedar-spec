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

namespace Cedar.Thm.Partial.Evaluation.Set

open Cedar.Data
open Cedar.Spec (Result)
open Except

/--
  helper lemma: any subexpression of x is a subexpression of any set containing x
-/
theorem element_subexpression {x₁ x₂ : Partial.Expr} {xs : List Partial.Expr} :
  x₁ ∈ xs → x₂ ∈ x₁.subexpressions → x₂ ∈ (Partial.Expr.set xs).subexpressions
:= by
  intro h₁ h₂
  unfold Partial.Expr.subexpressions
  simp [List.append_eq_append]
  right
  have h₃ := List.mem_map_of_mem Partial.Expr.subexpressions h₁
  apply List.mem_join_of_mem h₃ h₂

/--
  helper lemma: if any component of a `set` contains an unknown, the whole
  expression does
-/
theorem element_unknown {x : Partial.Expr} {xs : List Partial.Expr} :
  x ∈ xs → x.containsUnknown → (Partial.Expr.set xs).containsUnknown
:= by
  unfold Partial.Expr.containsUnknown
  repeat rw [List.any_eq_true]
  intro h₁ h₂
  replace ⟨subx, h₂⟩ := h₂
  exists subx
  constructor
  case left => apply element_subexpression h₁ h₂.left
  case right => exact h₂.right

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.set`
  expression gives the same output as concrete-evaluating the `Spec.Expr.set`
  with the same subexpressions
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {xs : List Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} :
  (∀ x ∈ xs, Partial.evaluate x request entities = (Spec.evaluate x request entities).map Partial.Value.value) →
  Partial.evaluate (Partial.Expr.set (xs.map₁ λ x => Spec.Expr.asPartialExpr x.val)) request entities = (Spec.evaluate (Spec.Expr.set xs) request entities).map Partial.Value.value
:= by
  intro ih₁
  unfold Partial.evaluate Spec.evaluate
  rw [List.map₁_eq_map (λ x => Spec.Expr.asPartialExpr x) xs]
  rw [List.mapM₁_eq_mapM (λ x => Partial.evaluate x request entities) (xs.map Spec.Expr.asPartialExpr)]
  rw [List.mapM₁_eq_mapM (λ x => Spec.evaluate x request entities) xs]
  induction xs
  case nil => simp [Except.map, pure, Except.pure]
  case cons x xs' h_ind =>
    specialize h_ind (by
      intro x' h₁
      exact ih₁ x' (List.mem_cons_of_mem x h₁)
    )
    cases h₁ : Spec.evaluate x request entities
    <;> cases h₂ : Partial.evaluate x request entities
    <;> simp [h₁, h₂]
    case error.error e₁ e₂ =>
      simp [ih₁ x, h₁, Except.map, pure, Except.pure] at h₂
      simp [h₂, Except.map, pure, Except.pure]
    case ok.error val e | error.ok e pval =>
      simp [ih₁ x, h₁, Except.map, pure, Except.pure] at h₂
    case ok.ok val pval =>
      simp [ih₁, h₁, Except.map, pure, Except.pure] at h₂
      subst h₂
      simp [List.mapM_map]
      simp [List.mapM_map] at h_ind
      -- the remaining goal is just a statement about `xs'`, not `x` itself
      -- (don't be confused by the goal's unfortunate use of `x` as a local in a let binding)
      -- so we can dispatch it using `h_ind`
      generalize h₃ : (xs'.mapM λ x => Partial.evaluate x.asPartialExpr request entities) = pres at *
      generalize h₄ : (xs'.mapM λ x => Spec.evaluate x request entities) = sres at *
      cases pres <;> cases sres <;> simp [Except.map, pure, Except.pure] at *
      case error.error e₁ e₂ => exact h_ind
      case ok.error pvals e =>
        -- here, partial evaluation of `xs'` produced `ok` (h₃), while concrete
        -- evaluation of `xs'` produced `error` (h₄).
        -- this contradicts `h_ind`.
        exfalso
        split at h_ind <;> simp at h_ind
      case ok.ok pvals vals =>
        -- here, partial evaluation of `xs'` produced `ok pvals` (h₃), while
        -- concrete evaluation of `xs'` produced `ok vals` (h₄), and we need to
        -- show a particular relationship between `pvals` and `vals` using `h_ind`.
        split at h_ind <;> simp at h_ind
        case h_1 vals' h₂ =>
          simp [h₂]
          exact Set.make_cons h_ind

/--
  Inductive argument for `ResidualsContainUnknowns` for `Partial.Expr.set`
-/
theorem residuals_contain_unknowns {xs : List Partial.Expr} {request : Partial.Request} {entities : Partial.Entities} :
  (∀ x ∈ xs, @Partial.Expr.ResidualsContainUnknowns x request entities) →
  @Partial.Expr.ResidualsContainUnknowns (Partial.Expr.set xs) request entities
:= by
  unfold Partial.Expr.ResidualsContainUnknowns
  intro ih₁ r h₁
  -- the entire set evaluated to `.residual r`. we must show that `r` contains
  -- an unknown
  unfold Partial.evaluate at h₁
  cases h₂ : (xs.mapM₁ λ x => Partial.evaluate x.val request entities) <;> simp [h₂] at h₁
  case ok pvals =>
    split at h₁ <;> simp at h₁
    -- naturally, the residual `r` which the set evaluated to, is itself a `.set`
    -- with elements `pvals.map Partial.Value.asPartialExpr`
    all_goals subst h₁
    -- so now we have to show that `(.set (pvals.map Partial.Value.asPartialExpr))`
    -- contains an unknown
    case h_2 h₃ =>
      -- in this case, some element of the set evaluated to a residual
      rw [mapM_none_iff_f_none_on_some_element] at h₃
      replace ⟨pval, h₃, h₄⟩ := h₃
      split at h₄ <;> simp at h₄
      case h_2 r =>
        -- `.residual r` is the residual we got when evaluating some element of
        -- the set
        apply element_unknown (x := r)
        case _ =>
          simp [List.mem_map]
          exists (Partial.Value.residual r)
        case _ =>
          unfold List.mapM₁ at h₂
          have ⟨⟨x, h₄⟩, _, h₆⟩ := mem_mapM_ok h₂ h₃
          simp at h₆
          -- `x` is the set element which evaluated to `.residual r`
          exact ih₁ x h₄ r h₆

end Cedar.Thm.Partial.Evaluation.Set
