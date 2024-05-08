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
import Cedar.Spec.Policy
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.Basic

namespace Cedar.Thm.Partial.Evaluation.Set

open Cedar.Data
open Cedar.Spec (Result)

/--
  Lemma (used for both the Set and Call cases):

  Inductive argument that `mapM`'ing partial evaluation over a list of concrete
  exprs gives the same output as `mapM`'ing concrete evaluation over the same
  exprs
-/
theorem mapM_partial_eval_eqv_concrete_eval {xs : List Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} :
  (∀ x ∈ xs, PartialEvalEquivConcreteEval x request entities) →
  xs.mapM (λ x => Partial.evaluate x.asPartialExpr request entities) = (xs.mapM (Spec.evaluate · request entities)).map λ vs => vs.map Partial.Value.value
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  induction xs
  case nil => simp [Except.map, pure, Except.pure]
  case cons hd tl ih =>
    specialize ih (by
      intro x' h₁
      exact ih₁ x' (List.mem_cons_of_mem hd h₁)
    )
    cases h₁ : Spec.evaluate hd request entities
    <;> cases h₂ : Partial.evaluate hd request entities
    <;> simp only [h₁, h₂, List.mapM_cons, Except.bind_err, Except.bind_ok]
    case error.error e₁ e₂ =>
      simp only [ih₁ hd, h₁, Except.map, List.mem_cons, true_or, Except.error.injEq] at h₂
      simp [h₂, Except.map]
    case ok.error val e | error.ok e pval =>
      simp [ih₁ hd, h₁, Except.map] at h₂
    case ok.ok val pval =>
      simp only [ih₁, h₁, Except.map, List.mem_cons, true_or, Except.ok.injEq] at h₂
      subst h₂
      -- the remaining goal is just a statement about `tl`, not `hd` itself
      -- so we can dispatch it using `ih`
      generalize h₃ : (tl.mapM λ x => Partial.evaluate x.asPartialExpr request entities) = pres at *
      generalize h₄ : (tl.mapM λ x => Spec.evaluate x request entities) = sres at *
      cases pres <;> cases sres
      <;> simp only [Except.map, pure, Except.pure, List.mem_cons, Except.error.injEq, Except.ok.injEq, Except.bind_ok, Except.bind_err, List.cons.injEq, List.map_cons, forall_eq_or_imp, true_and] at *
      case error.error e₁ e₂ => exact ih
      case ok.ok pvals vals => exact ih

/--
  Inductive argument that partial evaluating a concrete `Partial.Expr.set`
  expression gives the same output as concrete-evaluating the `Spec.Expr.set`
  with the same subexpressions
-/
theorem on_concrete_eqv_concrete_eval {xs : List Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} :
  (∀ x ∈ xs, PartialEvalEquivConcreteEval x request entities) →
  PartialEvalEquivConcreteEval (Spec.Expr.set xs) request entities
:= by
  unfold PartialEvalEquivConcreteEval
  intro ih₁
  unfold Partial.evaluate Spec.evaluate Spec.Expr.asPartialExpr
  simp only
  rw [List.map₁_eq_map Spec.Expr.asPartialExpr]
  rw [List.mapM₁_eq_mapM (Partial.evaluate · request entities)]
  rw [List.mapM₁_eq_mapM (Spec.evaluate · request entities)]
  rw [List.mapM_map]
  rw [mapM_partial_eval_eqv_concrete_eval ih₁]
  cases xs.mapM (Spec.evaluate · request entities) <;> simp only [Except.map, Except.bind_err, Except.bind_ok]
  case ok vs => simp [List.mapM_map, List.mapM_some]

end Cedar.Thm.Partial.Evaluation.Set
