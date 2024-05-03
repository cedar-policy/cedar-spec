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
import Cedar.Spec.Evaluator
import Cedar.Thm.Partial.Evaluation.And
import Cedar.Thm.Partial.Evaluation.Basic
import Cedar.Thm.Partial.Evaluation.Binary
import Cedar.Thm.Partial.Evaluation.Call
import Cedar.Thm.Partial.Evaluation.GetAttr
import Cedar.Thm.Partial.Evaluation.HasAttr
import Cedar.Thm.Partial.Evaluation.Ite
import Cedar.Thm.Partial.Evaluation.Or
import Cedar.Thm.Partial.Evaluation.Record
import Cedar.Thm.Partial.Evaluation.Set
import Cedar.Thm.Partial.Evaluation.Unary
import Cedar.Thm.Partial.Evaluation.Var
import Cedar.Thm.Data.Control

/-! This file contains theorems about Cedar's partial evaluator. -/

namespace Cedar.Thm.Partial.Evaluation

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (Error Result)

/--
  Partial evaluation with concrete inputs gives the same output as
  concrete evaluation with those inputs
-/
theorem on_concrete_eqv_concrete_eval' (expr : Spec.Expr) (request : Spec.Request) (entities : Spec.Entities)
  (wf : request.WellFormed) :
  PartialEvalEquivConcreteEval expr request entities
:= by
  unfold PartialEvalEquivConcreteEval
  cases expr
  case lit p => simp [Partial.evaluate, Spec.evaluate, Spec.Expr.asPartialExpr, Except.map]
  case var v =>
    have h := Var.on_concrete_eqv_concrete_eval v request entities wf
    unfold PartialEvalEquivConcreteEval at h ; exact h
  case and x₁ x₂ =>
    have ih₁ := on_concrete_eqv_concrete_eval' x₁ request entities wf
    have ih₂ := on_concrete_eqv_concrete_eval' x₂ request entities wf
    exact And.on_concrete_eqv_concrete_eval ih₁ ih₂
  case or x₁ x₂ =>
    have ih₁ := on_concrete_eqv_concrete_eval' x₁ request entities wf
    have ih₂ := on_concrete_eqv_concrete_eval' x₂ request entities wf
    exact Or.on_concrete_eqv_concrete_eval ih₁ ih₂
  case ite x₁ x₂ x₃ =>
    have ih₁ := on_concrete_eqv_concrete_eval' x₁ request entities wf
    have ih₂ := on_concrete_eqv_concrete_eval' x₂ request entities wf
    have ih₃ := on_concrete_eqv_concrete_eval' x₃ request entities wf
    exact Ite.on_concrete_eqv_concrete_eval ih₁ ih₂ ih₃
  case unaryApp op x₁ =>
    have ih₁ := on_concrete_eqv_concrete_eval' x₁ request entities wf
    exact Unary.on_concrete_eqv_concrete_eval ih₁
  case binaryApp op x₁ x₂ =>
    have ih₁ := on_concrete_eqv_concrete_eval' x₁ request entities wf
    have ih₂ := on_concrete_eqv_concrete_eval' x₂ request entities wf
    exact Binary.on_concrete_eqv_concrete_eval ih₁ ih₂
  case getAttr x₁ attr =>
    have ih₁ := on_concrete_eqv_concrete_eval' x₁ request entities wf
    exact GetAttr.on_concrete_eqv_concrete_eval ih₁
  case hasAttr x₁ attr =>
    have ih₁ := on_concrete_eqv_concrete_eval' x₁ request entities wf
    exact HasAttr.on_concrete_eqv_concrete_eval ih₁
  case set xs =>
    have ih : ∀ x ∈ xs, PartialEvalEquivConcreteEval x request entities := by
      intro x h₁
      have := List.sizeOf_lt_of_mem h₁
      apply on_concrete_eqv_concrete_eval' x request entities wf
    exact Set.on_concrete_eqv_concrete_eval ih
  case record attrs =>
    have ih : ∀ kv ∈ attrs, PartialEvalEquivConcreteEval kv.snd request entities := by
      intro kv h₁
      have := List.sizeOf_lt_of_mem h₁
      apply on_concrete_eqv_concrete_eval' kv.snd request entities wf
    exact Record.on_concrete_eqv_concrete_eval ih
  case call xfn args =>
    have ih : ∀ arg ∈ args, PartialEvalEquivConcreteEval arg request entities := by
      intro arg h₁
      have := List.sizeOf_lt_of_mem h₁
      apply on_concrete_eqv_concrete_eval' arg request entities wf
    exact Call.on_concrete_eqv_concrete_eval ih
termination_by expr
decreasing_by
  all_goals simp_wf
  all_goals try omega
  case _ => -- record
    have h₂ : sizeOf kv.snd < sizeOf kv := by simp only [sizeOf, Prod._sizeOf_1] ; omega
    apply Nat.lt_trans h₂
    omega

/--
  Corollary, written with `PartialEvalEquivConcreteEval` spelled out, which is
  easier for consumers
-/
theorem on_concrete_eqv_concrete_eval (expr : Spec.Expr) (request : Spec.Request) (entities : Spec.Entities)
  (wf : request.WellFormed) :
  Partial.evaluate expr request entities = (Spec.evaluate expr request entities).map Partial.Value.value
:= by
  have h := on_concrete_eqv_concrete_eval' expr request entities wf
  unfold PartialEvalEquivConcreteEval at h
  exact h

/--
  `Prop` that a given `Result Partial.Value` is either a concrete value or an
  error, not a residual
-/
def isValueOrError : Result Partial.Value → Prop
  | .ok (.value _) => true
  | .ok (.residual _) => false
  | .error _ => true

/--
  Corollary to the above: partial evaluation with concrete inputs gives a
  concrete value (or an error)
-/
theorem on_concrete_gives_concrete (expr : Spec.Expr) (request : Spec.Request) (entities : Spec.Entities)
  (wf : request.WellFormed) :
  isValueOrError (Partial.evaluate expr request entities)
:= by
  rw [on_concrete_eqv_concrete_eval expr request entities wf]
  simp only [Except.map, isValueOrError]
  split
  <;> rename_i h
  <;> split at h
  <;> simp only [Except.ok.injEq, Except.error.injEq, Partial.Value.value.injEq] at h
  <;> trivial

/--
  subst on a Spec.Expr is id
-/
theorem subst_expr_id (subsmap : Map Unknown Partial.Value) (expr : Spec.Expr) :
  expr.asPartialExpr.subst subsmap = expr.asPartialExpr
:= by
  unfold Partial.Expr.subst
  cases expr <;> simp [Spec.Expr.asPartialExpr]
  case unaryApp op x₁ | getAttr x₁ attr | hasAttr x₁ attr =>
    simp [subst_expr_id subsmap x₁]
  case and x₁ x₂ | or x₁ x₂ | binaryApp op x₁ x₂ =>
    simp [subst_expr_id subsmap x₁, subst_expr_id subsmap x₂]
  case ite x₁ x₂ x₃ =>
    simp [subst_expr_id subsmap x₁, subst_expr_id subsmap x₂, subst_expr_id subsmap x₃]
  case set xs | call xfn xs =>
    simp [List.map₁_eq_map, List.map_map]
    apply List.map_congr
    intro x _
    exact subst_expr_id subsmap x
  case record attrs =>
    simp [List.map_attach₂_snd]
    apply List.map_congr
    intro (a, x) h₁
    simp
    have := List.sizeOf_snd_lt_sizeOf_list h₁
    exact subst_expr_id subsmap x
termination_by expr
