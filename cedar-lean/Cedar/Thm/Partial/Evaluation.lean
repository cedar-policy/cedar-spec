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
theorem on_concrete_eqv_concrete_eval (expr : Spec.Expr) (request : Spec.Request) (entities : Spec.Entities)
  (wf : request.WellFormed) :
  Partial.evaluate expr request entities = (Spec.evaluate expr request entities).map Partial.Value.value
:= by
  cases expr <;> simp only [Spec.Expr.asPartialExpr]
  case lit p => simp [Partial.evaluate, Spec.evaluate, Except.map]
  case var v => exact Var.on_concrete_eqv_concrete_eval v request entities wf
  case and x₁ x₂ =>
    have ih₁ := on_concrete_eqv_concrete_eval x₁ request entities wf
    have ih₂ := on_concrete_eqv_concrete_eval x₂ request entities wf
    exact And.on_concrete_eqv_concrete_eval ih₁ ih₂
  case or x₁ x₂ =>
    have ih₁ := on_concrete_eqv_concrete_eval x₁ request entities wf
    have ih₂ := on_concrete_eqv_concrete_eval x₂ request entities wf
    exact Or.on_concrete_eqv_concrete_eval ih₁ ih₂
  case ite x₁ x₂ x₃ =>
    have ih₁ := on_concrete_eqv_concrete_eval x₁ request entities wf
    have ih₂ := on_concrete_eqv_concrete_eval x₂ request entities wf
    have ih₃ := on_concrete_eqv_concrete_eval x₃ request entities wf
    exact Ite.on_concrete_eqv_concrete_eval ih₁ ih₂ ih₃
  case unaryApp op x₁ =>
    have ih₁ := on_concrete_eqv_concrete_eval x₁ request entities wf
    exact Unary.on_concrete_eqv_concrete_eval ih₁
  case binaryApp op x₁ x₂ =>
    have ih₁ := on_concrete_eqv_concrete_eval x₁ request entities wf
    have ih₂ := on_concrete_eqv_concrete_eval x₂ request entities wf
    exact Binary.on_concrete_eqv_concrete_eval ih₁ ih₂
  case getAttr x₁ attr =>
    have ih₁ := on_concrete_eqv_concrete_eval x₁ request entities wf
    exact GetAttr.on_concrete_eqv_concrete_eval ih₁
  case hasAttr x₁ attr =>
    have ih₁ := on_concrete_eqv_concrete_eval x₁ request entities wf
    exact HasAttr.on_concrete_eqv_concrete_eval ih₁
  case set xs =>
    have ih : ∀ x ∈ xs, Partial.evaluate x request entities = (Spec.evaluate x request entities).map Partial.Value.value := by
      intro x h₁
      have := List.sizeOf_lt_of_mem h₁
      apply on_concrete_eqv_concrete_eval x request entities wf
    exact Set.on_concrete_eqv_concrete_eval ih
  case record attrs =>
    have ih : ∀ kv ∈ attrs, Partial.evaluate kv.snd request entities = (Spec.evaluate kv.snd request entities).map Partial.Value.value := by
      intro kv h₁
      have := List.sizeOf_lt_of_mem h₁
      apply on_concrete_eqv_concrete_eval kv.snd request entities wf
    exact Record.on_concrete_eqv_concrete_eval ih
  case call xfn args =>
    have ih : ∀ arg ∈ args, Partial.evaluate arg request entities = (Spec.evaluate arg request entities).map Partial.Value.value := by
      intro arg h₁
      have := List.sizeOf_lt_of_mem h₁
      apply on_concrete_eqv_concrete_eval arg request entities wf
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
  Corollary to the above: partial evaluation with concrete inputs gives a
  concrete value (or an error)
-/
theorem on_concrete_gives_concrete (expr : Spec.Expr) (request : Spec.Request) (entities : Spec.Entities)
  (wf : request.WellFormed) :
  match Partial.evaluate expr request entities with
  | .ok (.value _) => true
  | .ok (.residual _) => false
  | .error _ => true
:= by
  simp only [on_concrete_eqv_concrete_eval expr request entities wf, Except.map]
  split
  <;> rename_i h
  <;> split at h
  <;> simp only [Except.ok.injEq, Except.error.injEq, Partial.Value.value.injEq] at h
  <;> trivial
