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

import Cedar.Spec.Evaluator
import Cedar.Spec.PartialEvaluator
import Cedar.Thm.PartialEval.And
import Cedar.Thm.PartialEval.Basic
import Cedar.Thm.PartialEval.Binary
import Cedar.Thm.PartialEval.Call
import Cedar.Thm.PartialEval.GetAttr
import Cedar.Thm.PartialEval.HasAttr
import Cedar.Thm.PartialEval.Ite
import Cedar.Thm.PartialEval.Or
import Cedar.Thm.PartialEval.Set
import Cedar.Thm.PartialEval.Unary
import Cedar.Thm.Data.Control
import Cedar.Thm.Utils

/-! This file contains theorems about Cedar's partial evaluator. -/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Except

/--
  Partial evaluation with concrete inputs gives the same output as
  concrete evaluation with those inputs
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {expr : Expr} {request : Request} {entities : Entities} :
  partialEvaluate expr request entities = (evaluate expr request entities).map PartialValue.value
:= by
  cases expr <;> simp only [Expr.asPartialExpr]
  case lit p => simp [partialEvaluate, evaluate, Except.map]
  case var v =>
    unfold partialEvaluate evaluate
    cases v <;> simp only [Request.asPartialRequest, Except.map]
    case context =>
      split
      case h_1 kvs h =>
        simp
        -- rw [Map.mapOnValues_eq_make_map] at h
        sorry
      case h_2 =>
        sorry
  case and x₁ x₂ =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    have ih₂ := @partial_eval_on_concrete_eqv_concrete_eval x₂ request entities
    exact PartialEval.And.partial_eval_on_concrete_eqv_concrete_eval ih₁ ih₂
  case or x₁ x₂ =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    have ih₂ := @partial_eval_on_concrete_eqv_concrete_eval x₂ request entities
    exact PartialEval.Or.partial_eval_on_concrete_eqv_concrete_eval ih₁ ih₂
  case ite x₁ x₂ x₃ =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    have ih₂ := @partial_eval_on_concrete_eqv_concrete_eval x₂ request entities
    have ih₃ := @partial_eval_on_concrete_eqv_concrete_eval x₃ request entities
    exact PartialEval.Ite.partial_eval_on_concrete_eqv_concrete_eval ih₁ ih₂ ih₃
  case unaryApp op x₁ =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    exact PartialEval.Unary.partial_eval_on_concrete_eqv_concrete_eval ih₁
  case binaryApp op x₁ x₂ =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    have ih₂ := @partial_eval_on_concrete_eqv_concrete_eval x₂ request entities
    exact PartialEval.Binary.partial_eval_on_concrete_eqv_concrete_eval ih₁ ih₂
  case getAttr x₁ attr =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    exact PartialEval.GetAttr.partial_eval_on_concrete_eqv_concrete_eval ih₁
  case hasAttr x₁ attr =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    exact PartialEval.HasAttr.partial_eval_on_concrete_eqv_concrete_eval ih₁
  case set xs =>
    have ih : ∀ x ∈ xs, partialEvaluate x request entities = (evaluate x request entities).map PartialValue.value := by
      intro x h₁
      apply @partial_eval_on_concrete_eqv_concrete_eval x request entities
    exact PartialEval.Set.partial_eval_on_concrete_eqv_concrete_eval ih
  case record attrs =>
    sorry
  case call xfn args =>
    have ih : ∀ arg ∈ args, partialEvaluate arg request entities = (evaluate arg request entities).map PartialValue.value := by
      intro arg h₁
      apply @partial_eval_on_concrete_eqv_concrete_eval arg request entities
    exact PartialEval.Call.partial_eval_on_concrete_eqv_concrete_eval ih

/--
  Corollary to the above: partial evaluation with concrete inputs gives a
  concrete value (or an error)
-/
theorem partial_eval_on_concrete_gives_concrete {expr : Expr} {request : Request} {entities : Entities} :
  match partialEvaluate expr request entities with
  | .ok (.value _) => true
  | .ok (.residual _) => false
  | .error _ => true
:= by
  simp [partial_eval_on_concrete_eqv_concrete_eval, Except.map]
  split <;> rename_i h <;> split at h <;> simp at h <;> trivial

/--
  If partial evaluation returns a residual, then that residual expression
  contains an unknown
-/
theorem residuals_contain_unknowns {expr : PartialExpr} {request : PartialRequest} {entities : PartialEntities}
  (wf : entities.AllWellFormed)
  (ih : PartialEntities.ResidualsContainUnknowns entities) :
  ∀ r,
  partialEvaluate expr request entities = ok (.residual r) →
  r.containsUnknown
:= by
  cases expr
  case lit p =>
    unfold partialEvaluate
    intro r h₁
    simp at h₁
  case unknown name =>
    unfold partialEvaluate
    intro r h₁
    simp at h₁
    subst h₁
    unfold PartialExpr.containsUnknown PartialExpr.subexpressions
    simp [List.any_eq_true, PartialExpr.isUnknown]
  case var v =>
    unfold partialEvaluate
    intro r h₁
    cases v <;> simp at h₁
    case principal =>
      cases h₂ : request.principal <;> simp [h₂] at h₁
      case unknown name =>
        subst h₁
        simp [PartialExpr.containsUnknown, PartialExpr.subexpressions, PartialExpr.isUnknown]
    case action =>
      cases h₂ : request.action <;> simp [h₂] at h₁
      case unknown name =>
        subst h₁
        simp [PartialExpr.containsUnknown, PartialExpr.subexpressions, PartialExpr.isUnknown]
    case resource =>
      cases h₂ : request.resource <;> simp [h₂] at h₁
      case unknown name =>
        subst h₁
        simp [PartialExpr.containsUnknown, PartialExpr.subexpressions, PartialExpr.isUnknown]
    case context =>
      sorry
  case and x₁ x₂ =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf ih
    have ih₂ := @residuals_contain_unknowns x₂ request entities wf ih
    rw [← PartialExpr.ResidualsContainUnknowns] at *
    exact PartialEval.And.residuals_contain_unknowns ih₁ ih₂
  case or x₁ x₂ =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf ih
    have ih₂ := @residuals_contain_unknowns x₂ request entities wf ih
    rw [← PartialExpr.ResidualsContainUnknowns] at *
    exact PartialEval.Or.residuals_contain_unknowns ih₁ ih₂
  case ite x₁ x₂ x₃ =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf ih
    have ih₂ := @residuals_contain_unknowns x₂ request entities wf ih
    have ih₃ := @residuals_contain_unknowns x₃ request entities wf ih
    rw [← PartialExpr.ResidualsContainUnknowns] at *
    exact PartialEval.Ite.residuals_contain_unknowns ih₁ ih₂ ih₃
  case unaryApp op x₁ =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf ih
    exact PartialEval.Unary.residuals_contain_unknowns ih₁
  case binaryApp op x₁ x₂ =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf ih
    have ih₂ := @residuals_contain_unknowns x₂ request entities wf ih
    rw [← PartialExpr.ResidualsContainUnknowns] at *
    exact PartialEval.Binary.residuals_contain_unknowns ih₁ ih₂
  case getAttr x₁ attr =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf ih
    exact PartialEval.GetAttr.residuals_contain_unknowns wf ih₁ ih
  case hasAttr x₁ attr =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf ih
    exact PartialEval.HasAttr.residuals_contain_unknowns ih₁
  case set xs =>
    have ih : ∀ x ∈ xs, @PartialExpr.ResidualsContainUnknowns x request entities := by
      intro x h₁
      unfold PartialExpr.ResidualsContainUnknowns
      apply @residuals_contain_unknowns x request entities wf ih
    exact PartialEval.Set.residuals_contain_unknowns ih
  case record attrs =>
    sorry
  case call xfn args =>
    have ih : ∀ arg ∈ args, @PartialExpr.ResidualsContainUnknowns arg request entities := by
      intro arg h₁
      unfold PartialExpr.ResidualsContainUnknowns
      apply @residuals_contain_unknowns arg request entities wf ih
    exact PartialEval.Call.residuals_contain_unknowns ih

/--
  If partial evaluation returns a concrete value, then it returns the same value
  after any substitution of unknowns
-/
theorem subst_preserves_evaluation_to_literal {expr : PartialExpr} {req req' : PartialRequest} {entities : PartialEntities} {v : Value} {subsmap : Map String RestrictedPartialValue} :
  partialEvaluate expr req entities = ok (.value v) →
  req.subst subsmap = some req' →
  partialEvaluate (expr.subst subsmap) req' (entities.subst subsmap) = ok (.value v)
:= by
  unfold partialEvaluate PartialExpr.subst
  cases expr <;> simp <;> intro h₁ h₂
  case lit p => simp [h₁]
  case var v =>
    cases v <;> simp at *
    case principal | action | resource =>
      split at h₁ <;> simp at h₁
      subst h₁
      split <;> simp
      case _ h₃ _ _ h₄ =>
        -- invoke a lemma about PartialRequest.subst
        sorry
      case _ h₃ _ _ h₄ =>
        -- invoke a lemma about PartialRequest.subst
        sorry
    case context =>
      split at h₁ <;> simp at h₁
      case _ kvs h₃ =>
        subst h₁
        sorry
  case and x₁ x₂ =>
    sorry
  all_goals {
    sorry
  }

/--
  If partial evaluation returns an error, then it returns the same error
  after any substitution of unknowns
-/
theorem subst_preserves_errors {expr : PartialExpr} {req req' : PartialRequest} {entities : PartialEntities} {e : Error} {subsmap : Map String RestrictedPartialValue} :
  req.subst subsmap = some req' →
  partialEvaluate expr req entities = error e →
  partialEvaluate (expr.subst subsmap) req' (entities.subst subsmap) = error e
:= by
  unfold partialEvaluate PartialExpr.subst
  cases expr <;> simp <;> intro h₁ h₂
  case var v =>
    cases v <;> simp at *
    case context => split at h₂ <;> simp at h₂
  case and x₁ x₂ =>
    sorry
  all_goals {
    sorry
  }

/--
  Corollary (contrapositive) of the above:
  If partial evaluation returns ok after any substitution of unknowns,
  then it must return ok before that substitution
-/
theorem subst_preserves_errors_mt {expr : PartialExpr} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String RestrictedPartialValue} :
  req.subst subsmap = some req' →
  (partialEvaluate (expr.subst subsmap) req' (entities.subst subsmap)).isOk →
  (partialEvaluate expr req entities).isOk
:= by
  unfold Except.isOk Except.toBool
  intro h₁ h₂
  by_contra h₃
  split at h₃ <;> simp at h₃
  case _ e h₄ =>
    have h₅ := subst_preserves_errors h₁ h₄
    simp [h₅] at h₂

/--
  Re-evaluation with a substitution on the residual expression, is equivalent to
  substituting first and then evaluating on the original expression.
-/
theorem eval_on_residuals_eqv_substituting_first {expr : PartialExpr} {req req' : PartialRequest} {entities : PartialEntities} {subsmap: Map String RestrictedPartialValue} :
  req.subst subsmap = some req' →
  (partialEvaluate expr req entities >>= λ residual => partialEvaluate (residual.subst subsmap).asPartialExpr req' (entities.subst subsmap)) =
  partialEvaluate (expr.subst subsmap) req' (entities.subst subsmap)
:= by
  sorry
