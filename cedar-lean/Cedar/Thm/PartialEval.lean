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
  unfold partialEvaluate evaluate Except.map
  cases expr <;> simp [Expr.asPartialExpr]
  case var v =>
    cases v <;> simp [Request.asPartialRequest]
    case context =>
      split <;> simp
      case h_1 kvs h =>
        -- induction on kvs?
        sorry
      case h_2 =>
        sorry
  case and x₁ x₂ =>
    -- need some kind of inductive argument where we can assume the theorem on the subexpressions
    sorry
  case or x₁ x₂ =>
    sorry
  case ite x₁ x₂ x₃ =>
    sorry
  all_goals {
    sorry
  }

/--
  Corollary to the above: partial evaluation with concrete inputs gives a
  concrete value (or an error)
-/
theorem partial_eval_on_concrete_gives_concrete {expr : Expr} {request : Request} {entities : Entities} :
  match partialEvaluate expr request entities with
  | .ok (.value _) => false
  | .ok (.residual _) => true
  | .error _ => true
:= by
  sorry

/--
  If partial evaluation returns a residual, then that residual expression
  contains an unknown
-/
theorem residuals_contain_unknowns {expr : PartialExpr} {request : PartialRequest} {entities : PartialEntities} {r : PartialExpr} :
  partialEvaluate expr request entities = ok (.residual r) →
  r.containsUnknown
:= by
  unfold partialEvaluate PartialExpr.containsUnknown
  cases expr <;> simp <;> intro h₁
  case var v =>
    cases v <;> simp at h₁
    case principal =>
      cases h₂ : request.principal <;> simp [h₂] at h₁
      case unknown name =>
        subst h₁
        simp [PartialExpr.subexpressions, PartialExpr.isUnknown]
    case action =>
      cases h₂ : request.action <;> simp [h₂] at h₁
      case unknown name =>
        subst h₁
        simp [PartialExpr.subexpressions, PartialExpr.isUnknown]
    case resource =>
      cases h₂ : request.resource <;> simp [h₂] at h₁
      case unknown name =>
        subst h₁
        simp [PartialExpr.subexpressions, PartialExpr.isUnknown]
    case context =>
      sorry
  case and x₁ x₂ =>
    sorry
  all_goals {
    sorry
  }

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
