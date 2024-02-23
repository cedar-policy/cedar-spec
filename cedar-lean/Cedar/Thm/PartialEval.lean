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
