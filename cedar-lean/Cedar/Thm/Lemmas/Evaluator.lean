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

import Cedar.Spec
import Cedar.Thm.Lemmas.Std

/-!
This file contains useful lemmas about the `Evaluator` functions.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Data


theorem and_true_implies_left_true {e₁ e₂ : Expr} {request : Request} {entities : Entities} :
  evaluate (Expr.and e₁ e₂) request entities = .ok true →
  evaluate e₁ request entities = .ok true
:= by
  intro h₁
  simp [evaluate, Result.as] at h₁
  generalize h₂ : (evaluate e₁ request entities) = r₁
  simp [h₂] at h₁
  cases r₁ <;> simp at h₁
  case ok v₁ =>
    generalize h₃ : (Coe.coe v₁ : Result Bool) = rb
    simp [h₃] at h₁
    cases rb <;> simp at h₁
    case ok b =>
      cases b <;> simp at h₁
      simp [Coe.coe, Value.asBool] at h₃
      cases v₁ <;> try simp at h₃
      case _ p₁ =>
        cases p₁ <;> simp at h₃
        simp [h₃]

theorem and_true_implies_right_true {e₁ e₂ : Expr} {request : Request} {entities : Entities} :
  evaluate (Expr.and e₁ e₂) request entities = .ok true →
  evaluate e₂ request entities = .ok true
:= by
  intro h₁
  rcases (and_true_implies_left_true h₁) with h₂
  simp [evaluate, h₂, Result.as, Coe.coe, Value.asBool] at h₁
  generalize h₃ : (evaluate e₂ request entities) = r₂
  simp [h₃] at h₁
  cases r₂ <;> simp [Lean.Internal.coeM] at h₁
  case ok v₂ =>
    cases v₂ <;> try simp at h₁
    case _ p₂ =>
      cases p₂ <;> simp at h₁
      case _ b =>
        cases b <;> simp at h₁
        rfl

end Cedar.Thm