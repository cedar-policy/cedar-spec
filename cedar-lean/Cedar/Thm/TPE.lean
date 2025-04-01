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

import Cedar.TPE
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.Evaluator
import Cedar.Thm

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

theorem partial_evaluate_is_sound
  {x : TypedExpr}
  {req₁ : Request}
  {es₁ : Entities}
  {req₂ : PartialRequest}
  {es₂ : PartialEntities}
  {env : Environment} :
  TypedExpr.WellTyped env x →
  RequestAndEntitiesMatchEnvironment env req₁ es₁ →
  -- Do we need this hypothesis?
  -- I doubt that because `RequestAndEntitiesMatchEnvironment` ∧ `IsConsistent` → `PartialRequestAndEntitiesMatchEnvironment`
  -- not the other way around, unless we make `IsConsistent` stronger to consider the types of request/entities.
  -- Nevertheless, we should only need one of them.
  PartialRequestAndEntitiesMatchEnvironment env req₂ es₂ →
  IsConsistent req₁ es₁ req₂ es₂ →
  (Spec.evaluate x.toExpr req₁ es₁).toOption = (Residual.evaluate (Cedar.TPE.evaluate x req₂ es₂) req₁ es₁).toOption
:= by
  intro h₁ h₂ h₃ h₄
  induction h₁
  case ite x₁ x₂ x₃ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ hᵢ₇ hᵢ₈ =>
    simp [TypedExpr.toExpr, TPE.evaluate, TPE.ite]
    generalize h₅ : TPE.evaluate x₁ req₂ es₂ = res₁
    split
    case _ =>
      have h₆ := partial_evaluate_value h₂ hᵢ₁ h₄ h₅
      split
      case isTrue heq =>
        simp [Spec.evaluate, h₆, Result.as, Coe.coe, Value.asBool, heq]
        exact hᵢ₇
      case isFalse heq =>
        simp [Spec.evaluate, h₆, Result.as, Coe.coe, Value.asBool, heq]
        exact hᵢ₈
    case _ =>
      simp [h₅, Residual.evaluate] at hᵢ₆
      rcases to_option_right_err hᵢ₆ with ⟨_, h₆⟩
      simp [Spec.evaluate, h₆, Result.as, Residual.evaluate, Except.toOption]
    case _ =>
      simp [←h₅]
      -- "main" case: residual is essentially input expr
      -- essentially proving by case splitting and using induction lemmas
      sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
end Cedar.Thm
