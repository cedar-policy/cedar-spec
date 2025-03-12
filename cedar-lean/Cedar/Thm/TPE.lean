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
import Cedar.Thm
import Cedar.Thm.Validation.TypedExpr
import Cedar.Thm.Data

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm.TPE
open Cedar.Thm

theorem partialEvaluate_is_sound
  {x : TypedExpr}
  {req₁ : Request}
  {es₁ : Entities}
  {req₂ : PartialRequest}
  {es₂ : PartialEntities}
  {env : Environment} :
  TypedExpr.WellTyped env x →
  RequestAndEntitiesMatchEnvironment env req₁ es₁ →
  PartialRequestAndEntitiesMatchEnvironment env req₂ es₂ →
  IsConsistent env req₁ es₁ req₂ es₂ →
  (Spec.evaluate x.toExpr req₁ es₁).toOption = (Residual.evaluate (Cedar.TPE.evaluate x req₂ es₂) req₁ es₁).toOption
:= by
  intro h₀ h₁ h₂ h₃
  cases x
  case and x₁ x₂ ty =>
    sorry
  case lit => sorry
  case var => sorry
  case ite cond thenExpr elseExpr ty =>
    cases h₀
    rename_i h₄ h₅ h₆ h₇ h₈
    simp [TypedExpr.toExpr, Spec.evaluate]
    generalize hᵢ₁ : Spec.evaluate cond.toExpr req₁ es₁ = res₁
    cases res₁
    case _ =>
      sorry
    case _ v₁ =>
      have hᵢ₁' := typechecked_is_well_typed h₁ h₄ hᵢ₁
      simp [CedarType.isBool] at h₅
      split at h₅
      · rename_i heq
        simp only [heq] at hᵢ₁'
        have ⟨b, hᵢ₁'⟩ := instance_of_bool_is_bool hᵢ₁'
        simp [hᵢ₁', Result.as, Coe.coe, Value.asBool]
        have hᵢ₁₁ : (TPE.evaluate cond req₂ es₂).evaluate req₁ es₁ = .ok v₁
        := by sorry
        simp [TPE.evaluate, TPE.ite]
        split <;> split
        · rename_i  hb _ _ _ heq₁
          simp [heq₁, Residual.evaluate, hᵢ₁', hb] at hᵢ₁₁
          simp [hᵢ₁₁]
          exact partialEvaluate_is_sound h₆ h₁ h₂ h₃
        · rename_i heq₁
          simp [heq₁, Residual.evaluate] at hᵢ₁₁
        · rename_i hb _ _ _
          simp [Residual.evaluate, hᵢ₁₁, hᵢ₁', hb, Value.asBool]
          exact partialEvaluate_is_sound h₆ h₁ h₂ h₃
        · rename_i hb _ _ _ heq₁
          simp at hb
          simp [heq₁, Residual.evaluate, hᵢ₁', hb] at hᵢ₁₁
          simp [hᵢ₁₁]
          exact partialEvaluate_is_sound h₇ h₁ h₂ h₃
        · rename_i heq₁
          simp [heq₁, Residual.evaluate] at hᵢ₁₁
        · rename_i hb _ _ _
          simp at hb
          simp [hb] at hᵢ₁'
          simp [hᵢ₁'] at hᵢ₁₁
          simp [Residual.evaluate, hᵢ₁₁, Value.asBool]
          exact partialEvaluate_is_sound h₇ h₁ h₂ h₃
  case or => sorry
  case unaryApp => sorry
  case binaryApp => sorry
  case getAttr => sorry
  case hasAttr => sorry
  case set => sorry
  case record => sorry
  case call => sorry

end Cedar.Thm
