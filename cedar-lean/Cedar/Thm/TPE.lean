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
    cases h₀
    rename_i h₄ h₅ h₆ _
    have hᵢ₁ := partialEvaluate_is_sound h₄ h₁ h₂ h₃
    rcases h₆ with ⟨h₆₁, h₆₂⟩
    simp [TypedExpr.toExpr, Spec.evaluate]
    generalize hᵢ₁₁ : Spec.evaluate x₁.toExpr req₁ es₁ = res₁
    cases res₁
    case _ =>
      rcases to_option_left_err hᵢ₁ hᵢ₁₁ with ⟨_, hᵢ₁₂⟩
      simp [Result.as, TPE.evaluate]
      -- essentially (TPE.evaluate x₁ req₂ es₂).evaluate req₁ es₁ = .error _ → (TPE.and (TPE.evaluate x₁ req₂ es₂) (TPE.evaluate x₂ req₂ es₂) ty).evaluate req₁ es₁) = .error _
      sorry
    case _ v₁ =>
      rcases well_typed_bool h₁ h₄ h₆₁ hᵢ₁₁ with ⟨b₁, hᵢ₁₁'⟩
      have hᵢ₁₂ := to_option_left_ok hᵢ₁ hᵢ₁₁
      simp [hᵢ₁₁', Result.as, Coe.coe, Value.asBool, TPE.evaluate, TPE.and]
      split <;> split
      · rename_i hb _ _ _ _ _ heq _
        simp [heq, Residual.evaluate, hᵢ₁₁', hb] at hᵢ₁₂
      · rename_i hb _ _ _ _ _ _ _
        simp [Residual.evaluate, hb]
      · rename_i heq _
        simp [heq, Residual.evaluate] at hᵢ₁₂
      · simp [hᵢ₁₂, hᵢ₁₁']
      · rename_i hb _ _ _ _ _ _ _ _ _
        simp [Residual.evaluate, hᵢ₁₂, hᵢ₁₁', hb, Result.as, Coe.coe, Value.asBool]
      · rename_i hb _ v₂ heq
        simp at hb
        rcases well_typed_bool h₁ h₅ h₆₂ heq with ⟨b₂, hᵢ₂⟩
        split
        · simp
          sorry
        · rename_i heq₁
          simp [hᵢ₂] at heq₁
      · rename_i heq
        sorry
  case lit => sorry
  case var => sorry
  case ite cond thenExpr elseExpr ty =>
    cases h₀
    rename_i h₄ h₅ h₆ h₇ _
    simp [TypedExpr.toExpr, Spec.evaluate]
    generalize hᵢ₁ : Spec.evaluate cond.toExpr req₁ es₁ = res₁
    cases res₁
    case _ =>
      sorry
    case _ v₁ =>
      rcases well_typed_bool h₁ h₄ h₅ hᵢ₁ with ⟨b₁, hᵢ₁'⟩
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
  case hasAttr x₁ attr ty =>
    cases h₀
    rename_i h₄ h₅ h₆
    have hᵢ₁ := partialEvaluate_is_sound h₄ h₁ h₂ h₃
    generalize hᵢ₁₁ : Spec.evaluate x₁.toExpr req₁ es₁ = res₁
    cases res₁
    case _ =>
      rcases to_option_left_err hᵢ₁ hᵢ₁₁ with ⟨_, hᵢ₁₂⟩
      simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₁₁, TPE.evaluate, TPE.hasAttr]
      split
      · simp [Residual.evaluate, Except.toOption]
      · split
        · rename_i heq
          simp [TPE.attrsOf] at heq
          split at heq
          · rename_i heq₁
            simp [heq₁, Residual.evaluate] at hᵢ₁₂
          · rename_i heq₁
            simp [heq₁, Residual.evaluate] at hᵢ₁₂
          · cases heq
        · rename_i heq
          simp [TPE.attrsOf] at heq
          split at heq
          · cases heq
          · rename_i heq₁
            simp [heq₁, Residual.evaluate] at hᵢ₁₂
          · simp [Residual.evaluate, hᵢ₁₂, Except.toOption]
    case _ v =>
      simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₁₁, Spec.hasAttr, Spec.attrsOf]
      cases h₅
      case _ hₜ =>
        sorry
      case _ hₜ =>
        have ⟨m, hᵢ₁₂⟩ := well_typed_record h₁ h₄ hₜ hᵢ₁₁
        simp [hᵢ₁₂]
        have hᵢ₁₂' := to_option_left_ok hᵢ₁ hᵢ₁₁
        simp [TPE.evaluate, TPE.hasAttr]
        split
        · rename_i heq
          simp [heq, Residual.evaluate] at hᵢ₁₂'
        · split <;> rename_i heq₁ <;> simp [TPE.attrsOf] at heq₁
          · split at heq₁
            · rename_i heq₂
              simp [heq₂, Residual.evaluate] at hᵢ₁₂'
              simp at heq₁
              simp [hᵢ₁₂] at hᵢ₁₂'
              simp [←heq₁, Residual.evaluate, hᵢ₁₂']
            · rename_i heq₂
              simp [heq₂, Residual.evaluate, hᵢ₁₂] at hᵢ₁₂'
            · cases heq₁
          · split at heq₁
            · cases heq₁
            · rename_i heq₂
              simp [heq₂, Residual.evaluate] at hᵢ₁₂'
              simp [hᵢ₁₂] at hᵢ₁₂'
            · simp [Residual.evaluate, hᵢ₁₂', hᵢ₁₂, Spec.hasAttr, Spec.attrsOf]
  case set => sorry
  case record => sorry
  case call => sorry

end Cedar.Thm
