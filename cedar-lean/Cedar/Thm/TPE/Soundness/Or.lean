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
import Cedar.Thm.TPE.ErrorFree
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped
import Cedar.Thm.Data.Control

import Cedar.Thm.TPE.Soundness.Basic

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

theorem partial_evaluate_is_sound_or
{x₁ x₂ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(h₃ : RequestAndEntitiesRefine env req es preq pes)
(hᵢ₁ : Residual.WellTyped env x₁)
(hᵢ₂ : Residual.WellTyped env x₂)
(hᵢ₃ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₄ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₅ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₆ : Except.toOption (x₂.evaluate req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es))
(htc₁ : rTargetCorrect (TPE.evaluate x₁ preq pes) req es)
(htc₂ : rTargetCorrect (TPE.evaluate x₂ preq pes) req es) :
  Except.toOption ((x₁.or x₂ (CedarType.bool BoolType.anyBool)).evaluate req es) =
  Except.toOption ((TPE.evaluate (x₁.or x₂ (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.or]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [Residual.evaluate, h₅, Result.as, Coe.coe, Value.asBool, Residual.evaluate]
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [←hᵢ₆, Residual.evaluate, h₅, Result.as, Coe.coe, Value.asBool]
    cases h₆ : x₂.evaluate req es
    case error => simp [Except.toOption]
    case ok =>
      have h₇ := residual_well_typed_is_sound h₂ hᵢ₂ h₆
      rw [hᵢ₄] at h₇
      rcases instance_of_anyBool_is_bool h₇ with ⟨_, h₇⟩
      subst h₇
      simp [Except.toOption]
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    rcases to_option_right_err hᵢ₅ with ⟨_, hᵢ₅⟩
    simp [Residual.evaluate, hᵢ₅, Result.as, Residual.evaluate, Except.toOption]
  case _ heq _ _ _ =>
    simp [heq, Residual.evaluate] at hᵢ₆
    have hᵢ₇ := to_option_right_ok' hᵢ₆
    generalize h₅ : x₁.evaluate req es = res₁
    cases res₁
    case error =>
      simp [Residual.evaluate, h₅, Result.as]
      rw [←h₅]
      exact hᵢ₅
    case ok =>
      have h₆ := residual_well_typed_is_sound h₂ hᵢ₁ h₅
      rw [hᵢ₃] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      simp [Residual.evaluate, h₅, h₆, Result.as, Coe.coe, Value.asBool, hᵢ₇]
      split
      case _ heq₁ =>
        subst heq₁
        rw [h₆] at h₅
        rw [←h₅]
        exact hᵢ₅
      case _ heq₁ =>
        simp only [Bool.not_eq_true] at heq₁
        subst heq₁
        rw [h₆] at h₅
        rw [←h₅]
        exact hᵢ₅
  case _ =>
    simp [Residual.evaluate]
    cases h₅ : x₁.evaluate req es
    · simp [Result.as, Except.toOption]
      cases h₆ : (TPE.evaluate x₁ preq pes).errorFree <;> simp
      · split <;> simp
        rename_i h₇
        simp [Residual.evaluate] at h₇
        rw [h₅] at hᵢ₅
        simp [Except.toOption] at hᵢ₅
        split at hᵢ₅ <;> try contradiction
        clear hᵢ₅ ; rename_i hᵢ₅
        simp [hᵢ₅, Result.as] at h₇
      · sorry -- errorFree case: needs adaptation for new simp lemmas
    · simp [Result.as, Except.toOption, Coe.coe, Value.asBool]
      simp [h₅, Except.toOption] at hᵢ₅
      split at hᵢ₅ <;> try contradiction
      simp at hᵢ₅
      subst hᵢ₅
      rename_i hᵢ₅
      rename_i v _
      have ⟨_, hv⟩ : ∃ b, v = .prim (.bool b) := by
        have h₇ := residual_well_typed_is_sound h₂ hᵢ₁ h₅
        rw [hᵢ₃] at h₇
        exact instance_of_anyBool_is_bool h₇
      subst hv
      simp only
      rename_i h₁ _ _ _ _ _
      simp [h₁, Except.toOption, Residual.evaluate] at hᵢ₆
      split at hᵢ₆ <;> simp at hᵢ₆
      subst hᵢ₆
      rename_i hᵢ₆
      simp [hᵢ₆]
      rename_i b _
      have hb : (if b = true then (Except.ok (Value.prim (Prim.bool b)) : Except Spec.Error _) else Except.ok (Value.prim (Prim.bool true))) = Except.ok (.prim (.bool true)) := by
        split
        · rename_i hb
          simpa using hb
        · simp
      simp [hb]
      rename_i ty _ _ _ _ _
      cases he : (TPE.evaluate x₁ preq pes).errorFree<;> simp [Residual.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool]
      cases b <;> simp
  case _ =>
    simp [Residual.evaluate]
    generalize h₅ : x₁.evaluate req es = res₁
    cases res₁
    case ok =>
      have h₆ := residual_well_typed_is_sound h₂ hᵢ₁ h₅
      rw [hᵢ₃] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      subst h₆
      replace h₅ := to_option_left_ok hᵢ₅ h₅
      simp [Result.as, Coe.coe, h₅, Value.asBool]
      generalize h₇ : x₂.evaluate req es = res₂
      cases res₂
      case _ =>
        rw [h₇] at hᵢ₆
        rcases to_option_left_err hᵢ₆ with ⟨_, hᵢ₆⟩
        simp [hᵢ₆]
        split <;> simp [Except.toOption]
      case _ =>
        replace h₇ := to_option_left_ok hᵢ₆ h₇
        rw [h₇]
    case error =>
      rw [h₅] at hᵢ₅
      rcases to_option_left_err hᵢ₅ with ⟨_, hᵢ₅⟩
      simp [Result.as, hᵢ₅, Except.toOption]

end Cedar.Thm
