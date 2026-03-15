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

theorem partial_evaluate_is_sound_and
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
  Except.toOption ((x₁.and x₂ (CedarType.bool BoolType.anyBool)).evaluate req es) =
  Except.toOption ((TPE.evaluate (x₁.and x₂ (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.and]
  split
  case _ ty heq =>
    simp [heq] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [Residual.evaluate, h₅, Result.as, Coe.coe, Value.asBool]
    split
    case _ heq₁ =>
      have h₆ := residual_well_typed_is_sound h₂ hᵢ₂ heq₁
      rw [hᵢ₄] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      replace hᵢ₆ := to_option_left_ok hᵢ₆ heq₁
      simp [h₆, hᵢ₆, Except.toOption]
    case _ heq₁ =>
      rw [heq₁] at hᵢ₆
      rcases to_option_left_err hᵢ₆ with ⟨_, hᵢ₆⟩
      simp [hᵢ₆, Except.toOption]
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [Residual.evaluate, h₅, Result.as, Coe.coe, Value.asBool, Residual.evaluate]
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    rcases to_option_right_err hᵢ₅ with ⟨_, hᵢ₅⟩
    simp [Residual.evaluate, hᵢ₅, Result.as, Residual.evaluate, Except.toOption]
  case _ heq _ _ _ =>
    simp [heq, Residual.evaluate] at hᵢ₆
    have h₅ := to_option_right_ok' hᵢ₆
    simp [Residual.evaluate]
    generalize h₆ : x₁.evaluate req es = res₁
    cases res₁
    case ok =>
      have h₇ := residual_well_typed_is_sound h₂ hᵢ₁ h₆
      rw [hᵢ₃] at h₇
      rcases instance_of_anyBool_is_bool h₇ with ⟨_, h₇⟩
      simp [h₇, Result.as, Coe.coe, Value.asBool]
      split
      case _ heq₁ =>
        subst heq₁
        rw [h₇] at h₆
        rw [←h₆]
        exact hᵢ₅
      case _ heq₁ =>
        simp [h₅]
        simp at heq₁
        subst heq₁
        subst h₇
        rw [←h₆]
        exact hᵢ₅
    case error =>
      simp [h₆] at hᵢ₅
      rcases to_option_left_err hᵢ₅ with ⟨_, hᵢ₅⟩
      simp only [Except.toOption, Result.as, Except.bind_err, hᵢ₅]
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
      · -- errorFree = true case
        have h₇ : Residual.WellTyped env (TPE.evaluate x₁ preq pes) :=
          partial_eval_preserves_well_typed h₂ h₃ hᵢ₁
        rw [Residual.error_free_spec] at h₆
        have h₈ := error_free_evaluate_ok h₂ h₇ h₆ htc₁
        rw [Except.isOk_iff_exists] at h₈
        obtain ⟨v, hv⟩ := h₈
        rw [h₅] at hᵢ₅
        simp only [Except.toOption] at hᵢ₅
        rw [hv] at hᵢ₅
        simp [Except.toOption] at hᵢ₅
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
      have hb : (if b = false then (Except.ok (Value.prim (Prim.bool b)) : Except Spec.Error _) else Except.ok (Value.prim (Prim.bool false))) = Except.ok (.prim (.bool false)) := by
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
