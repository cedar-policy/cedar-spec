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

theorem partial_evaluate_is_sound_ite
{x₁ x₂ x₃ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(hwt : Residual.WellTyped env x₁)
(hₜ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₂ : Except.toOption (x₂.evaluate req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es))
(hᵢ₃ : Except.toOption (x₃.evaluate req es) = Except.toOption ((TPE.evaluate x₃ preq pes).evaluate req es)) :
  Except.toOption ((x₁.ite x₂ x₃ x₂.typeOf).evaluate req es) =
  Except.toOption ((TPE.evaluate (x₁.ite x₂ x₃ x₂.typeOf) preq pes).evaluate req es) := by
  simp [Residual.evaluate, TPE.evaluate, TPE.ite]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    have h₆ := to_option_right_ok' hᵢ₁
    split
    case isTrue heq =>
      simp only [h₆, heq, Value.asBool, Except.bind_ok, ↓reduceIte]
      exact hᵢ₂
    case isFalse heq =>
      simp only [h₆, heq, Value.asBool, Except.bind_ok, Bool.false_eq_true, ↓reduceIte]
      exact hᵢ₃
  case _ heq =>
    simp only [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, h₆⟩
    simp only [Except.toOption, h₆, Except.bind_err, Residual.evaluate]
  case _ =>
    simp [Residual.evaluate]
    generalize h₅ : x₁.evaluate req es = res₁
    cases res₁
    case ok =>
      have h₆ := residual_well_typed_is_sound h₂ hwt h₅
      simp only [hₜ] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      subst h₆
      simp only [Value.asBool, Except.bind_ok]
      replace hᵢ₆ := to_option_left_ok hᵢ₁ h₅
      simp only [hᵢ₆, Except.bind_ok]
      split
      case _ => exact hᵢ₂
      case _ => exact hᵢ₃
    case error =>
      simp only [Except.toOption, Except.bind_err]
      simp only [h₅] at hᵢ₁
      rcases to_option_left_err hᵢ₁ with ⟨_, hᵢ₁⟩
      simp only [hᵢ₁, Except.bind_err]

end Cedar.Thm
