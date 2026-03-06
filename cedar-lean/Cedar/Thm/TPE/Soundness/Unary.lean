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

theorem partial_evaluate_is_sound_unary_app
{x₁ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{op₁ : UnaryOp}
{ty : CedarType}
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es)) :
  Except.toOption ((Residual.unaryApp op₁ x₁ ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.unaryApp op₁ x₁ ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.apply₁]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  case _ =>
    split
    case _ heq =>
      rw [asValue_evaluate_val heq] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [someOrError, Residual.evaluate, hᵢ₁]
      split
      case _ heq₂ =>
        simp [to_option_some] at heq₂
        simp [heq₂, Residual.evaluate]
      case _ heq₂ =>
        rcases to_option_none.mp heq₂ with ⟨_, heq₂⟩
        simp [heq₂, Residual.evaluate, Except.toOption]
    case _ =>
      simp [Residual.evaluate]
      generalize h₅ : x₁.evaluate req es = res₁
      cases res₁ <;> simp [h₅] at hᵢ₁
      case error =>
        rcases to_option_left_err hᵢ₁ with ⟨_, hᵢ₁⟩
        simp [hᵢ₁, Except.toOption]
      case ok =>
        replace hᵢ₃ := to_option_left_ok' hᵢ₁
        simp [hᵢ₃]

end Cedar.Thm
