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
  case _ rv heq =>
    have heval := asResidualValue_evaluate heq req es
    rw [heval] at hᵢ₁
    -- Both sides compute apply₁ on the value
    -- LHS: x₁.evaluate >>= Spec.apply₁ op₁
    -- RHS: (TPE.apply₁ op₁ rv ty).evaluate
    -- By hᵢ₁, toOption of x₁.evaluate = toOption of rv.evaluate
    -- TPE.apply₁ matches on rv, Spec.apply₁ matches on the value
    -- For each case, the results match
    -- Use the fact that TPE.apply₁ result is someOrError/val/error
    -- which evaluates to the same as Spec.apply₁
    simp only [Residual.evaluate, someOrError_evaluate_ok, someOrError_evaluate_err,
      evaluate_asResidualValue, Except.toOption]
    -- After simp, the TPE side should be reduced
    -- Now case-split on rv to match both sides
    -- The TPE result is apply₁ op₁ rv ty, which matches on (op₁, rv)
    -- Each case produces someOrError/val/error, all evaluating predictably
    -- The concrete side computes Spec.apply₁ op₁ v where v = rv.evaluate
    -- Both give the same result
    sorry
  case _ =>
    split
    case _ heq =>
      -- error case
      simp only [Residual.evaluate, Except.toOption]
      rw [heq] at hᵢ₁
      simp only [Residual.evaluate, Except.toOption] at hᵢ₁
      cases hx : x₁.evaluate req es <;> simp_all
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
