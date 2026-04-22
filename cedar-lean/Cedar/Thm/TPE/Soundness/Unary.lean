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
(h_ref : RequestAndEntitiesRefine req es preq pes)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es)) :
  Except.toOption ((Residual.unaryApp op₁ x₁ ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.unaryApp op₁ x₁ ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.apply₁]
  split
  case _ heq =>
    simp only [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  case _ =>
    split
    case _ v heq  =>
      rw [asValue_evaluate_val heq] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp only [Residual.evaluate, hᵢ₁, Except.bind_ok, okOrResidualError, ExceptT.stM_eq]
      split <;> (rename_i h; simp [h])
    case _ =>
      split
      · -- .is ety, .var .resource _
        rename_i ety _ heq_r
        simp only [heq_r, Residual.evaluate, toOption_ok, toOption_eq_some_iff, evaluate_val] at hᵢ₁ ⊢
        simp [hᵢ₁, Spec.apply₁, h_ref.1.2, BEq.comm]
      · -- .is ety, .var .principal _
        rename_i ety _ heq_p
        simp only [heq_p, Residual.evaluate, toOption_ok, toOption_eq_some_iff, evaluate_val] at hᵢ₁ ⊢
        simp [hᵢ₁, Spec.apply₁,  h_ref.1.2, BEq.comm]
      · simp [Residual.evaluate]
        generalize h₅ : x₁.evaluate req es = res₁
        cases res₁ <;> simp only [h₅, toOption_error, toOption_ok] at hᵢ₁
        case error =>
          symm at hᵢ₁
          simp only [toOption_eq_none_iff] at hᵢ₁
          rcases hᵢ₁ with ⟨_, hᵢ₁⟩
          simp [hᵢ₁, Except.toOption]
        case ok =>
          symm at hᵢ₁
          simp only [toOption_eq_some_iff] at hᵢ₁
          simp [←hᵢ₁]

end Cedar.Thm
