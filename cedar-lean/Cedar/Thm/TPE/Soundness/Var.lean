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

theorem partial_evaluate_is_sound_val
{rv : ResidualValue}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{ty : CedarType} :
  Except.toOption ((Residual.val rv ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.val rv ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, Residual.evaluate]


theorem partial_evaluate_is_sound_var
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
{v : Var}
{ty : CedarType}
(h₄ : RequestAndEntitiesRefine env req es preq pes) :
  Except.toOption ((Residual.var v ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.var v ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, varₚ]
  split
  case _ =>
    -- principal
    simp [varₚ.varₒ, someOrSelf]
    split
    case _ heq =>
      simp [Option.bind_eq_some_iff] at heq
      rcases heq with ⟨uid, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      -- h₄ gives PartialIsValid (· = req.principal) preq.principal.asEntityUID
      have ⟨⟨hp, _⟩, _⟩ := h₄
      rw [heq₁] at hp; cases hp with | some _ h => simp [h, evaluate_asResidualValue, Except.toOption]
    case _ heq =>
      simp only [Residual.evaluate]
  case _ =>
    -- resource
    simp [varₚ.varₒ, someOrSelf]
    split
    case _ heq =>
      simp [Option.bind_eq_some_iff] at heq
      rcases heq with ⟨uid, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      have ⟨⟨_, _, hr, _⟩, _⟩ := h₄
      rw [heq₁] at hr; cases hr with | some _ h => simp [h, evaluate_asResidualValue, Except.toOption]
    case _ heq =>
      simp only [Residual.evaluate]
  case _ =>
    -- action
    simp [varₚ.varₒ, someOrSelf]
    simp [Residual.evaluate]
    have ⟨⟨_, ha, _⟩, _⟩ := h₄
    simp [ha, evaluate_asResidualValue, Except.toOption]
  case _ =>
    -- context
    simp only [varₚ, Option.bind, Option.getD]
    have ⟨⟨_, _, _, hcv⟩, _⟩ := h₄
    cases hc : preq.context with
    | none => simp [Residual.evaluate]
    | some attrs =>
      simp only [hc, PartialValue.asResidual, Residual.evaluate, Except.toOption]
      rw [hc] at hcv; cases hcv with | some _ href =>
      have htgt : (Residual.var Var.context ty).evaluate req es = .ok (.record req.context) := by
        unfold Residual.evaluate; rfl
      simp [Residual.evaluate, toResidualValue_evaluate htgt href, Except.toOption]

end Cedar.Thm
