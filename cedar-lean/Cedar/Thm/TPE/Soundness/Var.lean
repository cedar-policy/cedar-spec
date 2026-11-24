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
import Cedar.Thm.TPE.Attrs
import Cedar.Thm.TPE.State

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

theorem partial_evaluate_is_sound_val
{v : Value}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{ty : CedarType} :
  Except.toOption ((Residual.val v ty).evaluate req es) =
  Except.toOption ((TPE.evaluate env (Residual.val v ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, Residual.evaluate]


theorem partial_evaluate_is_sound_var
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{v : Var}
{ty : CedarType}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(hwt : Residual.WellTyped env (Residual.var v ty))
(h₄ : RequestAndEntitiesRefine req es preq pes) :
  Except.toOption ((Residual.var v ty).evaluate req es) =
  Except.toOption ((TPE.evaluate env (Residual.var v ty) preq pes).evaluate req es)
:= by
  simp only [TPE.evaluate, varₚ]
  cases v
  case principal =>
    simp only [varₚ.varₒ, someOrSelf]
    split
    case h_1 heq =>
      simp [Option.bind_eq_some_iff] at heq
      rcases heq with ⟨_, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      simp [RequestAndEntitiesRefine, RequestRefines] at h₄
      rcases h₄ with ⟨⟨h₄, _⟩, _⟩
      simp only [heq₁, PartialIsValid.some_inv] at h₄
      subst h₄
      rfl
    case h_2 =>
      simp only [Residual.evaluate]
  case resource =>
    simp only [varₚ.varₒ, someOrSelf]
    split
    case h_1 heq =>
      simp [Option.bind_eq_some_iff] at heq
      rcases heq with ⟨_, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      simp [RequestAndEntitiesRefine, RequestRefines] at h₄
      rcases h₄ with ⟨⟨_, ⟨_, ⟨h₄, _⟩⟩⟩, _⟩
      simp only [heq₁, PartialIsValid.some_inv] at h₄
      subst h₄
      rfl
    case h_2 =>
      simp only [Residual.evaluate]
  case action =>
    simp only [varₚ.varₒ, someOrSelf]
    simp [Residual.evaluate]
    simp [RequestAndEntitiesRefine, RequestRefines] at h₄
    rcases h₄ with ⟨⟨_, ⟨h₄, _⟩⟩, _⟩
    rw [h₄]
  case context =>
    cases hwt with | var hv =>
    cases hv with | context =>
    simp only [CedarType.liftBoolTypes]
    have hinst : InstanceOfType env (.record req.context)
        (.record (RecordType.liftBoolTypes env.reqty.context)) := by
      have h_ctx := h₂.2.1.2.2.2
      have := type_lifting_preserves_instance_of_type h_ctx
      simpa only [CedarType.liftBoolTypes] using this
    have hvar : Residual.WellTyped env
        (Residual.var Var.context (.record (RecordType.liftBoolTypes env.reqty.context))) := by
      have h := @Residual.WellTyped.var env Var.context
        ((CedarType.record env.reqty.context).liftBoolTypes) Var.WellTyped.context
      simpa only [CedarType.liftBoolTypes] using h
    cases hctx : preq.context with
    | none => simp only [Residual.evaluate]
    | some r =>
      simp only [RequestAndEntitiesRefine, RequestRefines, hctx, PartialIsValid.some_inv] at h₄
      obtain ⟨⟨_, _, _, hcr, _⟩, _⟩ := h₄
      refine (stateToResidual_sound h₂ ?_ hvar rfl).symm
      simpa only [Residual.evaluate, Except.toOption] using hcr.toAttrState

end Cedar.Thm
