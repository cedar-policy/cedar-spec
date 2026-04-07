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
{v : Value}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{ty : CedarType} :
  Except.toOption ((Residual.val v ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.val v ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, Residual.evaluate]


theorem partial_evaluate_is_sound_var
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{v : Var}
{ty : CedarType}
(h₄ : RequestAndEntitiesRefine req es preq pes) :
  Except.toOption ((Residual.var v ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.var v ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, varₚ]
  split <;>
  simp [varₚ.varₒ, someOrSelf]
  case _ =>
    split
    case _ heq =>
      simp [Option.bind_eq_some_iff] at heq
      rcases heq with ⟨_, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      simp [RequestAndEntitiesRefine, RequestRefines] at h₄
      rcases h₄ with ⟨⟨h₄, _⟩, _⟩
      rw [heq₁] at h₄
      cases h₄
      rename_i heq₂
      subst heq₂
      rfl
    case _ heq =>
      simp only [Residual.evaluate]
  case _ =>
    split
    case _ heq =>
      simp [Option.bind_eq_some_iff] at heq
      rcases heq with ⟨_, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      simp [RequestAndEntitiesRefine, RequestRefines] at h₄
      rcases h₄ with ⟨⟨_, ⟨_, ⟨h₄, _⟩⟩⟩, _⟩
      rw [heq₁] at h₄
      cases h₄
      rename_i heq₂
      subst heq₂
      rfl
    case _ heq =>
      simp only [Residual.evaluate]
  case _ =>
    simp [Residual.evaluate]
    simp [RequestAndEntitiesRefine, RequestRefines] at h₄
    rcases h₄ with ⟨⟨_, ⟨h₄, _⟩⟩, _⟩
    rw [h₄]
  case _ =>
    split
    case _ heq =>
      simp at heq
      rcases heq with ⟨_, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      simp [RequestAndEntitiesRefine, RequestRefines] at h₄
      rcases h₄ with ⟨⟨_, ⟨_, ⟨_, ⟨h₄, _, _⟩⟩⟩⟩, _⟩
      rw [heq₁] at h₄
      cases h₄
      rename_i heq₂
      subst heq₂
      rfl
    case _ =>
      simp only [Residual.evaluate]

end Cedar.Thm
