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

theorem partial_evaluate_is_sound_get_attr
{x₁ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
{attr : Attr}
{ty : CedarType}
(h₄ : RequestAndEntitiesRefine env req es preq pes)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es)) :
  Except.toOption ((x₁.getAttr attr ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (x₁.getAttr attr ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.getAttr]
  sorry
  /-
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  split
  case _ heq =>
    simp [TPE.attrsOf] at heq
    split at heq
    case _ heq₁ =>
      simp at heq
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [Residual.evaluate, hᵢ₁, someOrError, Spec.getAttr, Spec.attrsOf]
      subst heq
      split <;>
      (
        rename_i heq₂
        simp [Data.Map.findOrErr, heq₂, Residual.evaluate, Except.toOption]
      )
    case _ uid _ heq₁ =>
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [Residual.evaluate, hᵢ₁, Spec.getAttr, Spec.attrsOf]
      simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some_iff] at heq
      rcases heq with ⟨data, heq₂, heq₃⟩
      simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄
      rcases h₄ with ⟨_, h₄⟩
      specialize h₄ uid data heq₂
      rcases h₄ with ⟨_, h₄₁, h₄₂, _⟩
      rw [heq₃] at h₄₂
      rcases h₄₂
      rename_i data' _ h₄
      subst h₄
      simp [Entities.attrs, Data.Map.findOrErr, h₄₁]
      generalize h₄ : data'.attrs.find? attr = res
      cases res <;> simp [someOrError, Residual.evaluate, Except.toOption]
    case _ => cases heq
  case _ =>
    simp [Residual.evaluate]
    exact to_option_eq_do₁ (Spec.getAttr · attr es) hᵢ₁
  -/

end Cedar.Thm
