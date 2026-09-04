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

/-- `getAttr` on an entity errors exactly when the (concrete) attribute is
missing, whether because the entity is absent or the attribute is. -/
theorem get_attr_entity_none {es : Entities} {uid : EntityUID} {attr : Attr}
  (h : (es.attrsOrEmpty uid).find? attr = .none) :
  Spec.getAttr (.prim (.entityUID uid)) attr es = .error .entityDoesNotExist ∨
  Spec.getAttr (.prim (.entityUID uid)) attr es = .error .attrDoesNotExist
:= by
  simp only [Spec.getAttr, Spec.attrsOf, Entities.attrs, Entities.attrsOrEmpty] at *
  cases hf : es.find? uid with
  | none => left; simp [hf, Data.Map.findOrErr, bind, Except.bind]
  | some d =>
    right
    simp only [hf] at h
    simp [hf, Data.Map.findOrErr, h, bind, Except.bind]

theorem partial_evaluate_is_sound_get_attr
{x₁ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{attr : Attr}
{ty : CedarType}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(hwt : Residual.WellTyped env (Residual.getAttr x₁ attr ty))
(hwt' : Residual.WellTyped env (TPE.evaluate env x₁ preq pes))
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate env x₁ preq pes).evaluate req es)) :
  Except.toOption ((x₁.getAttr attr ty).evaluate req es) =
  Except.toOption ((TPE.evaluate env (x₁.getAttr attr ty) preq pes).evaluate req es)
:= by
  simp only [TPE.evaluate, TPE.getAttr]
  split
  case h_1 heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  case h_2 =>
    have hself := get_attr_residual_well_typed hwt' hwt
    have hcons : AttrStateConsistent (attrStateAt env preq pes (TPE.evaluate env x₁ preq pes) attr)
        ((((TPE.evaluate env x₁ preq pes).getAttr attr ty).evaluate req es).toOption) := by
      simpa only [Residual.evaluate, bind, Except.bind] using
        attrStateAt_sound (a := attr) h₂ h₄ hwt'
    rw [stateToResidual_sound (ty := ty) h₂ hcons hself rfl]
    simp only [Residual.evaluate]
    exact to_option_eq_do₁ (Spec.getAttr · attr es) hᵢ₁

end Cedar.Thm
