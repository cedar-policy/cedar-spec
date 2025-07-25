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

import Cedar.Thm.Validation.WellTyped.ResidualDefinition
import Cedar.Thm.Validation.WellTyped.Soundness
import Cedar.TPE.Residual
import Cedar.Thm.Validation.WellTyped.Typechecking
import Cedar.Data.Map

/-!
This file contains residual-specific lemmas of the theorem `residual_well_typed_is_sound`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Validation
open Cedar.Spec
open Cedar.Spec.Ext
open Cedar.TPE
open Cedar.Data

theorem residual_well_typed_is_sound_val
{v : Value}
{v' : Value}
{env : TypeEnv}
{request : Request}
{entities : Entities}
{ty : CedarType}
(h₁ : InstanceOfType env v' ty)
(h₂ : (Residual.val v' ty).evaluate request entities = Except.ok v) : (InstanceOfType env v (Residual.val v' ty).typeOf)
:= by
  simp only [Residual.typeOf]
  simp [Residual.evaluate] at h₂
  rewrite [h₂] at h₁
  exact h₁

theorem residual_well_typed_is_sound_var
{v : Value}
{var : Var}
{env : TypeEnv}
{request : Request}
{entities : Entities}
{ty : CedarType}
(h₁ : InstanceOfWellFormedEnvironment request entities env)
(h₂ : Var.WellTyped env var ty)
(h₃ : (Residual.var var ty).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.var var ty).typeOf
:= by
  simp only [Residual.typeOf]
  -- The residual var evaluation directly returns request components
  cases h₂ <;>
  simp only [Residual.evaluate, Except.ok.injEq] at h₃ <;>
  rw [←h₃] <;>
  simp only [InstanceOfWellFormedEnvironment, InstanceOfRequestType] at h₁
  case principal =>
    rcases h₁ with ⟨_, ⟨h₁, _, _, _⟩, _⟩
    exact InstanceOfType.instance_of_entity request.principal env.reqty.principal h₁
  case resource =>
    rcases h₁ with ⟨_, ⟨_, _, h₁, _⟩, _⟩
    exact InstanceOfType.instance_of_entity request.resource env.reqty.resource h₁
  case action =>
    rcases h₁ with ⟨hwf, ⟨_, h₁, _, _⟩, _⟩
    rw [h₁]
    have : InstanceOfEntityType env.reqty.action env.reqty.action.ty env := by
      have ⟨_, _, ⟨_, hwf_act, _⟩⟩ := hwf
      simp [
        InstanceOfEntityType, EntityUID.WellFormed,
        ActionSchema.contains, hwf_act,
      ]
    exact InstanceOfType.instance_of_entity env.reqty.action env.reqty.action.ty this
  case context =>
    rcases h₁ with ⟨_, ⟨_, _, _, h₁⟩, _⟩
    exact type_lifting_preserves_instance_of_type h₁

theorem residual_well_typed_is_sound_and
{v : Value}
{x₁ x₂ : Residual}
{env : TypeEnv}
{request : Request}
{entities : Entities}
(h₁ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(h₂ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₁ : ∀ {v : Value}, x₁.evaluate request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(hᵢ₂ : ∀ {v : Value}, x₂.evaluate request entities = Except.ok v → InstanceOfType env v x₂.typeOf)
(h₃ : (Residual.and x₁ x₂ (CedarType.bool BoolType.anyBool)).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.and x₁ x₂ (CedarType.bool BoolType.anyBool)).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate] at h₃
  -- The residual and evaluation: first evaluate x₁, if false return false, else evaluate x₂
  generalize hᵢ₁' : x₁.evaluate request entities = res₁
  cases res₁
  case error => simp only [Result.as, hᵢ₁', Except.bind_err, reduceCtorEq] at h₃
  case ok =>
    rename_i v₁
    specialize hᵢ₁ hᵢ₁'
    simp only [h₁] at hᵢ₁
    replace ⟨b, hᵢ₁⟩ := instance_of_anyBool_is_bool hᵢ₁
    simp only [hᵢ₁] at hᵢ₁'
    simp only [Result.as, hᵢ₁', Coe.coe, Value.asBool, Except.bind_ok] at h₃
    cases b <;> simp at h₃
    case false =>
      rw [←h₃]
      simp only [bool_is_instance_of_anyBool]
    case true =>
      generalize hᵢ₂' : x₂.evaluate request entities = res₂
      cases res₂
      case error =>
        simp only [hᵢ₂', Except.map_error, reduceCtorEq] at h₃
      case ok =>
        simp only [hᵢ₂'] at h₃
        specialize hᵢ₂ hᵢ₂'
        simp only [h₂] at hᵢ₂
        replace ⟨_, hᵢ₂⟩ := instance_of_anyBool_is_bool hᵢ₂
        simp only [hᵢ₂, Except.map_ok, Except.ok.injEq] at h₃
        simp only [←h₃, bool_is_instance_of_anyBool]

theorem residual_well_typed_is_sound_unary_app
{v : Value}
{op₁ : UnaryOp}
{x₁ : Residual}
{env : TypeEnv}
{request : Request}
{entities : Entities}
{ty : CedarType}
(h₁ : UnaryResidualWellTyped op₁ x₁ ty)
(_ : ∀ {v : Value}, x₁.evaluate request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(h₂ : (Residual.unaryApp op₁ x₁ ty).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.unaryApp op₁ x₁ ty).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate] at h₂
  generalize hᵢ₁' : x₁.evaluate request entities = res₁
  cases res₁
  case error => simp only [Result.as, hᵢ₁', Except.bind_err, reduceCtorEq] at h₂
  case ok v₁ =>
    simp only [hᵢ₁', Cedar.Spec.apply₁, Except.bind_ok] at h₂
    split at h₂ <;> cases h₁
    · -- not case
      simp only [Except.ok.injEq] at h₂
      simp only [←h₂, bool_is_instance_of_anyBool]
    · -- neg case
      simp only [intOrErr] at h₂
      split at h₂
      · simp only [Except.ok.injEq] at h₂
        rw [←h₂]
        exact InstanceOfType.instance_of_int
      · cases h₂
    · -- isEmpty case
      simp only [Except.ok.injEq] at h₂
      simp only [←h₂, bool_is_instance_of_anyBool]
    · -- like case
      simp only [Except.ok.injEq] at h₂
      simp only [←h₂, bool_is_instance_of_anyBool]
    · -- is case
      simp only [Except.ok.injEq] at h₂
      simp only [←h₂, bool_is_instance_of_anyBool]
    · -- error case (when apply₁ fails)
      cases h₂
    · -- error case (when apply₁ fails)
      cases h₂
    · -- error case (when apply₁ fails)
      cases h₂
    · -- error case (when apply₁ fails)
      cases h₂
    · -- error case (when apply₁ fails)
      cases h₂

end Cedar.Thm
