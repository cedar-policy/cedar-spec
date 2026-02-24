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

import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.TPE.Residual
import Cedar.Thm.WellTyped.Expr.Typechecking
import Cedar.Data.Map
import Cedar.Thm.Validation.Typechecker.Record
import Cedar.Thm.Data.List.Lemmas

/-!
This file contains residual-specific lemmas of the theorem `residual_well_typed_is_sound`
-/

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Spec
open Cedar.Spec.Ext
open Cedar.Data
open Cedar.Thm

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

theorem residual_well_typed_is_sound_or
{v : Value}
{x₁ x₂ : Residual}
{env : TypeEnv}
{request : Request}
{entities : Entities}
(h₁ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(h₂ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₁ : ∀ {v : Value}, x₁.evaluate request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(hᵢ₂ : ∀ {v : Value}, x₂.evaluate request entities = Except.ok v → InstanceOfType env v x₂.typeOf)
(h₃ : (Residual.or x₁ x₂ (CedarType.bool BoolType.anyBool)).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.or x₁ x₂ (CedarType.bool BoolType.anyBool)).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate] at h₃
  -- The residual or evaluation: first evaluate x₁, if true return true, else evaluate x₂
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
    case true =>
      rw [←h₃]
      simp only [bool_is_instance_of_anyBool]

theorem residual_well_typed_is_sound_ite
{v : Value}
{x₁ x₂ x₃ : Residual}
{env : TypeEnv}
{request : Request}
{entities : Entities}
(h₁ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(h₂ : x₂.typeOf = x₃.typeOf)
(hᵢ₁ : ∀ {v : Value}, x₁.evaluate request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(hᵢ₂ : ∀ {v : Value}, x₂.evaluate request entities = Except.ok v → InstanceOfType env v x₂.typeOf)
(hᵢ₃ : ∀ {v : Value}, x₃.evaluate request entities = Except.ok v → InstanceOfType env v x₃.typeOf)
(h₃ : (Residual.ite x₁ x₂ x₃ x₂.typeOf).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.ite x₁ x₂ x₃ x₂.typeOf).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate] at h₃
  -- The residual ite evaluation: first evaluate x₁, if true evaluate x₂, else evaluate x₃
  generalize hᵢ₁' : x₁.evaluate request entities = res₁
  cases res₁
  case error => simp only [hᵢ₁', Except.bind_err, reduceCtorEq] at h₃
  case ok =>
    rename_i v₁
    specialize hᵢ₁ hᵢ₁'
    simp only [h₁] at hᵢ₁
    replace ⟨b, hᵢ₁⟩ := instance_of_anyBool_is_bool hᵢ₁
    simp only [hᵢ₁] at hᵢ₁'
    simp only [hᵢ₁', Value.asBool, Except.bind_ok] at h₃
    cases b <;> simp at h₃
    case false =>
      have h₄ : InstanceOfType env v x₂.typeOf := by
        rw [h₂]
        exact hᵢ₃ h₃
      exact h₄
    case true =>
      exact hᵢ₂ h₃

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
  case error => simp only [hᵢ₁', Except.bind_err, reduceCtorEq] at h₂
  case ok v₁ =>
    simp only [hᵢ₁', apply₁, Except.bind_ok] at h₂
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

theorem residual_well_typed_is_sound_binary_app
{v : Value}
{op₂ : BinaryOp}
{x₁ x₂ : Residual}
{env : TypeEnv}
{request : Request}
{entities : Entities}
{ty : CedarType}
(h₁ : InstanceOfWellFormedEnvironment request entities env)
(h₄ : BinaryResidualWellTyped env op₂ x₁ x₂ ty)
(hᵢ₁ : ∀ {v : Value}, x₁.evaluate request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(hᵢ₂ : ∀ {v : Value}, x₂.evaluate request entities = Except.ok v → InstanceOfType env v x₂.typeOf)
(h₃ : (Residual.binaryApp op₂ x₁ x₂ ty).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.binaryApp op₂ x₁ x₂ ty).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate] at h₃
  generalize hᵢ₁' : x₁.evaluate request entities = res₁
  generalize hᵢ₂' : x₂.evaluate request entities = res₂
  cases res₁ <;> cases res₂ <;> simp [hᵢ₁', hᵢ₂'] at h₃
  -- case ok.ok
  rename_i v₁ v₂
  simp only [apply₂] at h₃
  split at h₃ <;>
  cases h₄ <;>
  try cases h₃ <;>
  try simp only [bool_is_instance_of_anyBool]
  · simp only [intOrErr] at h₃
    split at h₃
    · simp only [Except.ok.injEq] at h₃
      simp [←h₃]
      exact InstanceOfType.instance_of_int
    · cases h₃
  · simp only [intOrErr] at h₃
    split at h₃
    · simp only [Except.ok.injEq] at h₃
      simp [←h₃]
      exact InstanceOfType.instance_of_int
    · cases h₃
  · simp only [intOrErr] at h₃
    split at h₃
    · simp only [Except.ok.injEq] at h₃
      simp [←h₃]
      exact InstanceOfType.instance_of_int
    · cases h₃
  · specialize hᵢ₂ hᵢ₂'
    rename_i h₂
    simp only [h₂] at hᵢ₂
    cases hᵢ₂
  · simp only [Cedar.Spec.inₛ, do_ok_eq_ok] at h₃
    rcases h₃ with ⟨_, _, h₃⟩
    simp only [← h₃, bool_is_instance_of_anyBool]
  · rename_i uid₁ tag _ _ h₄ _ _
    simp only [Cedar.Spec.getTag, Data.Map.findOrErr] at h₃
    generalize hᵢ : entities.tags uid₁ = res₁
    cases res₁ <;> rw [hᵢ] at h₃
    case error => simp only [Except.bind_err, reduceCtorEq] at h₃
    case ok =>
      simp only [Except.bind_ok] at h₃
      split at h₃
      · rename_i ht₁ _ _ _ v₁ heq
        simp only [Except.ok.injEq] at h₃
        subst h₃
        specialize hᵢ₁ hᵢ₁'
        simp only [ht₁] at hᵢ₁
        cases hᵢ₁
        rename_i ht₁
        simp only [InstanceOfEntityType] at ht₁
        simp only [ht₁] at h₄
        simp only [InstanceOfWellFormedEnvironment] at h₁
        rcases h₁ with ⟨_, _, h₁⟩
        simp only [InstanceOfSchema] at h₁
        simp only [Entities.tags, do_ok_eq_ok, Data.Map.findOrErr] at hᵢ
        split at hᵢ
        · simp only [Except.ok.injEq, exists_eq_left'] at hᵢ
          rename_i entry heq₁
          cases h₁.1 uid₁ entry heq₁ with
          | inl h₁ =>
            replace ⟨entry₁, ⟨h₅, _, _, _, h₆⟩⟩ := h₁
            simp [InstanceOfEntityTags] at h₆
            simp [EntitySchema.tags?] at h₄
            rcases h₄ with ⟨_, h₃₁, h₃₂⟩
            simp only [h₅, Option.some.injEq] at h₃₁
            simp only [← h₃₁] at h₃₂
            simp only [h₃₂] at h₆
            simp only [←hᵢ] at heq
            specialize h₆ v₁ (Data.Map.in_list_in_values (Data.Map.find?_mem_toList heq))
            exact type_lifting_preserves_instance_of_type h₆
          | inr h₁ =>
            replace ⟨_, h₆, entry₁, _⟩ := h₁
            simp only [← hᵢ, h₆] at heq
            contradiction
        · simp only [reduceCtorEq, false_and, exists_const] at hᵢ
      · cases h₃

theorem residual_well_typed_is_sound_has_attr_entity
{v : Value}
{x₁ : Residual}
{attr : Attr}
{env : TypeEnv}
{request : Request}
{entities : Entities}
(h₃ : (Residual.hasAttr x₁ attr (CedarType.bool BoolType.anyBool)).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.hasAttr x₁ attr (CedarType.bool BoolType.anyBool)).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate] at h₃
  generalize hᵢ' : x₁.evaluate request entities = res₁
  cases res₁ <;> simp [hᵢ'] at h₃
  simp only [Cedar.Spec.hasAttr, do_ok_eq_ok] at h₃
  rcases h₃ with ⟨_, _, h₃⟩
  simp only [← h₃, bool_is_instance_of_anyBool]

theorem residual_well_typed_is_sound_has_attr_record
{v : Value}
{x₁ : Residual}
{attr : Attr}
{env : TypeEnv}
{request : Request}
{entities : Entities}
(h₃ : (Residual.hasAttr x₁ attr (CedarType.bool BoolType.anyBool)).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.hasAttr x₁ attr (CedarType.bool BoolType.anyBool)).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate] at h₃
  generalize hᵢ' : x₁.evaluate request entities = res₁
  cases res₁ <;> simp [hᵢ'] at h₃
  simp only [Cedar.Spec.hasAttr, do_ok_eq_ok] at h₃
  rcases h₃ with ⟨_, _, h₃⟩
  simp only [← h₃, bool_is_instance_of_anyBool]

theorem residual_well_typed_is_sound_get_attr_entity
{v : Value}
{env : TypeEnv}
{request : Request}
{entities : Entities}
{ety : EntityType}
{rty : RecordType}
{x₁ : Residual}
{attr : Attr}
{ty : CedarType}
(h₁ : InstanceOfWellFormedEnvironment request entities env)
(h₂ : ∀ {v : Value}, x₁.evaluate request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(h₄ : x₁.typeOf = CedarType.entity ety)
(h₅ : (env.ets.attrs? ety).map RecordType.liftBoolTypes = some rty)
(h₆ : Option.map Qualified.getType (Data.Map.find? rty attr) = some ty)
(h₇ : (Residual.getAttr x₁ attr ty).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.getAttr x₁ attr ty).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate] at h₇
  generalize hᵢ : x₁.evaluate request entities = res₁
  cases res₁ <;> simp [hᵢ] at h₇
  rename_i v₁
  replace h₂ := h₂ hᵢ
  simp only [h₄] at h₂
  cases h₂
  rename_i uid het
  simp only [InstanceOfEntityType] at het
  simp only [InstanceOfWellFormedEnvironment, InstanceOfSchema] at h₁
  obtain ⟨_, _, h₁⟩ := h₁
  simp only [Cedar.Spec.getAttr, Cedar.Spec.attrsOf, Entities.attrs, Data.Map.findOrErr, bind_assoc, Except.bind_ok] at h₇
  split at h₇
  · simp only [Except.bind_ok] at h₇
    rename_i data heq
    cases h₁.1 uid data heq with
    | inl h₁ =>
      have ⟨entry, h₁₁, _, h₁₂, _⟩ := h₁
      split at h₇
      · rename_i v₁ heq₁
        simp only [Except.ok.injEq] at h₇
        cases h₁₂
        rename_i h₈ _
        simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at h₅
        rcases h₅ with ⟨a, ⟨a₁, h₅₁, h₅₃⟩, h₅₂⟩
        simp [←het.1] at h₁₁
        simp only [h₁₁, Option.some.injEq] at h₅₁
        simp only [← h₅₁] at h₅₃
        have h₈ := λ qty => h₈ attr v₁ qty heq₁
        simp only at h₈
        simp only [Option.map_eq_some_iff] at h₆
        rcases h₆ with ⟨qty, h₆₁, h₆₂⟩
        simp [←h₅₂, RecordType.liftBoolTypes, lift_bool_types_record_eq_map_on_values] at h₆₁
        replace ⟨qty', h₆₁, h₆₃⟩ := Data.Map.find?_mapOnValues_some' QualifiedType.liftBoolTypes h₆₁
        simp [←h₅₃] at h₆₁
        specialize h₈ qty' h₆₁
        subst h₆₂
        subst h₆₃
        cases qty'
        all_goals {
          simp [QualifiedType.liftBoolTypes, Qualified.getType]
          simp [Qualified.getType] at h₈
          subst h₇
          exact type_lifting_preserves_instance_of_type h₈
        }
      · cases h₇
    | inr h₁ =>
      have ⟨h₁, _, ⟨entry, _⟩⟩ := h₁
      simp only [h₁, Data.Map.find?] at h₇
      contradiction
  · simp only [Except.bind_err, reduceCtorEq] at h₇

theorem residual_well_typed_is_sound_get_attr_record
{v : Value}
{request : Request}
{entities : Entities}
{rty : RecordType}
{x₁ : Residual}
{attr : Attr}
{ty : CedarType}
{env : TypeEnv}
(h₂ : ∀ {v : Value}, x₁.evaluate request entities = Except.ok v → InstanceOfType env v x₁.typeOf)
(h₄ : x₁.typeOf = CedarType.record rty)
(h₅ : Option.map Qualified.getType (Data.Map.find? rty attr) = some ty)
(h₆ : (Residual.getAttr x₁ attr ty).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.getAttr x₁ attr ty).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate] at h₆
  generalize hᵢ : x₁.evaluate request entities = res₁
  cases res₁ <;> simp [hᵢ] at h₆
  rename_i v₁
  replace h₂ := h₂ hᵢ
  simp only [h₄] at h₂
  cases h₂
  rename_i h₇ _
  simp only [Cedar.Spec.getAttr, Cedar.Spec.attrsOf, Data.Map.findOrErr, Except.bind_ok] at h₆
  split at h₆
  · rename_i v₁ heq
    have h₇ := λ qty => h₇ attr v₁ qty heq
    simp only [Option.map_eq_some_iff] at h₅
    rcases h₅ with ⟨qty, h₅₁, h₅₂⟩
    have h₇ := h₇ qty h₅₁
    simp only [Except.ok.injEq] at h₆
    rw [←h₆, ←h₅₂]
    exact h₇
  · cases h₆

theorem residual_well_typed_is_sound_set
{v : Value}
{request : Request}
{entities : Entities}
{ls : List Residual}
{ty : CedarType}
{env : TypeEnv}
(h₁ : ∀ (x : Residual), x ∈ ls → ∀ (v : Value), x.evaluate request entities = Except.ok v → InstanceOfType env v x.typeOf)
(h₂ : ∀ (x : Residual), x ∈ ls → x.typeOf = ty)
(h₃ : (Residual.set ls ty.set).evaluate request entities = Except.ok v)
: InstanceOfType env v (Residual.set ls ty.set).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate, do_ok_eq_ok] at h₃
  obtain ⟨v₁, h₃₁, h₃₂⟩ := h₃
  subst h₃₂
  rw [List.mapM₁_eq_mapM (fun x => Residual.evaluate x request entities)] at h₃₁
  simp only [List.mapM_ok_iff_forall₂] at h₃₁
  have h₄ := List.forall₂_implies_all_right h₃₁
  have hₛ : ∀ v, v ∈ (Data.Set.make v₁) → InstanceOfType env v ty := by
    intro v h
    rw [←Data.Set.make_mem] at h
    obtain ⟨x, hₓ₁, hₓ₂⟩ := h₄ v h
    have h' := h₁ x hₓ₁ v hₓ₂
    rw [h₂ x hₓ₁] at h'
    exact h'
  exact InstanceOfType.instance_of_set (Data.Set.make v₁) ty hₛ

theorem residual_attr_value_has_attrType
{request : Request}
{entities : Entities}
{m : List (Attr × Residual)}
{r : List (Attr × Value)}
{env : TypeEnv}
(h₁ : ∀ (k : Attr) (v : Residual),
  (k, v) ∈ m → ∀ (v_1 : Value), v.evaluate request entities = Except.ok v_1 → InstanceOfType env v_1 v.typeOf)
(h₃ : List.Forall₂ (λ x y => Prod.mk x.fst <$> x.snd.evaluate request entities = Except.ok y) m r) :
List.Forall₂ (λ x y => x.fst = y.fst ∧ InstanceOfType env x.snd (Qualified.getType y.snd)) r (List.map
      (fun x =>
        match x with
        | (a, ty) => (a, Qualified.required ty.typeOf))
      m)
:= by
  cases h₃
  case nil => simp only [List.map_nil, List.Forall₂.nil]
  case cons at₁ av at₂ lv hᵢ₃ hᵢ₄ =>
    have h : (at₁.fst, at₁.snd) ∈ at₁ :: at₂ := by
        simp only [List.mem_cons, true_or]
    generalize hᵢ₅ : at₁.snd.evaluate request entities = res
    cases res
    case error => simp only [hᵢ₅, Except.map_error, reduceCtorEq] at hᵢ₃
    case ok v =>
      simp only [hᵢ₅, Except.map_ok, Except.ok.injEq] at hᵢ₃
      have hᵢ := residual_attr_value_has_attrType (λ k v h => h₁ k v (List.mem_cons_of_mem at₁ h)) hᵢ₄
      have : av = (av.fst, av.snd) := by rfl
      rw [this] at hᵢ₃
      clear this
      simp only [Prod.mk.injEq] at hᵢ₃
      obtain ⟨hᵢ₃₁, hᵢ₃₂⟩ := hᵢ₃
      apply List.Forall₂.cons
      apply And.intro
      · simp only
        symm
        exact hᵢ₃₁
      · simp [Qualified.getType]
        have h₆ := h₁ at₁.fst at₁.snd
        simp at h₆
        specialize h₆ v hᵢ₅
        rw [hᵢ₃₂] at h₆
        exact h₆
      · exact hᵢ

theorem residual_well_typed_is_sound_record
{v : Value}
{request : Request}
{entities : Entities}
{m : List (Attr × Residual)}
{rty : RecordType}
{env : TypeEnv}
(h₁ : ∀ (k : Attr) (v : Residual),
  (k, v) ∈ m → ∀ (v_1 : Value), v.evaluate request entities = Except.ok v_1 → InstanceOfType env v_1 v.typeOf)
(h₂ : rty =
  Data.Map.make
    (List.map
      (fun x =>
        match x with
        | (a, r) => (a, Qualified.required r.typeOf))
      m))
(h₃ : (Residual.record m (CedarType.record rty)).evaluate request entities = Except.ok v) :
  InstanceOfType env v (Residual.record m (CedarType.record rty)).typeOf
:= by
  simp only [Residual.typeOf]
  simp only [Residual.evaluate, do_ok_eq_ok] at h₃
  obtain ⟨r, h₄, h₅⟩ := h₃
  subst h₅
  simp only [List.mapM₂_eq_mapM λ (x : Attr × Residual) => bindAttr x.fst (Residual.evaluate x.snd request entities)] at h₄
  simp only [bindAttr, bind_pure_comp, List.mapM_ok_iff_forall₂] at h₄
  let rty' := (List.map
      (fun x =>
        match x with
        | (a, ty) => (a, Qualified.required ty.typeOf))
      m)
  have h₆ : rty = Data.Map.make rty' := by
    simp only [h₂]
    rfl
  subst h₆
  have h₅ : List.Forall₂ (AttrValueHasAttrType (env := env)) r rty' := by
    exact residual_attr_value_has_attrType h₁ h₄
  apply mk_vals_instance_of_mk_types
  let p := fun (v : Value) (qty : QualifiedType) => InstanceOfType env v qty.getType
  have h₆ := List.canonicalize_preserves_forallᵥ p r rty'
  simp only [List.Forallᵥ] at h₆
  exact h₆ h₅

theorem residual_well_typed_is_sound_call
{v : Value}
{request : Request}
{entities : Entities}
{xfn : ExtFun}
{args : List Residual}
{ty : CedarType}
{env : TypeEnv}
(h₁ : ExtResidualWellTyped xfn args ty)
(h₂ : (Residual.call xfn args ty).evaluate request entities = Except.ok v) :
InstanceOfType env v (Residual.call xfn args ty).typeOf
:= by
  generalize hᵢ : (args.mapM₁ (fun ⟨x₁, _⟩ => Residual.evaluate x₁ request entities)) = res₁
  simp only [Residual.evaluate] at h₂
  cases res₁ <;> simp [hᵢ] at h₂
  simp only [Cedar.Spec.call, Cedar.Spec.res, gt_iff_lt, ge_iff_le] at h₂
  simp only [Residual.typeOf]
  split at h₂ <;>
  cases h₁ <;>
  try cases h₂ <;>
  try simp only [bool_is_instance_of_anyBool]
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.decimal v) .decimal := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.decimal v) .decimal this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.ipaddr v) .ipAddr := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.ipaddr v) .ipAddr this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.datetime v) .datetime := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.datetime v) .datetime this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.duration v) .duration := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.duration v) .duration this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.datetime v) .datetime := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.datetime v) .datetime this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.duration v) .duration := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.duration v) .duration this
    · cases h₂
  case _ =>
    split at h₂
    · rename_i v _
      simp only [Coe.coe, Except.ok.injEq] at h₂
      simp only [← h₂]
      have : InstanceOfExtType (Ext.datetime v) .datetime := by
        simp only [InstanceOfExtType]
      exact InstanceOfType.instance_of_ext (Ext.datetime v) .datetime this
    · cases h₂
  case _ =>
    rename_i dt _ _
    have : InstanceOfExtType (Ext.duration dt.toTime) .duration := by
      simp only [InstanceOfExtType]
    exact InstanceOfType.instance_of_ext (Ext.duration dt.toTime) .duration this
  all_goals { exact InstanceOfType.instance_of_int }

end Cedar.Thm
