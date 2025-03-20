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
import Cedar.Validation.TypedExpr
import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm
import Cedar.Spec

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Thm
open Cedar.Spec

theorem well_typed_is_sound_get_attr_entity
{v : Value}
{env : Environment}
{request : Request}
{entities : Entities}
{ety : EntityType}
{rty : RecordType}
{x₁ : TypedExpr}
{attr : Attr}
{ty : CedarType}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(h₂ : WellTypedIsSound x₁)
(h₃ : TypedExpr.WellTyped env x₁)
(h₄ : x₁.typeOf = CedarType.entity ety)
(h₅ : env.ets.attrs? ety = some rty)
(h₆ : Option.map Qualified.getType (Data.Map.find? rty attr) = some ty)
(h₇ : (do
  let v₁ ← evaluate x₁.toExpr request entities
  getAttr v₁ attr entities) = Except.ok v) :
InstanceOfType v (x₁.getAttr attr ty).typeOf
:= by
  simp only [WellTypedIsSound] at h₂
  generalize hᵢ' : evaluate x₁.toExpr request entities = res₁
  cases res₁ <;> simp [hᵢ'] at h₇
  replace h₂ := h₂ h₁ h₃ hᵢ'
  simp only [h₄] at h₂
  cases h₂
  rename_i het
  simp only [InstanceOfEntityType] at het
  simp only [RequestAndEntitiesMatchEnvironment, InstanceOfEntitySchema] at h₁
  rcases h₁ with ⟨_, h₁, _⟩
  simp only [getAttr, attrsOf, Entities.attrs, Data.Map.findOrErr, bind_assoc, Except.bind_ok] at h₇
  rename_i uid _ _
  split at h₇
  · simp only [Except.bind_ok] at h₇
    rename_i data heq
    have ⟨entry, h₁₁, _, h₁₂, _⟩  := h₁ uid data heq
    split at h₇
    · rename_i v₁ heq₁
      simp only [Except.ok.injEq] at h₇
      cases h₁₂
      rename_i h₈ _
      simp only [EntitySchema.attrs?, Option.map_eq_some'] at h₅
      rcases h₅ with ⟨a, h₅₁, h₅₂⟩
      simp [←het] at h₁₁
      simp only [h₁₁, Option.some.injEq] at h₅₁
      simp only [← h₅₁] at h₅₂
      have h₈ := λ qty => h₈ attr v₁ qty heq₁
      simp only [h₅₂] at h₈
      simp only [Option.map_eq_some'] at h₆
      rcases h₆ with ⟨qty, h₆₁, h₆₂⟩
      have h₈ := h₈ qty h₆₁
      simp only [h₆₂] at h₈
      simp [TypedExpr.typeOf, ←h₇]
      exact h₈
    · cases h₇
  · simp only [Except.bind_err, reduceCtorEq] at h₇

theorem well_typed_is_sound_get_attr_record
{v : Value}
{env : Environment}
{request : Request}
{entities : Entities}
{rty : RecordType}
{x₁ : TypedExpr}
{attr : Attr}
{ty : CedarType}
(h₁ : RequestAndEntitiesMatchEnvironment env request entities)
(h₂ : WellTypedIsSound x₁)
(h₃ : TypedExpr.WellTyped env x₁)
(h₄ : x₁.typeOf = CedarType.record rty)
(h₅ : Option.map Qualified.getType (Data.Map.find? rty attr) = some ty)
(h₆ : (do
  let v₁ ← evaluate x₁.toExpr request entities
  getAttr v₁ attr entities) = Except.ok v) :
InstanceOfType v (x₁.getAttr attr ty).typeOf
:= by
  simp only [WellTypedIsSound] at h₂
  generalize hᵢ' : evaluate x₁.toExpr request entities = res₁
  cases res₁ <;> simp [hᵢ'] at h₆
  replace h₂ := h₂ h₁ h₃ hᵢ'
  simp only [h₄] at h₂
  cases h₂
  rename_i h₇ _
  simp only [getAttr, attrsOf, Data.Map.findOrErr, Except.bind_ok] at h₆
  split at h₆
  · rename_i v₁ heq
    have h₇ := λ qty => h₇ attr v₁ qty heq
    simp only [Option.map_eq_some'] at h₅
    rcases h₅ with ⟨qty, h₅₁, h₅₂⟩
    have h₇ := h₇ qty h₅₁
    simp only [Except.ok.injEq] at h₆
    simp [TypedExpr.typeOf, ←h₆, ←h₅₂]
    exact h₇
  · cases h₆

end Cedar.Thm
