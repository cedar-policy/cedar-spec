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

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Levels.Basic

/-!
This file proves that level checking for `.getAttr` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_get_attr_entity {e : Expr} {tx : TypedExpr} {a : Attr} {n : Nat} {c₀: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (hl : (checkLevel (ty₁.getAttr a tx.typeOf) n).checked = true)
  (h₄ : typeOf e c₀ env = Except.ok (ty₁, c₁'))
  (h₇ : ∃ ety, ty₁.typeOf = CedarType.entity ety)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.getAttr e a) request entities = evaluate (.getAttr e a) request slice
:= by
  replace ⟨ ety, h₇⟩ := h₇
  have ⟨ hgc, v, h₁₃, h₁₄ ⟩ := type_of_is_sound hc hr h₄
  rw [h₇] at h₁₄
  replace ⟨ euid, h₁₄, h₁₅⟩ := instance_of_entity_type_is_entity h₁₄
  subst h₁₄ h₁₅
  simp [checkLevel, h₇] at hl
  have ⟨ ⟨ hl₁, _⟩, hl₂ ⟩ := hl ; clear hl
  have h₈ := check_level_succ hl₂
  have h₉ : (1 + (n - 1)) = n := by omega
  rw [h₉] at h₈ ; clear h₉
  simp [evaluate]
  rw [←ihe hs hc hr (typed_at_level_def h₄ h₈)]
  clear h₈
  simp [getAttr, attrsOf]
  unfold EvaluatesTo at h₁₃
  rcases h₁₃ with h₁₃ | h₁₃ | h₁₃ | h₁₃ <;> simp [h₁₃]
  cases hee : entities.attrs euid
  case error => simp [not_entities_attrs_then_not_slice_attrs hs hee]
  case ok =>
    have h₆ : (checkLevel ty₁ (n - 1) = LevelCheckResult.mk true true) := by
      have h₇ : ∀ r, r = LevelCheckResult.mk r.checked r.root := by simp
      rw [h₇ (checkLevel ty₁ (n - 1))]
      simp [hl₁, hl₂]
    have h₈ : n = 1 + (n - 1) := by omega
    rw [h₈] at hs

    have ⟨ ed, hee', hee''⟩ := entities_attrs_then_find? hee
    subst hee''
    have h₇ := slice_at_succ_n_has_entity hs hc hr h₄ h₆ h₁₃ hee'
    replace h₇ := entities_find?_then_attrs h₇
    simp [h₇]

theorem level_based_slicing_is_sound_get_attr_record {e : Expr} {tx : TypedExpr} {a : Attr} {n : Nat} {c₀: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (hl : (checkLevel (ty₁.getAttr a tx.typeOf) n).checked = true)
  (h₄ : typeOf e c₀ env = Except.ok (ty₁, c₁'))
  (h₇ : ∃ rty, ty₁.typeOf = CedarType.record rty)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.getAttr e a) request entities = evaluate (.getAttr e a) request slice
:= by
  replace ⟨ ety, h₇⟩ := h₇
  have ⟨ hgc, v, h₁₃, h₁₄ ⟩ := type_of_is_sound hc hr h₄
  rw [h₇] at h₁₄
  replace ⟨ euid, h₁₄⟩ := instance_of_record_type_is_record h₁₄
  subst h₁₄
  simp [checkLevel, h₇] at hl
  have ih := ihe hs hc hr (typed_at_level_def h₄ hl)
  simp [evaluate, ←ih]
  cases he : evaluate e request entities <;> simp [he]
  simp [getAttr]
  rename_i v
  unfold EvaluatesTo at h₁₃
  simp [he] at h₁₃
  subst h₁₃
  simp [attrsOf]

theorem level_based_slicing_is_sound_get_attr {e : Expr} {tx : TypedExpr} {a : Attr} {n : Nat} {c₀ c₁: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (e.getAttr a) c₀ env = Except.ok (tx, c₁))
  (hl : (checkLevel tx n).checked = true)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.getAttr e a) request entities = evaluate (.getAttr e a) request slice
:= by
  have ⟨ h₇, ty₁, _, h₄, h₅, h₆ ⟩ := type_of_getAttr_inversion ht
  rw [h₅] at hl
  cases h₆
  case _ h₇ =>
    exact level_based_slicing_is_sound_get_attr_entity hs hc hr hl h₄ h₇ ihe
  case _ h₇ =>
    exact level_based_slicing_is_sound_get_attr_record hs hc hr hl h₄ h₇ ihe
