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
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Levels.Basic
import Cedar.Thm.Validation.Levels.Slice

/-!
This file proves that level checking for `.binaryApp` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem not_dereferencing_apply₂_invariant_entities {op : BinaryOp} {entities entities' : Entities} {v₁ v₂ : Value}
  (hop : ¬ DereferencingBinaryOp op)
  : apply₂ op v₁ v₂ entities = apply₂ op v₁ v₂ entities'
:= by
  cases op <;> simp only [DereferencingBinaryOp, not_true_eq_false] at hop
  all_goals
    cases v₁ <;> cases v₂ <;> simp only [apply₂]
    try (
      rename_i p₁ p₂
      cases p₁ <;> cases p₂ <;> simp
    )

theorem level_based_slicing_is_sound_inₑ {e₁ : Expr} {euid₁ euid₂ : EntityUID} {n : Nat} {c₀ c₁ : Capabilities} {entities slice : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e₁ c₀ env = Except.ok (tx₁, c₁))
  (hl : TypedExpr.AtLevel tx₁ n)
  (hel : ¬ TypedExpr.EntityLitViaPath tx₁ [])
  (he : evaluate e₁ request entities = .ok (Value.prim (Prim.entityUID euid₁)))
  (hs : some slice = entities.sliceAtLevel request (n + 1))
  : inₑ euid₁ euid₂ entities = inₑ euid₁ euid₂ slice
:= by
  simp only [inₑ]
  cases heq : euid₁ == euid₂ <;> simp only [Bool.false_or, Bool.true_or]
  have hfeq := checked_eval_entity_find_entities_eq_find_slice hc hr ht hl hel he hs
  simp [hfeq, Entities.ancestorsOrEmpty]

theorem level_based_slicing_is_sound_binary_app {op : BinaryOp} {e₁ e₂ : Expr} {n : Nat} {c₀ c₁: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.binaryApp op e₁ e₂) c₀ env = Except.ok (tx, c₁))
  (hl : TypedExpr.AtLevel tx n)
  (ihe₁ : TypedAtLevelIsSound e₁)
  (ihe₂ : TypedAtLevelIsSound e₂)
  : evaluate (.binaryApp op e₁ e₂) request entities = evaluate (.binaryApp op e₁ e₂) request slice
:= by
  replace ⟨tx₁, c₁, tx₂, c₂, htx₁, htx₂, ty, htx⟩ := type_of_binaryApp_inversion ht
  subst tx
  simp only [evaluate]
  cases hl
  case getTag hel hl₁ hl₂ | hasTag hel hl₁ hl₂ =>
    specialize ihe₂ hs hc hr htx₂ hl₂
    rw [←ihe₂]
    have hl₁' := check_level_succ hl₁
    specialize ihe₁ hs hc hr htx₁ hl₁'
    rw [←ihe₁]
    cases he₁ : evaluate e₁ request entities <;> simp only [Except.bind_ok, Except.bind_err]
    cases he₂ : evaluate e₂ request entities <;> simp only [Except.bind_ok, Except.bind_err]
    rename_i v₁ v₂
    cases v₁ <;> cases v₂ <;> simp only [apply₂]
    rename_i p₁ p₂
    cases p₁ <;> cases p₂ <;> simp only
    rename_i euid _
    have hfeq := checked_eval_entity_find_entities_eq_find_slice hc hr htx₁ hl₁ hel he₁ hs
    simp only [hfeq, hasTag, getTag, Entities.tagsOrEmpty, Entities.tags, Map.findOrErr]
  case mem hel hl₁ hl₂ =>
    specialize ihe₂ hs hc hr htx₂ hl₂
    rw [←ihe₂]
    have hl₁' := check_level_succ hl₁
    specialize ihe₁ hs hc hr htx₁ hl₁'
    rw [←ihe₁]
    cases he₁ : evaluate e₁ request entities <;> simp only [Except.bind_ok, Except.bind_err]
    cases he₂ : evaluate e₂ request entities <;> simp only [Except.bind_ok, Except.bind_err]
    rename_i v₁ v₂
    cases v₁ <;> cases v₂ <;> simp only [apply₂]
    case prim =>
      rename_i p₁ p₂
      cases p₁ <;> cases p₂ <;> simp only
      simp [level_based_slicing_is_sound_inₑ hc hr htx₁ hl₁ hel he₁ hs]
    case set =>
      rename_i p₁ sv
      cases p₁ <;> simp only
      simp [inₛ, level_based_slicing_is_sound_inₑ hc hr htx₁ hl₁ hel he₁ hs]
  case binaryApp hop hl₁ hl₂ =>
    specialize ihe₁ hs hc hr htx₁ hl₁
    specialize ihe₂ hs hc hr htx₂ hl₂
    rw [ihe₁, ihe₂]
    simp [(@not_dereferencing_apply₂_invariant_entities op entities slice · · hop)]
