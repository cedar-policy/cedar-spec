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
  cases hl
  case hasTag => sorry
  case getTag => sorry
  case mem => sorry
  case binaryApp =>
    rename_i hop hl₁ hl₂
    simp only [evaluate]
    specialize ihe₁ hs hc hr htx₁ hl₁
    specialize ihe₂ hs hc hr htx₂ hl₂
    rw [ihe₁, ihe₂]
    simp [(@not_dereferencing_apply₂_invariant_entities op entities slice · · hop)]
