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
This file proves that level checking for `.ite` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_if {c t e : Expr} {n : Nat} {c₀ c₁: Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf (.ite c t e) c₀ env = Except.ok (tx, c₁))
  (hl : (checkLevel tx n).checked = true)
  (ihc : TypedAtLevelIsSound c)
  (iht : TypedAtLevelIsSound t)
  (ihe : TypedAtLevelIsSound e)
  : evaluate (.ite c t e) request entities = evaluate (.ite c t e) request slice
:= by
    have ⟨ty₁, bty₁, c₁, ty₂, c₂, ty₃, c₃, h₅, h₆, h₇, h₈ ⟩ := type_of_ite_inversion ht
    have ⟨ hgc, v, h₁₃, h₁₄ ⟩ := type_of_is_sound hc hr h₆
    rw [h₇] at h₁₄
    split at h₈
    · replace ⟨h₇, h₈, h₉⟩ := h₈
      subst h₉
      replace h₁₄ := instance_of_ff_is_false h₁₄
      subst h₁₄
      rw [h₅] at hl
      simp only [checkLevel, Bool.and_eq_true] at hl
      have ⟨ ⟨ hl₄, _ ⟩,  hr₄⟩ := hl
      specialize ihc hs hc hr (typed_at_level_def h₆ hl₄)
      specialize ihe hs hc hr (typed_at_level_def h₇ hr₄)
      simp only [evaluate]
      rw [ihc, ihe]
      cases h₁₂ : Result.as Bool (evaluate c request slice) <;> simp only [Except.bind_err, Except.bind_ok]
      simp only [Result.as, Coe.coe, Value.asBool] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq, Except.ok.injEq] at h₁₂
      subst h₁₂
      rename_i h₁₅
      simp only [EvaluatesTo, ihc, h₁₅, reduceCtorEq, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq, false_or] at h₁₃
      subst h₁₃
      simp
    · replace ⟨h₇, h₈, h₉⟩ := h₈
      subst h₉
      replace h₁₄ := instance_of_tt_is_true h₁₄
      subst h₁₄
      rw [h₅] at hl
      simp only [checkLevel, Bool.and_eq_true] at hl
      have ⟨ ⟨ hl₄, hr₄ ⟩,  _⟩ := hl
      specialize ihc hs hc hr (typed_at_level_def h₆ hl₄)
      simp only [evaluate]
      rw [ihc]
      cases h₁₂ : Result.as Bool (evaluate c request slice) <;> simp only [Except.bind_err, Except.bind_ok]
      simp only [Result.as, Coe.coe, Value.asBool] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq, Except.ok.injEq] at h₁₂
      subst h₁₂
      rename_i h₁₅
      simp only [EvaluatesTo, ihc, h₁₅, reduceCtorEq, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq, false_or] at h₁₃
      subst h₁₃
      simp only [GuardedCapabilitiesInvariant, ihc, h₁₅, forall_const] at hgc
      specialize iht hs (capability_union_invariant hc hgc) hr (typed_at_level_def h₇ hr₄)
      simp [iht]
    · replace ⟨h₇, h₈, h₉, h₁₀⟩ := h₈
      rw [h₅] at hl
      simp only [checkLevel, Bool.and_eq_true] at hl
      have ⟨⟨ ha₄, hb₄ ⟩, hc₄ ⟩ := hl
      specialize ihc hs hc hr (typed_at_level_def h₆ ha₄)
      specialize ihe hs hc hr (typed_at_level_def h₈ hc₄)
      simp only [ihc, ihe, evaluate]
      cases h₁₂ : Result.as Bool (evaluate c request slice) <;> simp only [Except.bind_err, Except.bind_ok]
      simp only [Result.as, Coe.coe, Value.asBool] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq, Except.ok.injEq] at h₁₂
      subst h₁₂
      rename_i h₁₄
      rename_i b ; cases b
      case false => simp
      case true =>
        simp only [GuardedCapabilitiesInvariant, ihc, h₁₄, forall_const] at hgc
        specialize iht hs (capability_union_invariant hc hgc) hr (typed_at_level_def h₇ hb₄)
        simp [iht]
