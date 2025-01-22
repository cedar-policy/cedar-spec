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
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Types

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem typed_at_level_inversion {e : Expr} {c₀: Capabilities} {env : Environment} {n : Nat} :
  typedAtLevel e c₀ env n ->
  ∃ tx c₁, typeOf e c₀ env = .ok (tx, c₁) ∧ checkLevel tx n
:= by
  unfold typedAtLevel
  split
  · rename_i h₂
    rw [h₂]
    simp
  · simp

theorem typed_at_level_def {e : Expr} {tx : TypedExpr} {c₀ c₁: Capabilities} {env : Environment} {n : Nat} :
  typeOf e c₀ env = .ok (tx, c₁) → checkLevel tx n →
  typedAtLevel e c₀ env n
:= by
  intros h₁
  unfold typedAtLevel
  rw [h₁]
  simp

def TypedAtLevelIsSound₀ (e : Expr) : Prop := ∀ {c : Capabilities} {env :Environment} {request : Request} {entities : Entities},
  -- slice = entities.sliceAtLevel request 0 →
  CapabilitiesInvariant c request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typedAtLevel e c env 0 →
  evaluate e request entities = evaluate e request Map.empty

theorem level_based_slicing_is_sound_if₀ {c t e : Expr} {c₀ c₁: Capabilities} {env : Environment} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (.ite c t e) c₀ env = Except.ok (tx, c₁))
  (h₄ : checkLevel tx 0 = true)
  (ihc : TypedAtLevelIsSound₀ c)
  (iht : TypedAtLevelIsSound₀ t)
  (ihe : TypedAtLevelIsSound₀ e)
  : evaluate (.ite c t e) request entities = evaluate (.ite c t e) request Map.empty
:= by
    have ⟨ty₁, bty₁, c₁, ty₂, c₂, ty₃, c₃, h₅, h₆, h₇ ⟩ := type_of_ite_inversion h₃
    have ⟨ hgc, v, h₁₃, h₁₄ ⟩ := type_of_is_sound hc h₂ h₅
    rw [h₆] at h₁₄
    split at h₇
    · replace ⟨h₇, h₈, _⟩ := h₇
      subst h₈
      replace h₁₄ := instance_of_ff_is_false h₁₄
      subst h₁₄
      simp only [checkLevel, Bool.and_eq_true] at h₄
      have ⟨ ⟨ hl₄, _ ⟩,  hr₄⟩ := h₄
      specialize ihc hc h₂ (typed_at_level_def h₅ hl₄)
      specialize ihe hc h₂ (typed_at_level_def h₇ hr₄)
      simp only [evaluate]
      rw [ihc, ihe]
      cases h₁₂ : Result.as Bool (evaluate c request Map.empty) <;> simp only [Except.bind_err, Except.bind_ok]
      simp only [Result.as, Coe.coe, Value.asBool] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq, Except.ok.injEq] at h₁₂
      subst h₁₂
      rename_i h₁₅
      simp only [EvaluatesTo, ihc, h₁₅, reduceCtorEq, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq, false_or] at h₁₃
      subst h₁₃
      simp
    · replace ⟨h₇, h₈, _⟩ := h₇
      subst h₈
      replace h₁₄ := instance_of_tt_is_true h₁₄
      subst h₁₄
      simp only [checkLevel, Bool.and_eq_true] at h₄
      have ⟨ ⟨ hl₄, _ ⟩,  hr₄⟩ := h₄
      specialize ihc hc h₂ (typed_at_level_def h₅ hl₄)
      simp only [evaluate]
      rw [ihc]
      cases h₁₂ : Result.as Bool (evaluate c request Map.empty) <;> simp only [Except.bind_err, Except.bind_ok]
      simp only [Result.as, Coe.coe, Value.asBool] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq, Except.ok.injEq] at h₁₂
      subst h₁₂
      rename_i h₁₅
      simp only [EvaluatesTo, ihc, h₁₅, reduceCtorEq, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq, false_or] at h₁₃
      subst h₁₃
      simp only [GuardedCapabilitiesInvariant, ihc, h₁₅, forall_const] at hgc
      specialize iht (capability_union_invariant hc hgc) h₂ (typed_at_level_def h₇ hr₄)
      simp [iht]
    · replace ⟨h₇, h₈, h₉, h₁₀, _⟩ := h₇
      rw [h₉] at h₄
      simp only [checkLevel, Bool.and_eq_true] at h₄
      have ⟨⟨ ha₄, hb₄ ⟩, hc₄ ⟩ := h₄
      specialize ihc hc h₂ (typed_at_level_def h₅ ha₄)
      specialize ihe hc h₂ (typed_at_level_def h₈ hc₄)
      simp only [ihc, ihe, evaluate]
      cases h₁₂ : Result.as Bool (evaluate c request Map.empty) <;> simp only [Except.bind_err, Except.bind_ok]
      simp only [Result.as, Coe.coe, Value.asBool] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq] at h₁₂
      split at h₁₂ <;> try simp only [reduceCtorEq, Except.ok.injEq] at h₁₂
      subst h₁₂
      rename_i h₁₄
      rename_i b ; cases b
      case false => simp
      case true =>
        simp only [GuardedCapabilitiesInvariant, ihc, h₁₄, forall_const] at hgc
        specialize iht (capability_union_invariant hc hgc) h₂ (typed_at_level_def h₇ hb₄)
        simp [iht]

theorem level_based_slicing_is_sound₀ {e : Expr} {c : Capabilities} {env : Environment} {request : Request} {entities : Entities}
  -- slice = entities.sliceAtLevel request 0 →
  (hc : CapabilitiesInvariant c request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₁ : typedAtLevel e c env 0) :
  evaluate e request entities = evaluate e request Map.empty
:= by
  have ⟨_, _, h₃, h₄⟩ := typed_at_level_inversion h₁
  cases e
  case lit => simp [evaluate]
  case var v => cases v <;> simp [evaluate]
  case ite c t e =>
    have ihc := @level_based_slicing_is_sound₀ c
    have iht := @level_based_slicing_is_sound₀ t
    have ihe := @level_based_slicing_is_sound₀ e
    apply level_based_slicing_is_sound_if₀ hc h₂ h₃ h₄ ihc iht ihe
  case and => sorry
  case or => sorry
  case unaryApp => sorry
  case binaryApp => sorry
  case getAttr => sorry
  case hasAttr => sorry
  case set => sorry
  case record => sorry
  case call => sorry

-- theorem level_based_slicing_is_sound' {e : Expr} {env : Environment} {request : Request} {entities slice : Entities} {n : Nat} :
--   slice = entities.sliceAtLevel request n →
--   typedAtLevel e env n →
--   evaluate e request entities = evaluate e request slice
-- := by
--   intros h₁ h₂
--   cases n
--   ·
--     simp [Entities.sliceAtLevel, Entities.sliceAtLevel.sliceAtLevel, Map.make, List.canonicalize] at h₁
--     subst slice
--     simp [typedAtLevel] at h₂
--     split at h₂ <;> try simp at h₂
--     -- unfold checkLevel at h₂



/-
theorem level_based_slicing_is_sound {e : Expr} {env : Environment} {request : Request} {entities slice : Entities} {n : Nat} :
  slice = entities.sliceAtLevel request n →
  typedAtLevel e env n →
  evaluate e request entities = evaluate e request slice
:= by
  intros h₁
  cases e
  case lit =>
    simp [evaluate]
  case var v =>
    cases v <;> simp [evaluate]
  case ite c t e =>
    intros h₂
    have ⟨_, _, h₃, h₄⟩ := typed_at_level_then_type_and_level h₂
    have ⟨ty₁, bty₁, c₁, ty₂, c₂, ty₃, c₃, h₅, h₆, h₇ ⟩  := type_of_ite_inversion h₃
    split at h₇
    · replace ⟨h₇, h₈, h₉⟩ := h₇
      subst c₃ ty₃
      have h₁₀ : typedAtLevel e env n := by sorry
      have h₁₁ := level_based_slicing_is_sound h₁ h₁₀
      have hc := empty_capabilities_invariant request entities
      have ⟨ hgc, v, h₁₂, h₁₃ ⟩ := type_of_is_sound hc (by sorry) h₅
      have hc' := empty_capabilities_invariant request slice
      have ⟨ hgc', v', h'₁₂, h'₁₃ ⟩ := type_of_is_sound hc' (by sorry) h₅
      rw [h₆] at h₁₃
      rw [h₆] at h'₁₃
      have h₁₄ := instance_of_ff_is_false h₁₃
      have h'₁₄ := instance_of_ff_is_false h'₁₃
      subst v v'
      simp [evaluate]
      cases h₁₂ <;> cases h'₁₂
      · rename_i h₁₂ h'₁₂
        rw [h₁₂, h'₁₂]
        simp [Result.as]
      · rename_i h₁₂ h'₁₂
        cases h₁₂ <;> cases h'₁₂
      · sorry
      · sorry









      unfold EvaluatesTo at h₁₂


    simp [evaluate]
    intros h₂
    simp [typedAtLevel] at h₂
    split at h₂


    cases h₂ : evaluate c request entities <;>
    cases h₃ : evaluate c request slice <;>
    simp [Result.as, bind, Except.bind]
    case error.ok =>
      unfold typedAtLevel
      cases h₄ : typeOf (c.ite t e) ∅ env <;> simp
      intros
      have ih := level_based_slicing_is_sound h₁



    --case error.error =>
    --  unfold typedAtLevel
    --  cases h₄ : typeOf (c.ite t e) ∅ env
    --  case error => simp
    --  case ok =>
    --    simp ; intros



  case and => sorry
  case or => sorry
  case unaryApp => sorry
  case binaryApp => sorry
  case getAttr => sorry
  case hasAttr => sorry
  case set => sorry
  case record => sorry
  case call => sorry

-/
