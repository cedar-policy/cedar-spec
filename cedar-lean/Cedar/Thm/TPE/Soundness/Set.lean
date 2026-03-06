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

theorem partial_evaluate_is_sound_set
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{ls : List Residual}
{ty : CedarType}
(hᵢ₁ : ∀ (x : Residual),
  x ∈ ls →
    Except.toOption (x.evaluate req es) = Except.toOption ((TPE.evaluate x preq pes).evaluate req es)) :
  Except.toOption ((Residual.set ls ty.set).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.set ls ty.set) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, List.map₁, TPE.set]
  split
  case _ vs heq =>
    simp [Residual.evaluate]
    have : (Except.ok (Value.set (Data.Set.make vs)) : Except Spec.Error Value).toOption = .some (Value.set (Data.Set.make vs)) := by
      simp only [Except.toOption]
    rw [this]
    clear this
    simp only [List.mapM₁_eq_mapM (Residual.evaluate · req es), to_option_some, do_ok_eq_ok, Value.set.injEq]
    exists vs
    simp only [and_true]
    simp [List.mapM_some_iff_forall₂] at heq
    have : ∀ x y, (TPE.evaluate x preq pes).asValue = some y → (TPE.evaluate x preq pes).evaluate req es = .ok y := by
      intro x y h
      rcases as_value_some h with ⟨_, h⟩
      simp [h, Residual.evaluate]
    replace heq := List.Forall₂.imp this heq
    clear this
    rw [←List.mapM_ok_iff_forall₂] at heq
    have : ∀ (x : Residual),
      x ∈ ls →
      Except.toOption ((TPE.evaluate x preq pes).evaluate req es) =
      Except.toOption (x.evaluate req es) := by
      intro x h
      specialize hᵢ₁ x h
      symm
      exact hᵢ₁
    have h₅ := to_option_eq_mapM
      (λ x => (TPE.evaluate x preq pes).evaluate req es)
      (λ x => x.evaluate req es)
      this
    simp [heq] at h₅
    exact to_option_left_ok' h₅
  case _ heq =>
    split
    case isTrue heq₁ =>
      rcases heq₁ with ⟨x, heq₂, heq₃⟩
      specialize hᵢ₁ x heq₂
      simp [Residual.isError] at heq₃
      split at heq₃ <;> cases heq₃
      rename_i heq₃
      simp [heq₃, Residual.evaluate] at hᵢ₁
      replace ⟨_, hᵢ₁⟩ := to_option_right_err hᵢ₁
      simp only [Residual.evaluate, List.mapM₁_eq_mapM (Residual.evaluate · req es)]
      have heq₄ := @List.element_error_implies_mapM_error _ _ _ _ _ (λ x => x.evaluate req es) _ heq₂ hᵢ₁
      rcases heq₄ with ⟨_, heq₄⟩
      simp [heq₄, Except.toOption]
    case isFalse =>
      simp only [Residual.evaluate, List.mapM₁_eq_mapM (Residual.evaluate · req es)]
      apply to_option_eq_do₁ (λ (x : List Value) => (Except.ok (Value.set (Data.Set.make x))))
      -- We need to show that evaluating the original list gives the same result as evaluating the TPE-transformed list
      -- Since we're in the case where List.mapM (Residual.asValue ∘ fun x => TPE.evaluate x preq pes) ls = none
      -- and ¬∃ x, x ∈ ls ∧ (TPE.evaluate x preq pes).isError = true
      -- we can directly apply our hypothesis hᵢ₁
      have h₃ :=  to_option_eq_mapM
        (fun x => x.evaluate req es)
        (fun x => (TPE.evaluate x preq pes).evaluate req es)
        hᵢ₁
      rw [h₃]
      rw [List.mapM_map]
      unfold Function.comp
      simp



end Cedar.Thm
