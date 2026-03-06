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

theorem partial_evaluate_is_sound_record
{m : List (Attr × Residual)}
{rty : RecordType}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
(hᵢ₁ : ∀ (k : Attr) (v : Residual),
  (k, v) ∈ m →
    Except.toOption (v.evaluate req es) = Except.toOption ((TPE.evaluate v preq pes).evaluate req es)) :
  Except.toOption ((Residual.record m (CedarType.record rty)).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.record m (CedarType.record rty)) preq pes).evaluate req es)
:= by
  simp only [TPE.evaluate, TPE.record,
    List.map₁_eq_map (fun (x : Attr × Residual) => (x.fst, TPE.evaluate x.snd preq pes)),
    List.any_map, List.any_eq_true, Function.comp_apply, Prod.exists]
  split
  case _ vs heq =>
    simp only [Residual.evaluate, List.mapM₂_eq_mapM λ x => bindAttr x.fst (Residual.evaluate x.snd req es)]
    have : (Except.ok (Value.record (Data.Map.make vs)) : Except Spec.Error Value).toOption = .some (Value.record (Data.Map.make vs)) := by
      simp only [Except.toOption]
    rw [this]
    clear this
    simp [to_option_some, do_ok_eq_ok]
    exists vs
    simp only [and_true]
    simp only [List.mapM_map, List.mapM_some_iff_forall₂] at heq
    have : ∀ (x : Attr × Residual) y, bindAttr x.fst (TPE.evaluate x.snd preq pes).asValue = some y → bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es) = .ok y := by
      intro x y h
      simp only [bindAttr] at h ⊢
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      rcases h with ⟨_, h₁, h₂⟩
      simp [h₂, as_value_evaluates_to h₁]
    replace heq := List.Forall₂.imp this heq
    clear this
    rw [←List.mapM_ok_iff_forall₂] at heq
    have : ∀ x,
      x ∈ m →
      Except.toOption (bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es)) =
      Except.toOption (bindAttr x.fst (x.snd.evaluate req es)) := by
      intro x h
      have hrfl : x = (x.fst, x.snd) := by rfl
      rw [hrfl] at h
      specialize hᵢ₁ x.fst x.snd h
      simp [bindAttr]
      symm
      exact to_option_eq_map (Prod.mk x.fst ·) hᵢ₁
    have h₁ := to_option_eq_mapM
      (λ (x : Attr × Residual) => bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es))
      (λ x => bindAttr x.fst (x.snd.evaluate req es))
      this
    simp [heq] at h₁
    replace h₁ := to_option_left_ok' h₁
    exact h₁
  split
  case _ h₁ =>
    simp only [
      List.map₁_eq_map λ (x : Attr × Residual) => (x.fst, TPE.evaluate x.snd preq pes),
      List.any_map, List.any_eq_true, Function.comp_apply, Prod.exists] at h₁
    rcases h₁ with ⟨k, v, h₂, h₃⟩
    simp [Residual.isError] at h₃
    split at h₃ <;> simp at h₃
    rename_i heq
    specialize hᵢ₁ k v h₂
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨err, hᵢ₁⟩
    simp only [Residual.evaluate, List.mapM₂_eq_mapM λ x => bindAttr x.fst (Residual.evaluate x.snd req es)]
    have : (fun (x: Attr × Residual) => bindAttr x.fst (x.snd.evaluate req es)) (k, v) = .error err := by
      simp only [bindAttr, hᵢ₁, bind_pure_comp, Except.map_error]
    have h₄ := @List.element_error_implies_mapM_error _ _ _ _ _ (fun (x: Attr × Residual) => bindAttr x.fst (x.snd.evaluate req es)) _ h₂ this
    rcases h₄ with ⟨_, h₄⟩
    simp [h₄, Except.toOption]
  case _ =>
    simp only [Residual.evaluate,
      List.mapM₂_eq_mapM λ x => bindAttr x.fst (Residual.evaluate x.snd req es), List.mapM_map,
      Function.comp_def]
    apply to_option_eq_do₁
    have : ∀ x,
      x ∈ m →
      Except.toOption (bindAttr x.fst (x.snd.evaluate req es)) =
      Except.toOption (bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es)) := by
      intro x h
      have hrfl : x = (x.fst, x.snd) := by rfl
      rw [hrfl] at h
      specialize hᵢ₁ x.fst x.snd h
      simp [bindAttr]
      exact to_option_eq_map (Prod.mk x.fst ·) hᵢ₁
    exact to_option_eq_mapM
      (fun (x : Attr × Residual) => bindAttr x.fst (x.snd.evaluate req es))
      (fun x => bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es))
      this

end Cedar.Thm
