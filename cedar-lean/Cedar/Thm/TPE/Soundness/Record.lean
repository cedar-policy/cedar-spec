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
      cases h₁ : (TPE.evaluate x.snd preq pes).asValue <;>
        simp only [h₁, Option.pure_def, Option.bind_none_fun, reduceCtorEq, Option.bind_some_fun, Option.some.injEq] at h
      simp [h, asValue_evaluate_val h₁]
    replace heq := List.Forall₂.imp this heq
    clear this
    rw [←List.mapM_ok_iff_forall₂] at heq
    have : ∀ x ∈ m,
      Except.toOption (bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es)) =
      Except.toOption (bindAttr x.fst (x.snd.evaluate req es))
    := by
      intro x h
      specialize hᵢ₁ x.fst x.snd h
      simp only [bindAttr, bind_pure_comp]
      rw [to_option_distr_fmap]
      rw [to_option_distr_fmap]
      rw [hᵢ₁]
    have h₁ := List.mapM_to_option_congr this
    simp [heq] at h₁
    replace h₁ := to_option_left_ok' h₁
    exact h₁
  split
  case _ h₁ =>
    simp only [
      List.map₁_eq_map λ (x : Attr × Residual) => (x.fst, TPE.evaluate x.snd preq pes),
      List.any_map, List.any_eq_true, Function.comp_apply, Prod.exists] at h₁
    rcases h₁ with ⟨k, v, h₂, h₃⟩
    have ⟨tpe_err, h_tpe_err⟩ := isError_evaluate_err h₃ req es
    specialize hᵢ₁ k v h₂
    rw [h_tpe_err] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨err, hᵢ₁⟩
    simp only [Residual.evaluate, List.mapM₂_eq_mapM λ x => bindAttr x.fst (Residual.evaluate x.snd req es)]
    have h₄ := @List.element_error_implies_mapM_error _ _ _ _ _
      (fun (x: Attr × Residual) => bindAttr x.fst (x.snd.evaluate req es)) _
      h₂ (show (fun (x: Attr × Residual) => bindAttr x.fst (x.snd.evaluate req es)) (k, v) = .error err from
        by simp only [bindAttr, hᵢ₁, bind_pure_comp, Except.map_error])
    rcases h₄ with ⟨_, h₄⟩
    simp [h₄, Except.toOption]
  case _ =>
    simp only [Residual.evaluate,
      List.mapM₂_eq_mapM λ x => bindAttr x.fst (Residual.evaluate x.snd req es), List.mapM_map,
      Function.comp_def]
    apply to_option_eq_do₁
    have : ∀ x ∈ m,
      Except.toOption (bindAttr x.fst (x.snd.evaluate req es)) =
      Except.toOption (bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es))
    := by
      intro x h
      specialize hᵢ₁ x.fst x.snd h
      simp [bindAttr]
      rw [to_option_distr_fmap]
      rw [to_option_distr_fmap]
      rw [hᵢ₁]
    exact List.mapM_to_option_congr this

end Cedar.Thm
