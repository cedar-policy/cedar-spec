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

theorem partial_evaluate_is_sound_call
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{xfn : ExtFun}
{args : List Residual}
{ty : CedarType}
(hᵢ₁ : ∀ (x : Residual),
  x ∈ args →
    Except.toOption (x.evaluate req es) = Except.toOption ((TPE.evaluate x preq pes).evaluate req es)) :
  Except.toOption ((Residual.call xfn args ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.call xfn args ty) preq pes).evaluate req es)
:= by
  simp only [TPE.evaluate, TPE.call, List.map₁, List.map_subtype, List.unattach_attach,
    List.mapM_map, Function.comp_def, List.any_map, List.any_eq_true]
  split
  case _ vs heq =>
    simp only [Residual.evaluate, List.mapM₁_eq_mapM (Residual.evaluate · req es), someOrError]
    simp only [List.mapM_some_iff_forall₂] at heq
    have : ∀ x y, (TPE.evaluate x preq pes).asValue = some y → (TPE.evaluate x preq pes).evaluate req es = .ok y :=
      λ x y => as_value_evaluates_to
    replace heq := List.Forall₂.imp this heq
    clear this
    rw [←List.mapM_ok_iff_forall₂] at heq
    have : ∀ (x : Residual),
      x ∈ args →
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
    replace h₅ := to_option_left_ok' h₅
    simp [h₅]
    split
    case _ heq₁ =>
      simp only [to_option_some] at heq₁
      simp only [heq₁, Residual.evaluate]
    case _ heq₁ =>
      rcases to_option_none heq₁ with ⟨_, heq₁⟩
      simp [heq₁, Residual.evaluate, Except.toOption]
  split
  case _ heq₁ =>
    rcases heq₁ with ⟨x, heq₂, heq₃⟩
    specialize hᵢ₁ x heq₂
    simp [Residual.isError] at heq₃
    split at heq₃ <;> cases heq₃
    rename_i heq₃
    simp [heq₃, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    have heq₄ := @List.element_error_implies_mapM_error _ _ _ _ _ (λ x => x.evaluate req es) _ heq₂ hᵢ₁
    rcases heq₄ with ⟨_, heq₄⟩
    simp only [Except.toOption, Residual.evaluate, List.mapM₁_eq_mapM (Residual.evaluate · req es), heq₄, Except.bind_err]
  case _ =>
    simp only [Residual.evaluate, List.mapM₁_eq_mapM (Residual.evaluate · req es)]
    apply to_option_eq_do₁ (λ (x : List Value) => Spec.call xfn x)
    have h₃ := to_option_eq_mapM
      (fun x => x.evaluate req es)
      (fun x => (TPE.evaluate x preq pes).evaluate req es)
      hᵢ₁
    rw [h₃]
    rw [List.mapM_map]
    unfold Function.comp
    simp

end Cedar.Thm
