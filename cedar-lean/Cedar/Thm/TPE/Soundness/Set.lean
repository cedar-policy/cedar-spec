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
    simp only [Residual.evaluate, List.mapM₁_eq_mapM (Residual.evaluate · req es)]
    simp only [List.mapM_some_iff_forall₂, Function.comp_apply] at heq
    have h_tpe_ok : List.mapM (fun x => (TPE.evaluate x preq pes).evaluate req es) ls = .ok vs := by
      rw [List.mapM_ok_iff_forall₂]
      exact List.Forall₂.imp (fun _ _ h => asValue_evaluate_val h req es) heq
    have h₅ : List.mapM (λ x => x.evaluate req es) ls = .ok vs := by
      have h₅ := List.mapM_to_option_congr hᵢ₁
      simp only [h_tpe_ok] at h₅
      exact to_option_left_ok' h₅.symm
    simp [h₅]
  case _ heq =>
    split
    case _ heq₁ =>
      simp only [evaluate_error, toOption_error, toOption_eq_none_iff]
      rename_i e _
      simp only [List.findSome?_eq_some_iff, asError_some, exists_and_right] at heq₁
      rcases heq₁ with ⟨ls', arg, ⟨ls'', heq₂⟩, heq₃, heq₄⟩
      have h_mem : arg ∈ List.map (TPE.evaluate · preq pes) ls := by
        rw [heq₂]; simp
      have ⟨a, h_a_mem, h_a_eq⟩ := List.mem_map.mp h_mem
      have h_is_err : (TPE.evaluate a preq pes).isError := by
        rw [h_a_eq, heq₃]; simp [Residual.isError]
      have ⟨_, h_tpe_err⟩ := isError_evaluate_err h_is_err req es
      have h_none : (a.evaluate req es).toOption = .none := by
        rw [hᵢ₁ a h_a_mem, h_tpe_err]; simp [Except.toOption]
      have ⟨err, h_err⟩ := (toOption_eq_none_iff).mp <|
        List.element_to_option_none_implies_mapM_none (f := (Residual.evaluate · req es)) h_a_mem h_none
      exists err
      simp [Residual.evaluate, List.mapM₁_eq_mapM (Residual.evaluate · req es), h_err]
    case _ =>
      simp only [Residual.evaluate, List.mapM₁_eq_mapM (Residual.evaluate · req es)]
      apply to_option_eq_do₁ (λ (x : List Value) => (Except.ok (Value.set (Data.Set.make x))))
      -- We need to show that evaluating the original list gives the same result as evaluating the TPE-transformed list
      -- Since we're in the case where List.mapM (Residual.asValue ∘ fun x => TPE.evaluate x preq pes) ls = none
      -- and ¬∃ x, x ∈ ls ∧ (TPE.evaluate x preq pes).isError = true
      -- we can directly apply our hypothesis hᵢ₁
      rw [List.mapM_to_option_congr hᵢ₁]
      rw [List.mapM_map]
      unfold Function.comp
      simp



end Cedar.Thm
