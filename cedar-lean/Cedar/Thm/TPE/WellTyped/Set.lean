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
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

import Cedar.Thm.TPE.WellTyped.Basic

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

/--
Helper theorem: Partial evaluation preserves well-typedness for set residuals.
-/
theorem partial_eval_well_typed_set {env : TypeEnv} {ls : List Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  (∀ r ∈ ls, Residual.WellTyped env (TPE.evaluate r preq pes)) →
  PEWellTyped env (Residual.set ls ty) (TPE.evaluate (Residual.set ls ty) preq pes) req preq es pes
:= by
  intros h_ls_wt h_wf h_ref h_wt
  cases h_wt
  rename_i ty₁ h₀ h₁ h₂
  simp only [TPE.evaluate, TPE.set, List.any_eq_true]
  split
  case h_1 x xs h₃ =>
    apply Residual.WellTyped.val
    apply InstanceOfResidualValueType.instance_of_set
    intro v h₄
    unfold List.map₁ List.attach List.attachWith at h₃
    rw [List.map_pmap_subtype (fun x => TPE.evaluate x preq pes), List.mapM_map] at h₃
    rw [Set.mem_make] at h₄
    have h₅ := List.mem_mapM_some_implies_exists_unmapped h₃ h₄
    rcases h₅ with ⟨y, h₆, h₇⟩
    specialize h₀ y h₆
    let h₈ := partial_eval_preserves_typeof _ h₀ preq pes
    simp only [Function.comp_apply, Residual.asValue] at h₇
    sorry
    /-
    split at h₇
    case h_2 =>
      contradiction
    case h_1 x₂ v₂ ty₂ h₉ =>
      injection h₇
      rename_i h₇
      rw [h₇] at h₉
      let ih := h_ls_wt y h₆
      rw [h₉] at ih
      cases ih
      case val h₁₀ =>
      specialize h₁ y h₆
      rw [h₁] at h₈
      rw [h₉] at h₈
      simp only [Residual.typeOf] at h₈
      rw [← h₈]
      exact h₁₀
      -/
  case h_2 x h₃ =>
    split
    . apply Residual.WellTyped.error
    case isFalse _ =>
      apply Residual.WellTyped.set
      . intro x h₅
        simp only [List.map₁, List.attach, List.map_subtype, List.unattach_attachWith, List.mem_map] at h₅
        rcases h₅ with ⟨x₂, h₆, h₇⟩
        specialize h₀ x₂ h₆
        let ih := h_ls_wt x₂ h₆
        rw [← h₇]
        exact ih
      . intro x h₅
        simp only [List.map₁, List.attach, List.map_subtype, List.unattach_attachWith, List.mem_map] at h₅
        rcases h₅ with ⟨x₂, h₆, h₇⟩
        specialize h₀ x₂ h₆
        let h₆ := partial_eval_preserves_typeof _ h₀ preq pes
        rw [h₇] at h₆
        rename_i h₈
        specialize h₁ x₂ h₈
        rw [← h₁]
        exact h₆
      . simp only [List.map₁, List.map_subtype, List.unattach_attach, bne_iff_ne, ne_eq, List.map_eq_nil_iff]
        simp only [bne_iff_ne, ne_eq] at h₂
        exact h₂
