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

theorem partial_eval_well_typed_record {env : TypeEnv} {ls : List (Attr × Residual)} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  (∀ k v, (k, v) ∈ ls → Residual.WellTyped env (TPE.evaluate v preq pes)) →
  PEWellTyped env (Residual.record ls ty) (TPE.evaluate (Residual.record ls ty) preq pes) req preq es pes
:= by
  intros h_ls_wt h_wf h_ref h_wt
  cases h_wt
  rename_i ty₁ h₀ h₁
  simp only [TPE.evaluate]
  unfold List.map₁ List.attach List.attachWith
  rw [List.map_pmap_subtype (fun x => (x.fst, TPE.evaluate x.snd preq pes)) ls]
  simp only [record, List.mapM_map, List.any_map, List.any_eq_true, Function.comp_apply, Prod.exists]
  let m := Map.mk ls
  split
  . rename_i x xs h₃
    apply Residual.WellTyped.val
    apply InstanceOfType.instance_of_record
    . intro k h₄
      rw [Map.contains_iff_some_find?] at h₄
      rcases h₄ with ⟨v, h₄⟩

      rw [← Map.list_find?_iff_make_find?] at h₄
      rw [Map.contains_iff_some_find?]
      unfold Function.comp at h₃
      simp [bindAttr] at h₃

      have h₈ := Map.list_find?_mapM_implies_exists_unmapped (λ x => (TPE.evaluate x preq pes).asValue) h₃ h₄
      rcases h₈ with ⟨v₂, h₈, h₉⟩
      simp at h₈

      rw [Map.list_find?_some_iff_map_find?_some] at h₉
      replace h₉ := Map.find?_mapOnValues_some (λ x => Qualified.required x.typeOf) h₉

      subst ty₁
      simp only [Map.mapOnValues] at h₉
      exists (Qualified.required v₂.typeOf)
      rw [← Map.list_find?_iff_make_find?]
      rw [← Map.list_find?_iff_mk_find?] at h₉
      exact h₉
    . intro k v qty h₄ h₅
      rw [h₁] at h₅
      have h₆ := h₄
      rw [← Map.list_find?_iff_make_find?] at h₆
      have h₇ := h₅
      rw [← Map.list_find?_iff_make_find?] at h₇
      unfold Function.comp at h₃
      simp only [bindAttr, Option.pure_def, Option.bind_eq_bind] at h₃
      have h₈ := Map.list_find?_mapM_implies_exists_unmapped (λ x => (TPE.evaluate x preq pes).asValue) h₃ h₆
      rcases h₈ with ⟨v₂, _, h₈⟩


      have h₇_new : ((Map.mk ls).mapOnValues (λ x => Qualified.required x.typeOf)).find? k = some qty := by
        unfold Map.mapOnValues
        simp only [Map.find?, Map.toList_mk_id]
        rw [h₇]

      have h₉_new := Map.find?_mapOnValues_some' (fun x: Residual => Qualified.required x.typeOf) h₇_new
      rcases h₉_new with ⟨v₃, h₁₀, h₉⟩
      rw [h₉]
      have h₁₁ := h₀
      have h₁₂ := List.mem_of_find?_eq_some h₈
      specialize h₁₁ k v₂ h₁₂
      rw [← Map.list_find?_iff_mk_find?] at h₁₀
      rw [h₁₀] at h₈
      injection h₈
      rename_i h₁₃
      simp only [Prod.mk.injEq, true_and] at h₁₃
      rw [h₁₃]
      rename_i h₁₄
      simp only [Residual.asValue] at h₁₄
      split at h₁₄
      case h_2 => contradiction
      rename_i v₄ ty h₁₅
      injection h₁₄; rename_i h₁₅
      simp only [Qualified.getType]
      rename_i h₁₆
      have h₁₇ := partial_eval_preserves_typeof _ h₁₁ preq pes
      rw [h₁₆] at h₁₇
      rw [←h₁₇]
      simp only [Residual.typeOf]
      let ih := h_ls_wt k v₂ h₁₂
      rw [h₁₆] at ih
      cases ih
      rw [← h₁₅]
      assumption
    . intro k qty h₄ h₅
      subst ty₁
      replace h₄ : ((Map.mk ls).mapOnValues (λ x => Qualified.required x.typeOf)).find? k = some qty := by
        unfold Map.mapOnValues
        simp only [Map.find?, Map.toList_mk_id]
        rw [← Map.list_find?_iff_make_find?] at h₄
        rw [h₄]
      have h₅ := Map.find?_mapOnValues_some' (α := Attr) (fun x: Residual => Qualified.required x.typeOf) h₄

      rcases h₅ with ⟨v₂, h₅, _⟩
      rw [← Map.list_find?_iff_mk_find?] at h₅

      unfold Function.comp at h₃
      simp only [bindAttr, Option.pure_def, Option.bind_eq_bind] at h₃
      have h₆ := Map.list_find?_mapM_implies_exists_mapped (λ x => (TPE.evaluate x preq pes).asValue) h₃ h₅

      rw [Map.contains_iff_some_find?]
      rcases h₆ with ⟨v₃, _, h₆⟩
      exists v₃
      rw [← Map.list_find?_iff_make_find?]
      exact h₆
  case h_2 x h₂ =>
    split
    . apply Residual.WellTyped.error
    case isFalse h₃ =>
      apply Residual.WellTyped.record
      . intros k v h₄
        have h₅ := List.mem_of_map_implies_exists_unmapped h₄
        rcases h₅ with ⟨p, h₅, h₆⟩
        cases p ; rename_i k₂ v₂
        simp only [Prod.mk.injEq] at h₆
        rcases h₆ with ⟨h₆, h₇⟩
        rw [← h₆] at h₅
        specialize h₀ k v₂ h₅
        have ih := h_ls_wt k v₂ h₅
        rw [h₇]
        assumption
      . rw [h₁]
        simp only [List.map_map]
        unfold Function.comp
        simp only
        congr 1
        apply List.map_congr
        intro x h₄
        congr 2

        cases x
        rename_i k v
        specialize h₀ k v h₄
        simp only
        let h₅ := partial_eval_preserves_typeof _ h₀
        rw [h₅]
