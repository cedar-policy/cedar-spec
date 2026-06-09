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
import Cedar.Slice.ValidationPolicySlice
import Cedar.Thm.Data
import Cedar.Thm.Validation.ValidationPolicySlice.Environments

/-!
This file proves that `checkEntities` is preserved under schema changes: equality
when schemas agree on entity/action checks, monotonicity when checks are
forward-preserved, and preservation through `substituteAction`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.Slice

theorem checkEntities_eq {schema₁ schema₂ : Schema} (expr : Expr)
    (huid : ∀ uid : EntityUID,
      (schema₁.ets.isValidEntityUID uid || schema₁.acts.contains uid) =
      (schema₂.ets.isValidEntityUID uid || schema₂.acts.contains uid))
    (hety : ∀ ety : EntityType,
      (schema₁.ets.contains ety || schema₁.acts.actionType? ety) =
      (schema₂.ets.contains ety || schema₂.acts.actionType? ety)) :
    checkEntities schema₁ expr = checkEntities schema₂ expr := by
  match expr with
  | .lit (.entityUID uid) => simp [checkEntities, huid]
  | .lit (.bool _) | .lit (.int _) | .lit (.string _) | .var _ =>
    unfold checkEntities; rfl
  | .unaryApp (.is ety) e₁ =>
    unfold checkEntities; simp only [hety]
    split
    · exact checkEntities_eq e₁ huid hety
    · rfl
  | .unaryApp (.not) e₁ | .unaryApp (.neg) e₁ | .unaryApp (.like _) e₁ | .unaryApp (.isEmpty) e₁ =>
    unfold checkEntities; exact checkEntities_eq e₁ huid hety
  | .and e₁ e₂ | .or e₁ e₂ | .binaryApp _ e₁ e₂ =>
    unfold checkEntities
    rw [checkEntities_eq e₁ huid hety, checkEntities_eq e₂ huid hety]
  | .ite e₁ e₂ e₃ =>
    unfold checkEntities
    rw [checkEntities_eq e₁ huid hety, checkEntities_eq e₂ huid hety, checkEntities_eq e₃ huid hety]
  | .getAttr e₁ _ | .hasAttr e₁ _ =>
    unfold checkEntities; exact checkEntities_eq e₁ huid hety
  | .set xs =>
    simp only [checkEntities]
    congr 1
    ext ⟨x, hx⟩
    exact checkEntities_eq x huid hety
  | .record axs =>
    simp only [checkEntities]
    congr 1
    ext ⟨ax, hax⟩
    exact checkEntities_eq ax.snd huid hety
  | .call _ xs =>
    simp only [checkEntities]
    congr 1
    ext ⟨x, hx⟩
    exact checkEntities_eq x huid hety
  termination_by sizeOf expr

theorem checkEntities_monotone {schema₁ schema₂ : Schema} (expr : Expr)
    (huid : ∀ uid : EntityUID,
      (schema₁.ets.isValidEntityUID uid || schema₁.acts.contains uid) = true →
      (schema₂.ets.isValidEntityUID uid || schema₂.acts.contains uid) = true)
    (hety : ∀ ety : EntityType,
      (schema₁.ets.contains ety || schema₁.acts.actionType? ety) = true →
      (schema₂.ets.contains ety || schema₂.acts.actionType? ety) = true)
    (hok : checkEntities schema₁ expr = .ok ()) :
    checkEntities schema₂ expr = .ok () := by
  match expr with
  | .lit (.entityUID uid) =>
    simp only [checkEntities] at hok ⊢
    split at hok
    · rename_i hv; rw [show (schema₂.ets.isValidEntityUID uid || schema₂.acts.contains uid) = true from huid uid hv]; rfl
    · contradiction
  | .lit (.bool _) | .lit (.int _) | .lit (.string _) | .var _ =>
    unfold checkEntities; rfl
  | .unaryApp (.is ety) e₁ =>
    simp only [checkEntities] at hok ⊢
    split at hok
    · rename_i hv
      rw [show (schema₂.ets.contains ety || schema₂.acts.actionType? ety) = true from hety ety hv]
      exact checkEntities_monotone e₁ huid hety hok
    · contradiction
  | .unaryApp (.not) e₁ | .unaryApp (.neg) e₁ | .unaryApp (.like _) e₁ | .unaryApp (.isEmpty) e₁ =>
    unfold checkEntities at hok ⊢; exact checkEntities_monotone e₁ huid hety hok
  | .and e₁ e₂ | .or e₁ e₂ | .binaryApp _ e₁ e₂ =>
    unfold checkEntities at hok ⊢
    cases h₁ : checkEntities schema₁ e₁ with
    | error => simp [h₁] at hok
    | ok _ =>
      simp [h₁] at hok
      have h₁' := checkEntities_monotone e₁ huid hety (by exact h₁ ▸ rfl)
      simp [h₁']
      exact checkEntities_monotone e₂ huid hety hok
  | .ite e₁ e₂ e₃ =>
    unfold checkEntities at hok ⊢
    cases h₁ : checkEntities schema₁ e₁ with
    | error => simp [h₁] at hok
    | ok _ =>
      cases h₂ : checkEntities schema₁ e₂ with
      | error => simp [h₁, h₂] at hok
      | ok _ =>
        simp [h₁, h₂] at hok
        have h₁' := checkEntities_monotone e₁ huid hety (by exact h₁ ▸ rfl)
        have h₂' := checkEntities_monotone e₂ huid hety (by exact h₂ ▸ rfl)
        simp [h₁', h₂']
        exact checkEntities_monotone e₃ huid hety hok
  | .hasAttr e₁ _ | .getAttr e₁ _ =>
    unfold checkEntities at hok ⊢; exact checkEntities_monotone e₁ huid hety hok
  | .set xs =>
    simp only [checkEntities] at hok ⊢
    apply List.all_ok_implies_forM_ok
    intro ⟨x, hx⟩ hmem
    have hok_x := List.forM_ok_implies_all_ok' hok ⟨x, hx⟩ hmem
    exact checkEntities_monotone x huid hety hok_x
  | .record axs =>
    simp only [checkEntities] at hok ⊢
    apply List.all_ok_implies_forM_ok
    intro ⟨ax, hax⟩ hmem
    have hok_ax := List.forM_ok_implies_all_ok' hok ⟨ax, hax⟩ hmem
    exact checkEntities_monotone ax.snd huid hety hok_ax
  | .call _ xs =>
    simp only [checkEntities] at hok ⊢
    apply List.all_ok_implies_forM_ok
    intro ⟨x, hx⟩ hmem
    have hok_x := List.forM_ok_implies_all_ok' hok ⟨x, hx⟩ hmem
    exact checkEntities_monotone x huid hety hok_x
  termination_by sizeOf expr

theorem checkEntities_mapOnVars {schema : Schema} {f : Var → Expr} (expr : Expr)
    (hf : ∀ v, checkEntities schema (f v) = .ok ())
    (hce : checkEntities schema expr = .ok ()) :
    checkEntities schema (mapOnVars f expr) = .ok () := by
  match expr with
  | .lit _ => simp [mapOnVars, hce]
  | .var v => simp [mapOnVars, hf]
  | .unaryApp (.is ety) e₁ =>
    simp only [checkEntities] at hce
    split at hce
    · rename_i hv; simp only [mapOnVars, checkEntities, hv]; exact checkEntities_mapOnVars e₁ hf hce
    · contradiction
  | .unaryApp (.not) e₁ | .unaryApp (.neg) e₁ | .unaryApp (.like _) e₁ | .unaryApp (.isEmpty) e₁ =>
    unfold checkEntities at hce; simp only [mapOnVars]; unfold checkEntities
    exact checkEntities_mapOnVars e₁ hf hce
  | .and e₁ e₂ =>
    unfold checkEntities at hce
    cases h₁ : checkEntities schema e₁ <;> simp [h₁] at hce
    simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf (by rw [h₁]),
          checkEntities_mapOnVars e₂ hf hce]
  | .or e₁ e₂ =>
    unfold checkEntities at hce
    cases h₁ : checkEntities schema e₁ <;> simp [h₁] at hce
    simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf (by rw [h₁]),
          checkEntities_mapOnVars e₂ hf hce]
  | .binaryApp _ e₁ e₂ =>
    unfold checkEntities at hce
    cases h₁ : checkEntities schema e₁ <;> simp [h₁] at hce
    simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf (by rw [h₁]),
          checkEntities_mapOnVars e₂ hf hce]
  | .ite e₁ e₂ e₃ =>
    unfold checkEntities at hce
    cases h₁ : checkEntities schema e₁ <;> simp [h₁] at hce
    cases h₂ : checkEntities schema e₂ <;> simp [h₂] at hce
    simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf (by rw [h₁]),
          checkEntities_mapOnVars e₂ hf (by rw [h₂]),
          checkEntities_mapOnVars e₃ hf hce]
  | .hasAttr e₁ _ =>
    unfold checkEntities at hce; simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf hce]
  | .getAttr e₁ _ =>
    unfold checkEntities at hce; simp [mapOnVars, checkEntities, checkEntities_mapOnVars e₁ hf hce]
  | .set xs =>
    simp only [checkEntities] at hce
    simp only [mapOnVars, List.map₁, checkEntities]
    apply List.all_ok_implies_forM_ok
    intro ⟨y, hy⟩ hmem
    have hy_in_map : y ∈ xs.attach.map (fun ⟨x, _⟩ => mapOnVars f x) := hy
    rw [List.mem_map] at hy_in_map
    obtain ⟨⟨x, hx⟩, hmem_att, heq⟩ := hy_in_map
    have : checkEntities schema y = .ok () := by
      rw [← heq]
      exact checkEntities_mapOnVars x hf (List.forM_ok_implies_all_ok' hce ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩))
    exact this
  | .record axs =>
    simp only [checkEntities] at hce
    simp only [mapOnVars, List.map₂, checkEntities]
    apply List.all_ok_implies_forM_ok
    intro ⟨y, hy⟩ hmem
    -- y ∈ the mapped list. Get membership from hmem via attach₂ → mem_attach₂
    have hy_mem : y ∈ axs.attach₂.map (fun ⟨⟨a, x⟩, _⟩ => (a, mapOnVars f x)) :=
      List.mem_attach₂ hmem
    simp only [List.mem_map] at hy_mem
    obtain ⟨⟨ax, hax⟩, hmem_att, heq⟩ := hy_mem
    have heq_snd : y.snd = mapOnVars f ax.snd := by
      have := congrArg Prod.snd heq; simp at this; exact this.symm
    rw [heq_snd]
    exact checkEntities_mapOnVars ax.snd hf (List.forM_ok_implies_all_ok' hce ⟨ax, hax⟩ hmem_att)
  | .call _ xs =>
    simp only [checkEntities] at hce
    simp only [mapOnVars, List.map₁, checkEntities]
    apply List.all_ok_implies_forM_ok
    intro ⟨y, hy⟩ hmem
    have hy_in_map : y ∈ xs.attach.map (fun ⟨x, _⟩ => mapOnVars f x) := hy
    rw [List.mem_map] at hy_in_map
    obtain ⟨⟨x, hx⟩, hmem_att, heq⟩ := hy_in_map
    have : checkEntities schema y = .ok () := by
      rw [← heq]
      exact checkEntities_mapOnVars x hf (List.forM_ok_implies_all_ok' hce ⟨x, hx⟩ (List.mem_attach xs ⟨x, hx⟩))
    exact this
  termination_by sizeOf expr

theorem checkEntities_substituteAction {schema : Schema} {uid : EntityUID} {expr : Expr}
    (hce : checkEntities schema expr = .ok ())
    (hvalid : (schema.ets.isValidEntityUID uid || schema.acts.contains uid) = true) :
    checkEntities schema (substituteAction uid expr) = .ok () := by
  simp only [substituteAction]
  exact checkEntities_mapOnVars expr (fun v => by cases v <;> simp [checkEntities, hvalid]) hce

end Cedar.Thm
