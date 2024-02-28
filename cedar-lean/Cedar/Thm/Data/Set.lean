/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Data.Set
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List

/-!
# Set properties

This file proves useful properties of canonical list-based sets defined in
`Cedar.Data.Set`.
-/

namespace Cedar.Data.Set

/-! ### Well-formed sets -/

def WellFormed {α} [LT α] [DecidableLT α] (s : Set α) :=
  s = Set.make s.toList

/-! ### contains and mem -/

theorem contains_prop_bool_equiv [DecidableEq α] {v : α} {s : Set α} :
  s.contains v = true ↔ v ∈ s
:= by
  apply Iff.intro
  intro h0
  apply List.mem_of_elem_eq_true
  assumption
  intro h0
  apply List.elem_eq_true_of_mem
  assumption

theorem in_list_in_set {α : Type u} (v : α) (s : Set α) :
  v ∈ s.elts → v ∈ s
:= by
  intro h0
  apply h0

theorem in_set_in_list {α : Type u} (v : α) (s : Set α) :
  v ∈ s → v ∈ s.elts
:= by
  simp [Membership.mem]

theorem mem_cons_self {α : Type u} (hd : α) (tl : List α) :
  hd ∈ Set.mk (hd :: tl)
:= by
  simp only [Membership.mem]
  apply List.mem_cons_self hd tl

theorem mem_cons_of_mem {α : Type u} (a : α) (hd : α) (tl : List α) :
  a ∈ Set.mk tl → a ∈ Set.mk (hd :: tl)
:= by
  simp only [Membership.mem] ; intro h₁
  apply List.mem_cons_of_mem hd h₁

theorem in_set_means_list_non_empty {α : Type u} (v : α) (s : Set α) :
  v ∈ s.elts → ¬(s.elts = [])
:= by
  intros h0 h1
  rw [List.eq_nil_iff_forall_not_mem] at h1
  specialize h1 v
  contradiction

/-! ### isEmpty -/

theorem make_non_empty [DecidableEq α] [LT α] [DecidableLT α] (xs : List α) :
  xs ≠ [] ↔ (Set.make xs).isEmpty = false
:= by
  unfold isEmpty; unfold empty; unfold make
  simp only [beq_eq_false_iff_ne, ne_eq, mk.injEq]
  apply List.canonicalize_not_nil

/-! ### make -/

theorem make_mem [LT α] [DecidableLT α] [StrictLT α] (x : α) (xs : List α) :
  x ∈ xs ↔ x ∈ Set.make xs
:= by
  simp only [Membership.mem, make]
  have h₁ := List.canonicalize_equiv xs
  simp [List.Equiv, List.subset_def] at h₁
  have ⟨h₁, h₂⟩ := h₁
  constructor <;> intro h₃
  case mp => apply h₁ h₃
  case mpr => apply h₂ h₃

theorem make_mk_eqv [LT α] [DecidableLT α] [StrictLT α] {xs ys : List α} :
  Set.make xs = Set.mk ys → xs ≡ ys
:= by
  simp [make] ; intro h₁
  have h₂ := List.canonicalize_equiv xs
  subst h₁
  exact h₂

theorem make_make_eqv [LT α] [DecidableLT α] [StrictLT α] {xs ys : List α} :
  Set.make xs = Set.make ys ↔ xs ≡ ys
:= by
  constructor
  case mp =>
    intro h; unfold make at h; simp at h
    have h₁ := List.canonicalize_equiv xs
    have h₂ := List.canonicalize_equiv ys
    unfold id at h₁ h₂
    rw [← h] at h₂
    have h₃ := List.Equiv.symm h₂; clear h₂
    exact List.Equiv.trans (a := xs) (b := List.canonicalize (fun x => x) xs) (c := ys) h₁ h₃
  case mpr =>
    intro h; unfold make; simp only [mk.injEq]
    apply List.equiv_implies_canonical_eq _ _ h

theorem elts_make_equiv [LT α] [DecidableLT α] [StrictLT α] {xs : List α} :
  Set.elts (Set.make xs) ≡ xs
:= by
  simp [List.Equiv, List.subset_def]
  constructor
  case left =>
    intro a h₁
    rw [make_mem]
    exact in_list_in_set a (make xs) h₁
  case right =>
    intro a h₁
    apply in_set_in_list
    rw [← make_mem]
    exact h₁

theorem in_set_in_list' [LT α] [DecidableLT α] [StrictLT α] (v : α) (xs : List α) :
  v ∈ (Set.make xs) → v ∈ xs
:= by
  rw [make_mem]
  simp

theorem make_any_iff_any [LT α] [DecidableLT α] [StrictLT α] (f : α → Bool) (xs : List α) :
  (Set.make xs).any f = xs.any f
:= by
  simp [make, any]
  have h₁ := List.canonicalize_equiv xs
  simp [List.Equiv, List.subset_def] at h₁
  have ⟨hl₁, hr₁⟩ := h₁
  cases h₃ : List.any xs f
  case false =>
    by_contra h₄
    simp only [Bool.not_eq_false, List.any_eq_true] at h₄
    have ⟨x, h₄, h₅⟩ := h₄
    specialize hr₁ h₄
    simp [List.any_of_mem hr₁ h₅] at h₃
  case true =>
    simp [List.any_eq_true] at *
    have ⟨x, h₃, h₄⟩ := h₃
    exists x ; simp [h₄]
    apply hl₁ h₃

theorem make_of_make_is_id [LT α] [DecidableLT α] [StrictLT α] (xs : List α) :
  Set.make (Set.elts (Set.make xs)) = Set.make xs
:= by
  simp only [make, mk.injEq]
  have h₁ := List.canonicalize_idempotent id xs
  unfold id at h₁
  exact h₁

theorem elts_make_is_id_then_equiv [LT α] [DecidableLT α] [StrictLT α] {xs ys : List α} :
  Set.elts (Set.make xs) = ys → ys ≡ xs
:= by
  intro h
  rw [← h]; clear h
  rw [← make_make_eqv]
  exact make_of_make_is_id xs

/-! ### inter -/

theorem mem_inter_iff {α} [DecidableEq α] {x : α} {s₁ s₂ : Set α} :
  x ∈ s₁ ∩ s₂ ↔ x ∈ s₁ ∧ x ∈ s₂
:= by
  simp only [Membership.mem, intersect]
  rename_i iDecEq
  have h := @List.mem_inter_iff α iDecEq x s₁.1 s₂.1
  simp only [Membership.mem, Inter.inter] at h
  exact h

theorem inter_wf {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {s₁ s₂ : Set α}
 (h₁ : WellFormed s₁) :
 WellFormed (s₁ ∩ s₂)
:= by
  simp only [WellFormed] at *
  simp only [Inter.inter, intersect]
  simp only [make, toList, elts, mk.injEq] at *
  simp only [List.inter]
  rename_i iLT iSLT iDecLT iDecEq
  have h₃ := @List.canonicalize_id_filter α iLT iSLT iDecLT (fun x => decide (x ∈ s₂.1)) s₁.1
  rw (config := {occs := .pos [1]}) [h₁]
  simp only
  apply h₃

end Cedar.Data.Set
