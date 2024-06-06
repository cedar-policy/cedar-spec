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

theorem if_wellformed_then_exists_make [LT α] [DecidableLT α] (s : Set α) :
  WellFormed s → ∃ list, s = Set.make list
:= by
  intro h₁
  exists s.elts

theorem wf_iff_sorted {α} [LT α] [DecidableLT α] [StrictLT α]  (s : Set α) :
  s.WellFormed ↔ s.elts.Sorted
:= by
  simp only [WellFormed, make, toList, elts]
  have hid : (fun x => x) = @id α := by
    apply funext ; simp only [id_eq, implies_true]
  rw [hid]
  constructor <;>
  intro h
  case mp =>
    rw [h]
    simp only [List.Sorted, List.canonicalize_sortedBy id s.1]
  case mpr =>
    rw [← (List.sortedBy_implies_canonicalize_eq h),
      List.canonicalize_idempotent, List.sortedBy_implies_canonicalize_eq h]

/-! ### contains and mem -/

theorem contains_prop_bool_equiv [DecidableEq α] {v : α} {s : Set α} :
  s.contains v = true ↔ v ∈ s
:= by
  constructor <;> intro h
  · exact List.mem_of_elem_eq_true h
  · exact List.elem_eq_true_of_mem h

theorem in_list_iff_in_set {α : Type u} (v : α) (s : Set α) :
  v ∈ s.elts ↔ v ∈ s
:= by
  constructor
  case mp => intro h ; apply h
  case mpr => simp [elts, Membership.mem]

theorem in_list_iff_in_mk {α : Type u} (v : α) (xs : List α) :
  v ∈ xs ↔ v ∈ mk xs
:= by
  constructor
  case mp => intro h ; apply h
  case mpr => simp [elts, Membership.mem]

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

theorem mem_cons {a : α} {hd : α} {tl : List α} :
  a ∈ Set.mk (hd :: tl) → a = hd ∨ a ∈ tl
:= by
  simp [← in_list_iff_in_mk]

theorem in_set_means_list_non_empty {α : Type u} (v : α) (s : Set α) :
  v ∈ s.elts → ¬(s.elts = [])
:= by
  intros h0 h1
  rw [List.eq_nil_iff_forall_not_mem] at h1
  specialize h1 v
  contradiction

/-! ### empty -/

theorem empty_eq_mk_empty {α} :
  (Set.empty : Set α) = Set.mk []
:= by simp only [empty]

theorem empty_no_elts {α : Type u} (v : α) :
  ¬ v ∈ Set.empty
:= by
  intro h
  simp only [Membership.mem, Set.elts, Set.empty] at h
  have _ := List.ne_nil_of_mem h
  contradiction

theorem empty_wf {α : Type u} [LT α] [DecidableLT α] :
  Set.WellFormed (Set.empty : Set α)
:= by
  unfold WellFormed toList empty make List.canonicalize
  rfl

/-! ### isEmpty -/

theorem make_empty [DecidableEq α] [LT α] [DecidableLT α] (xs : List α) :
  xs = [] ↔ (Set.make xs).isEmpty
:= by
  unfold isEmpty; unfold empty; unfold make
  constructor
  case mp =>
    intro h₁ ; subst h₁
    simp only [beq_iff_eq, mk.injEq]
    apply List.canonicalize_nil
  case mpr =>
    intro h₁ ; simp only [beq_iff_eq, mk.injEq] at h₁
    apply (List.canonicalize_nil' id xs).mpr
    assumption

theorem make_non_empty [DecidableEq α] [LT α] [DecidableLT α] (xs : List α) :
  xs ≠ [] ↔ (Set.make xs).isEmpty = false
:= by
  unfold isEmpty; unfold empty; unfold make
  simp only [beq_eq_false_iff_ne, ne_eq, mk.injEq]
  apply List.canonicalize_not_nil

theorem non_empty_iff_exists [DecidableEq α] (s : Set α) :
  ¬ s.isEmpty ↔ ∃ a, a ∈ s
:= by
  simp only [isEmpty, empty, beq_iff_eq]
  constructor
  case mp =>
    intro h₁
    apply List.exists_mem_of_ne_nil s.elts
    intro h₂
    apply h₁ ; clear h₁
    cases s
    simp only [elts, mk.injEq] at *
    assumption
  case mpr =>
    intro h₁
    replace ⟨a, h₁⟩ := h₁
    intro h₂
    rw [← in_list_iff_in_set] at h₁
    cases s
    simp only [mk.injEq] at h₂
    subst h₂
    simp [elts] at h₁

theorem empty_iff_not_exists [DecidableEq α] (s : Set α) :
  s.isEmpty ↔ ¬ ∃ a, a ∈ s
:= by
  simp only [isEmpty, empty, beq_iff_eq, not_exists]
  constructor
  case mp =>
    intro h₁
    subst h₁
    apply List.not_mem_nil
  case mpr =>
    intro h₁
    match s with
    | mk xs =>
      rw [mk.injEq]
      rw [List.eq_nil_iff_forall_not_mem]
      intro x
      specialize h₁ x
      rw [in_list_iff_in_mk]
      assumption

/-! ### make -/

theorem make_wf [LT α] [DecidableLT α] [StrictLT α] (xs : List α) :
  WellFormed (Set.make xs)
:= by
  simp only [WellFormed, make, toList, elts, List.canonicalize_idempotent]

theorem make_sorted {α} [LT α] [DecidableLT α] [StrictLT α] {xs : List α} :
  xs.Sorted → Set.make xs = Set.mk xs
:= by
  intro h
  have hid : (fun x => x) = @id α := by
    apply funext ; simp only [id_eq, implies_true]
  simp only [make, hid, List.sortedBy_implies_canonicalize_eq h]

theorem make_mem [LT α] [DecidableLT α] [StrictLT α] (x : α) (xs : List α) :
  x ∈ xs ↔ x ∈ Set.make xs
:= by
  simp only [make, Membership.mem]
  have h₁ := List.canonicalize_equiv xs
  simp only [List.Equiv, List.subset_def] at h₁
  have ⟨h₁, h₂⟩ := h₁
  constructor <;> intro h₃
  case mp => exact h₁ h₃
  case mpr => exact h₂ h₃

theorem make_mk_eqv [LT α] [DecidableLT α] [StrictLT α] {xs ys : List α} :
  Set.make xs = Set.mk ys → xs ≡ ys
:= by
  simp only [make, mk.injEq] ; intro h₁
  have h₂ := List.canonicalize_equiv xs
  subst h₁
  exact h₂

theorem make_make_eqv [LT α] [DecidableLT α] [StrictLT α] {xs ys : List α} :
  Set.make xs = Set.make ys ↔ xs ≡ ys
:= by
  constructor <;> intro h
  case mp =>
    simp only [make, mk.injEq] at h
    have h₁ := List.canonicalize_equiv xs
    have h₂ := List.canonicalize_equiv ys
    unfold id at h₁ h₂
    rw [← h] at h₂
    have h₃ := List.Equiv.symm h₂; clear h₂
    exact List.Equiv.trans (a := xs) (b := List.canonicalize (fun x => x) xs) (c := ys) h₁ h₃
  case mpr =>
    simp only [make, mk.injEq]
    apply List.equiv_implies_canonical_eq _ _ h

theorem elts_make_equiv [LT α] [DecidableLT α] [StrictLT α] {xs : List α} :
  Set.elts (Set.make xs) ≡ xs
:= by
  simp only [List.Equiv, List.subset_def]
  constructor <;> intro a h₁
  · rw [make_mem, ← in_list_iff_in_set]
    exact h₁
  · rw [in_list_iff_in_set, ← make_mem]
    exact h₁

theorem elts_make_nil [LT α] [DecidableLT α] [StrictLT α] :
  Set.elts (Set.make ([] : List α)) = []
:= by
  simp [make, elts, List.canonicalize_nil]

def eq_means_eqv [LT α] [DecidableLT α] [StrictLT α] {s₁ s₂ : Set α} :
  WellFormed s₁ → WellFormed s₂ →
  (s₁.elts ≡ s₂.elts ↔ s₁ = s₂)
:= by
  intro h₁ h₂
  constructor
  case mp =>
    intro h₃
    have ⟨elts₁, h₄⟩ := if_wellformed_then_exists_make s₁ h₁ ; clear h₁
    subst h₄
    have ⟨elts₂, h₄⟩ := if_wellformed_then_exists_make s₂ h₂ ; clear h₂
    subst h₄
    rw [make_make_eqv]
    apply List.Equiv.trans (List.Equiv.symm (elts_make_equiv (xs := elts₁)))
    apply List.Equiv.trans h₃ (elts_make_equiv)
  case mpr =>
    intro h₃
    subst h₃
    apply List.Equiv.refl

theorem make_any_iff_any [LT α] [DecidableLT α] [StrictLT α] (f : α → Bool) (xs : List α) :
  (Set.make xs).any f = xs.any f
:= by
  simp only [make, any]
  have h₁ := List.canonicalize_equiv xs
  simp only [List.Equiv, List.subset_def] at h₁
  have ⟨hl₁, hr₁⟩ := h₁
  cases h₃ : List.any xs f
  case false =>
    by_contra h₄
    simp only [Bool.not_eq_false, List.any_eq_true] at h₄
    have ⟨x, h₄, h₅⟩ := h₄
    specialize hr₁ h₄
    simp [List.any_of_mem hr₁ h₅] at h₃
  case true =>
    simp only [List.any_eq_true] at *
    have ⟨x, h₃, h₄⟩ := h₃
    exists x
    simp only [h₄, and_true]
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

/--
  Note that the converse of this is not true:
  counterexample `xs = [1]`, `ys = []`, `a = 1`.
-/
theorem make_cons [LT α] [DecidableLT α] {xs ys : List α} {a : α} :
  make xs = make ys → make (a :: xs) = make (a :: ys)
:= by
  simp only [make, mk.injEq]
  apply List.canonicalize_cons

/-! ### inter and union -/

theorem inter_def {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {s₁ s₂ : Set α} :
  s₁ ∩ s₂ = s₁.intersect s₂
:= by simp only [Inter.inter]

open BEq LawfulBEq in
theorem mem_inter_iff {α} [DecidableEq α] {x : α} {s₁ s₂ : Set α} :
  x ∈ s₁ ∩ s₂ ↔ x ∈ s₁ ∧ x ∈ s₂
:= by
  simp only [Membership.mem, intersect]
  have h := @List.mem_inter_iff α _ _ x (elts s₁) (elts s₂)
  simp only [Membership.mem, Inter.inter] at h
  exact h

theorem inter_wf {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {s₁ s₂ : Set α}
 (h₁ : WellFormed s₁) :
 WellFormed (s₁ ∩ s₂)
:= by
  unfold WellFormed
  simp only [Inter.inter, intersect]
  simp only [make, toList, elts, mk.injEq] at *
  simp only [List.inter]
  rename_i iLT iSLT iDecLT iDecEq
  have h₃ := @List.canonicalize_id_filter α iLT iSLT iDecLT (fun x => decide (x ∈ s₂.1)) s₁.1
  rw (config := {occs := .pos [1]}) [h₁]
  simp only [List.elem_eq_mem]
  exact h₃

theorem inter_empty_left {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (s : Set α) :
 Set.empty ∩ s = Set.empty
:= by
  cases s ; rename_i xs
  simp only [Inter.inter, intersect, List.inter, elts, List.elem_eq_mem, empty, List.filter_nil]

theorem inter_empty_right {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (s : Set α) :
 s ∩ Set.empty = Set.empty
:= by
  cases s ; rename_i xs
  simp only [Inter.inter, intersect, List.inter, elts, empty, List.elem_eq_mem, List.not_mem_nil,
    decide_False, mk.injEq, List.filter_eq_nil, not_false_eq_true, implies_true]

theorem inter_self_eq {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (s : Set α) :
 s ∩ s = s
:= by
  simp only [Inter.inter, intersect, List.inter, elts, List.elem_eq_mem]
  cases s ; rename_i xs
  simp only [mk.injEq]
  induction xs
  case nil =>
    simp only [List.not_mem_nil, decide_False, List.filter_nil]
  case cons hd tl ih =>
    simp only [List.mem_cons, true_or, decide_True, List.filter_cons_of_pos, List.cons.injEq, true_and]
    rw [eq_comm]
    rw (config := {occs := .pos [1]}) [← ih]
    rw [List.filter_congr']
    simp only [decide_eq_true_eq]
    intro _ h
    simp only [h, or_true]

theorem intersects_def {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {s₁ s₂ : Set α} :
 s₁.intersects s₂ = ¬ (s₁ ∩ s₂).isEmpty
:= by
  simp only [Bool.not_eq_true, eq_iff_iff]
  simp only [intersects, List.any_eq_true, in_list_iff_in_set, contains_prop_bool_equiv]
  constructor
  case mp =>
    intro h
    replace ⟨x, h⟩ := h
    by_contra hc
    simp only [ne_eq, Bool.not_eq_false] at hc
    simp only [empty_iff_not_exists, not_exists] at hc
    specialize hc x
    have _ := mem_inter_iff.mpr h
    contradiction
  case mpr =>
    intro h
    replace h : ¬ isEmpty (s₁ ∩ s₂) = true := by
      simp only [h, not_false_eq_true]
    rw [non_empty_iff_exists] at h
    replace ⟨x, h⟩ := h
    rw [mem_inter_iff] at h
    exists x

theorem intersects_iff_exists {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {s₁ s₂ : Set α} :
 s₁.intersects s₂ ↔ ∃ a, a ∈ s₁ ∧ a ∈ s₂
:= by
  constructor <;> intro h
  case mp =>
    simp only [Set.intersects_def, Set.non_empty_iff_exists, Set.mem_inter_iff] at h
    exact h
  case mpr =>
    replace ⟨a, h⟩ := h
    rw [← Set.mem_inter_iff] at h
    simp only [Set.intersects_def, Set.non_empty_iff_exists]
    exists a

theorem union_wf [LT α] [DecidableLT α] [StrictLT α] (s₁ s₂ : Set α) :
  WellFormed (s₁ ∪ s₂)
:= by
  unfold WellFormed
  simp only [Union.union, union, toList]
  rw [make_make_eqv]
  apply List.Equiv.symm
  exact elts_make_equiv

/-! ### subset -/

theorem elts_subset_then_subset [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {xs ys : List α} :
  xs ⊆ ys → Set.make xs ⊆ Set.make ys
:= by
  simp only [Subset, List.Subset, subset, List.all_eq_true]
  intro h₁ x h₂
  rw [contains_prop_bool_equiv]
  rw [in_list_iff_in_set] at h₂
  rw [← make_mem] at *
  apply h₁ h₂

/--
  Like `List.subset_def`, but lifted to Sets
-/
theorem subset_def [DecidableEq α] {s₁ s₂ : Set α} :
  s₁ ⊆ s₂ ↔ ∀ a, a ∈ s₁ → a ∈ s₂
:= by
  simp only [Subset, List.Subset, subset, List.all_eq_true]
  constructor <;> intro h₁ a h₂ <;> specialize h₁ a
  case mp =>
    rw [in_list_iff_in_set] at h₁
    rw [contains_prop_bool_equiv] at h₁
    exact h₁ h₂
  case mpr =>
    rw [in_list_iff_in_set] at h₂
    rw [contains_prop_bool_equiv]
    exact h₁ h₂

theorem superset_empty_subset_empty [DecidableEq α] {s₁ s₂ : Set α} :
  s₁ ⊆ s₂ → s₂.isEmpty → s₁.isEmpty
:= by
  repeat rw [Set.empty_iff_not_exists]
  intro h₁ h₂ h₃
  rw [subset_def] at h₁
  replace ⟨a, h₃⟩ := h₃
  apply h₂
  exists a
  exact h₁ a h₃

theorem subset_iff_subset_elts [DecidableEq α] {s₁ s₂ : Set α} :
  s₁ ⊆ s₂ ↔ s₁.elts ⊆ s₂.elts
:= by
  simp only [subset_def, elts, List.subset_def, in_list_iff_in_set]

theorem subset_iff_eq [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {s₁ s₂ : Set α} :
  WellFormed s₁ → WellFormed s₂ →
  ((s₁ ⊆ s₂ ∧ s₂ ⊆ s₁) ↔ s₁ = s₂)
:= by
  intro hw₁ hw₂
  simp only [← (eq_means_eqv hw₁ hw₂), elts, List.Equiv, subset_iff_subset_elts]

end Cedar.Data.Set
