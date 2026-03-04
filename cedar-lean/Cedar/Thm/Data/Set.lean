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

module

public import Cedar.Data.Set
import all Cedar.Data.Set -- inside this module, we're allowed to unfold defs in Cedar.Data.Set that are not normally exposed
import Cedar.Thm.Data.Control
public import Cedar.Thm.Data.List
public import Cedar.Data.LT

/-!
# Set properties

This file proves useful properties of canonical list-based sets defined in
`Cedar.Data.Set`.
-/

namespace Cedar.Data.Set

/-! ### Well-formed sets -/

public def WellFormed {α} [LT α] [DecidableLT α] (s : Set α) :=
  s = Set.make s.toList

public theorem if_wellformed_then_exists_make [LT α] [DecidableLT α] (s : Set α) :
  WellFormed s → ∃ list, s = Set.make list
:= by
  intro h₁
  exists s.elts

public theorem wf_iff_sorted {α} [LT α] [DecidableLT α] [StrictLT α]  (s : Set α) :
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

public theorem contains_prop_bool_equiv [DecidableEq α] {v : α} {s : Set α} :
  s.contains v = true ↔ v ∈ s
:= by
  constructor <;> intro h
  · exact List.mem_of_elem_eq_true h
  · exact List.elem_eq_true_of_mem h

public theorem not_contains_prop_bool_equiv [DecidableEq α] {v : α} {s : Set α} :
  s.contains v = false ↔ v ∉ s
:= by
  rw [← Bool.not_eq_true, contains_prop_bool_equiv]

public theorem in_list_iff_in_set {α : Type u} (v : α) (s : Set α) :
  v ∈ s.elts ↔ v ∈ s
:= by
  constructor
  case mp => intro h ; apply h
  case mpr => simp [elts, Membership.mem]

public theorem in_list_iff_in_mk {α : Type u} (v : α) (xs : List α) :
  v ∈ xs ↔ v ∈ mk xs
:= by
  constructor
  case mp => intro h ; apply h
  case mpr => simp [elts, Membership.mem]

public theorem mem_cons_self {α : Type u} (hd : α) (tl : List α) :
  hd ∈ Set.mk (hd :: tl)
:= by
  simp only [Membership.mem, elts]
  exact List.mem_cons_self

public theorem mem_cons_of_mem {α : Type u} (a : α) (hd : α) (tl : List α) :
  a ∈ Set.mk tl → a ∈ Set.mk (hd :: tl)
:= by
  simp only [Membership.mem] ; intro h₁
  apply List.mem_cons_of_mem hd h₁

public theorem mem_cons {a : α} {hd : α} {tl : List α} :
  a ∈ Set.mk (hd :: tl) ↔ a = hd ∨ a ∈ tl
:= by
  simp [← in_list_iff_in_mk]

/-! ### empty -/

public theorem empty_eq_mk_empty {α} :
  (Set.empty : Set α) = Set.mk []
:= by simp only [empty]

public theorem empty_no_elts {α : Type u} (v : α) :
  ¬ v ∈ Set.empty
:= by
  intro h
  simp only [Membership.mem, Set.elts, Set.empty] at h
  have _ := List.ne_nil_of_mem h
  contradiction

public theorem empty_wf {α : Type u} [LT α] [DecidableLT α] :
  Set.WellFormed (Set.empty : Set α)
:= by
  simp [WellFormed, toList, empty, make, elts]
  apply List.canonicalize_nil

public theorem map_empty [LT β] [DecidableLT β] (f : α → β) :
  Set.empty.map f = Set.empty
:= by
  simp [Set.map, empty_eq_mk_empty, Set.elts, Set.make, List.canonicalize_nil]


/-! ### isEmpty -/

public theorem make_empty [DecidableEq α] [LT α] [DecidableLT α] (xs : List α) :
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

public theorem make_non_empty [DecidableEq α] [LT α] [DecidableLT α] (xs : List α) :
  xs ≠ [] ↔ (Set.make xs).isEmpty = false
:= by
  unfold isEmpty; unfold empty; unfold make
  simp only [beq_eq_false_iff_ne, ne_eq, mk.injEq]
  apply List.canonicalize_not_nil

public theorem non_empty_iff_exists [DecidableEq α] (s : Set α) :
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

public theorem empty_iff_not_exists [DecidableEq α] (s : Set α) :
  s.isEmpty ↔ ¬ ∃ a, a ∈ s
:= by
  simp only [isEmpty, empty, beq_iff_eq, not_exists]
  constructor
  case mp =>
    intro h₁ ; subst h₁ ; exact λ _ => List.not_mem_nil
  case mpr =>
    intro h₁
    cases s with | mk xs =>
    simp only [mk.injEq, List.eq_nil_iff_forall_not_mem]
    intro x ; rw [in_list_iff_in_mk] ; exact h₁ x


/-! ### singleton -/

public theorem singleton_wf [DecidableEq α] [LT α] [DecidableLT α] (a : α) :
  WellFormed (Set.singleton a)
:= by
  simp [singleton, WellFormed, make, toList, elts]
  rw [List.canonicalize_singleton]

public theorem mem_singleton_iff_eq [DecidableEq α] (a b : α) :
  a ∈ Set.singleton b ↔ a = b
:= by
  simp only [singleton, ← in_list_iff_in_mk, List.mem_singleton]

public theorem mem_singleton [DecidableEq α] (a : α) :
  a ∈ Set.singleton a
:= by simp only [mem_singleton_iff_eq]

/-! ### make -/

public theorem make_wf [LT α] [DecidableLT α] [StrictLT α] (xs : List α) :
  WellFormed (Set.make xs)
:= by
  simp only [WellFormed, make, toList, elts, List.canonicalize_idempotent]

public theorem make_sorted {α} [LT α] [DecidableLT α] [StrictLT α] {xs : List α} :
  xs.Sorted → Set.make xs = Set.mk xs
:= by
  intro h
  have hid : (fun x => x) = @id α := by
    apply funext ; simp only [id_eq, implies_true]
  simp only [make, hid, List.sortedBy_implies_canonicalize_eq h]

public theorem make_mem [LT α] [DecidableLT α] [StrictLT α] (x : α) (xs : List α) :
  x ∈ xs ↔ x ∈ Set.make xs
:= by
  simp only [make, Membership.mem]
  have h := List.canonicalize_equiv xs
  simp only [List.Equiv, List.subset_def] at h
  exact ⟨h.left, h.right⟩

public theorem make_mk_eqv [LT α] [DecidableLT α] [StrictLT α] {xs ys : List α} :
  Set.make xs = Set.mk ys → xs ≡ ys
:= by
  simp only [make, mk.injEq] ; intro h₁
  have h₂ := List.canonicalize_equiv xs
  subst h₁
  exact h₂

public theorem make_make_eqv [LT α] [DecidableLT α] [StrictLT α] {xs ys : List α} :
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

public theorem elts_make_equiv [LT α] [DecidableLT α] [StrictLT α] {xs : List α} :
  Set.elts (Set.make xs) ≡ xs
:= by
  simp only [List.Equiv, List.subset_def]
  constructor <;> intro a h₁
  · rw [make_mem, ← in_list_iff_in_set]
    exact h₁
  · rw [in_list_iff_in_set, ← make_mem]
    exact h₁

public theorem make_nil [LT α] [DecidableLT α] [StrictLT α] :
  Set.make [] (α := α) = Set.empty
:= by
  simp [make, List.canonicalize_nil, empty]

public theorem elts_make_nil [LT α] [DecidableLT α] [StrictLT α] :
  Set.elts (Set.make ([] : List α)) = []
:= by
  simp [make, elts, List.canonicalize_nil]

public theorem make_singleton_nonempty [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] (a : α) :
  Set.make [a] ≠ Set.empty
:= by
  simp [make, empty, List.canonicalize_singleton]

public def eq_means_eqv [LT α] [DecidableLT α] [StrictLT α] {s₁ s₂ : Set α} :
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

public theorem make_any_iff_any [LT α] [DecidableLT α] [StrictLT α] (f : α → Bool) (xs : List α) :
  (Set.make xs).any f = xs.any f
:= by
  simp only [make, any]
  have h₁ := List.canonicalize_equiv xs
  simp only [List.Equiv, List.subset_def] at h₁
  have ⟨hl₁, hr₁⟩ := h₁
  cases h₃ : List.any xs f
  case false =>
    false_or_by_contra ; rename_i h₄
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

public theorem make_of_make_is_id [LT α] [DecidableLT α] [StrictLT α] (xs : List α) :
  Set.make (Set.elts (Set.make xs)) = Set.make xs
:= by
  simp only [make, mk.injEq]
  have h₁ := List.canonicalize_idempotent id xs
  unfold id at h₁
  exact h₁

public theorem elts_make_is_id_then_equiv [LT α] [DecidableLT α] [StrictLT α] {xs ys : List α} :
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
public theorem make_cons [LT α] [DecidableLT α] {xs ys : List α} {a : α} :
  make xs = make ys → make (a :: xs) = make (a :: ys)
:= by
  simp only [make, mk.injEq]
  apply List.canonicalize_cons

/-! ### inter and union -/

public theorem inter_def {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {s₁ s₂ : Set α} :
  s₁ ∩ s₂ = s₁.intersect s₂
:= by simp only [Inter.inter]

open BEq LawfulBEq in
public theorem mem_inter_iff {α} [DecidableEq α] {x : α} {s₁ s₂ : Set α} :
  x ∈ s₁ ∩ s₂ ↔ x ∈ s₁ ∧ x ∈ s₂
:= by
  simp only [Membership.mem]
  have h := @List.mem_inter_iff α _ _ x (elts s₁) (elts s₂)
  simp only [Membership.mem, Inter.inter] at h
  exact h

public theorem inter_wf {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {s₁ s₂ : Set α}
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

public theorem inter_empty_left {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (s : Set α) :
 Set.empty ∩ s = Set.empty
:= by
  cases s ; rename_i xs
  simp only [Inter.inter, intersect, List.inter, elts, List.elem_eq_mem, empty, List.filter_nil]

public theorem inter_empty_right {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (s : Set α) :
 s ∩ Set.empty = Set.empty
:= by
  cases s ; rename_i xs
  simp only [Inter.inter, intersect, List.inter, elts, empty, List.elem_eq_mem, List.not_mem_nil,
    decide_false, mk.injEq, List.filter_eq_nil_iff, not_false_eq_true, implies_true, reduceCtorEq]

public theorem inter_self_eq {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (s : Set α) :
 s ∩ s = s
:= by
  simp only [Inter.inter, intersect, List.inter, elts, List.elem_eq_mem]
  cases s ; rename_i xs
  simp only [mk.injEq]
  induction xs
  case nil =>
    simp only [List.not_mem_nil, decide_false, List.filter_nil]
  case cons hd tl ih =>
    simp only [List.mem_cons, true_or, decide_true, List.filter_cons_of_pos, List.cons.injEq, true_and]
    rw [eq_comm]
    rw (config := {occs := .pos [1]}) [← ih]
    rw [List.filter_congr]
    simp only [Bool.decide_or, Bool.eq_or_self, decide_eq_true_eq]
    intro _ h
    simp only [h, implies_true]

public theorem intersects_def {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {s₁ s₂ : Set α} :
 s₁.intersects s₂ = ¬ (s₁ ∩ s₂).isEmpty
:= by
  simp only [Bool.not_eq_true, eq_iff_iff]
  simp only [intersects, List.any_eq_true, in_list_iff_in_set, contains_prop_bool_equiv]
  constructor
  case mp =>
    intro h
    replace ⟨x, h⟩ := h
    false_or_by_contra ; rename_i hc
    simp only [ne_eq, Bool.not_eq_false] at hc
    simp only [empty_iff_not_exists, not_exists] at hc
    specialize hc x
    have _ := mem_inter_iff.mpr h
    contradiction
  case mpr =>
    intro h
    replace h : ¬ isEmpty (s₁ ∩ s₂) = true := by
      simp only [h, not_false_eq_true, reduceCtorEq]
    rw [non_empty_iff_exists] at h
    replace ⟨x, h⟩ := h
    rw [mem_inter_iff] at h
    exists x

public theorem intersects_iff_exists {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {s₁ s₂ : Set α} :
 s₁.intersects s₂ ↔ ∃ a, a ∈ s₁ ∧ a ∈ s₂
:= by
  rw [intersects_def, non_empty_iff_exists]
  simp only [mem_inter_iff]

public theorem union_wf [LT α] [DecidableLT α] [StrictLT α] (s₁ s₂ : Set α) :
  WellFormed (s₁ ∪ s₂)
:= by
  simp only [Union.union, union, make_wf]

public theorem make_cons_eq_singleton_union [LT α] [DecidableLT α] [StrictLT α] (a : α) (L : List α) :
  Set.make (a :: L) = Set.singleton a ∪ Set.make L := by
  rw [← eq_means_eqv (make_wf _) (union_wf _ _)]
  simp only [make, singleton, Union.union, union, elts]
  rw [List.canonicalize_cons]
  · apply List.Equiv.refl
  · simp [List.canonicalize_idempotent]

public theorem mem_union_iff_mem_or [LT α] [DecidableLT α] [StrictLT α] (s₁ s₂ : Set α) :
  ∀ a, a ∈ s₁ ∪ s₂ ↔ (a ∈ s₁ ∨ a ∈ s₂)
:= by
  intro a
  simp only [Union.union, union, make, ← in_list_iff_in_mk]
  constructor <;> intro h
  case mp =>
    have hc := (List.canonicalize_equiv (s₁.elts ++ s₂.elts)).right
    simp only [List.subset_def, List.mem_append] at hc
    replace hc := hc h
    rcases hc with hc | hc <;>
    simp only [(in_list_iff_in_set _ _).mp hc, true_or, or_true]
  case mpr =>
    have hc := (List.canonicalize_equiv (s₁.elts ++ s₂.elts)).left
    simp only [List.append_subset] at hc
    simp only [List.subset_def] at hc
    simp only [← in_list_iff_in_set] at h
    rcases h with h | h
    · exact hc.left h
    · exact hc.right h

public theorem prop_union_iff_prop_and [LT α] [DecidableLT α] [StrictLT α] (p : α → Prop) (s₁ s₂ : Set α) :
  ((∀ a ∈ s₁, p a) ∧ (∀ a ∈ s₂, p a)) ↔ ∀ a ∈ (s₁ ∪ s₂), p a
:= by
  constructor <;> intro h₁
  case mp =>
    intro a h₂
    rw [mem_union_iff_mem_or] at h₂
    rcases h₂ with h₂ | h₂
    · exact h₁.left a h₂
    · exact h₁.right a h₂
  case mpr =>
    constructor
    all_goals {
      intro a h₂
      specialize h₁ a
      simp only [mem_union_iff_mem_or, h₂, or_true, true_or, true_implies] at h₁
      exact h₁
    }

public theorem union_comm [LT α] [DecidableLT α] [StrictLT α] (s₁ s₂ : Set α) :
  s₁ ∪ s₂ = s₂ ∪ s₁
:= by
  simp only [Union.union, union, make, elts, mk.injEq]
  apply List.equiv_implies_canonical_eq
  simp only [List.Equiv, List.append_subset,
    List.subset_append_right, List.subset_append_left, and_self]

public theorem union_assoc [LT α] [DecidableLT α] [StrictLT α] (s₁ s₂ s₃ : Set α) :
  (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃)
:= by
  rw [← eq_means_eqv (union_wf _ _) (union_wf _ _)]
  simp only [Union.union, Set.union, Set.make, Set.elts]
  have h₁ := List.Equiv.symm (List.canonicalize_equiv (List.canonicalize id (s₁.1 ++ s₂.1) ++ s₃.1))
  have h₂ := List.Equiv.symm (List.canonicalize_equiv (s₁.1 ++ List.canonicalize id (s₂.1 ++ s₃.1)))
  apply List.Equiv.trans h₁
  apply List.Equiv.symm
  apply List.Equiv.trans h₂
  have h₃ := List.Equiv.symm (List.canonicalize_equiv (s₂.1 ++ s₃.1))
  replace h₃ := List.append_right_equiv s₁.1 _ _ h₃
  have h₄ := List.Equiv.symm (List.canonicalize_equiv (s₁.1 ++ s₂.1))
  replace h₄ := List.append_left_equiv _ _ s₃.1 h₄
  apply List.Equiv.trans h₃
  apply List.Equiv.symm
  apply List.Equiv.trans h₄
  simp only [List.append_assoc]
  exact List.append_right_equiv _ _ _ List.Equiv.refl

public theorem union_empty_right [LT α] [DecidableLT α] [StrictLT α] {s : Set α} :
  s.WellFormed → s ∪ Set.empty = s
:= by
  intro h
  simp only [WellFormed, toList, elts] at h
  simp only [Union.union, union, elts, empty, List.append_nil, ← h]

public theorem union_empty_left [LT α] [DecidableLT α] [StrictLT α] {s : Set α} :
  s.WellFormed → Set.empty ∪ s = s
:= by
  rw [union_comm]
  exact union_empty_right

public theorem union_idempotent [LT α] [DecidableLT α] [StrictLT α] {s : Set α} :
  s.WellFormed → s ∪ s = s
:= by
  intro h
  rw [← eq_means_eqv (union_wf _ _) h]
  simp only [Union.union, Set.union, Set.make, Set.elts]
  apply List.Equiv.trans (List.Equiv.symm (List.canonicalize_equiv _))
  simp only [List.Equiv, List.append_subset, List.Subset.refl, and_self, List.subset_append_left]

/-! ### subset -/

public theorem elts_subset_then_subset [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {xs ys : List α} :
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
public theorem subset_def [DecidableEq α] {s₁ s₂ : Set α} :
  s₁ ⊆ s₂ ↔ ∀ a, a ∈ s₁ → a ∈ s₂
:= by
  simp only [Subset, subset, List.all_eq_true]
  constructor <;> intro h₁ a h₂ <;> specialize h₁ a
  case mp =>
    rw [in_list_iff_in_set] at h₁
    rw [contains_prop_bool_equiv] at h₁
    exact h₁ h₂
  case mpr =>
    rw [in_list_iff_in_set] at h₂
    rw [contains_prop_bool_equiv]
    exact h₁ h₂

public theorem superset_empty_subset_empty [DecidableEq α] {s₁ s₂ : Set α} :
  s₁ ⊆ s₂ → s₂.isEmpty → s₁.isEmpty
:= by
  simp only [empty_iff_not_exists, subset_def, not_exists]
  intro h₁ h₂ a h₃
  exact h₂ a (h₁ a h₃)

public theorem subset_iff_subset_elts [DecidableEq α] {s₁ s₂ : Set α} :
  s₁ ⊆ s₂ ↔ s₁.elts ⊆ s₂.elts
:= by
  simp only [subset_def, elts, List.subset_def, in_list_iff_in_set]

public theorem subset_iff_eq [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {s₁ s₂ : Set α} :
  WellFormed s₁ → WellFormed s₂ →
  ((s₁ ⊆ s₂ ∧ s₂ ⊆ s₁) ↔ s₁ = s₂)
:= by
  intro hw₁ hw₂
  simp only [← (eq_means_eqv hw₁ hw₂), elts, List.Equiv, subset_iff_subset_elts]

public theorem subset_trans [DecidableEq α] {s₁ s₂ s₃ : Set α} :
  s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃
:= by
  simp only [subset_def]
  intro h₁ h₂ a ha
  exact h₂ a (h₁ a ha)

public theorem subset_refl [DecidableEq α] {s : Set α} :
  s ⊆ s
:= by
  simp only [subset_def, imp_self, implies_true]

public theorem mem_subset_mem [DecidableEq α] {a : α} {s₁ s₂ : Set α} :
  a ∈ s₁ → s₁ ⊆ s₂ → a ∈ s₂
:= by
  simp only [subset_def]
  intro h₁ h₂
  exact h₂ a h₁

public theorem subset_union [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] (s₁ s₂ : Set α) :
  s₁ ⊆ s₁ ∪ s₂
:= by
  simp only [subset_def, mem_union_iff_mem_or]
  intro a hin
  exact Or.inl hin

public theorem union_subset [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {s₁ s₂ s₃ : Set α} :
  s₁ ∪ s₂ ⊆ s₃ ↔ s₁ ⊆ s₃ ∧ s₂ ⊆ s₃
:= by
  simp only [subset_def, mem_union_iff_mem_or]
  constructor
  case mp =>
    intro h
    constructor
    all_goals {
      intro a hin
      apply h a
      simp only [hin, true_or, or_true]
    }
  case mpr =>
    intro h a hor
    rcases hor with hor | hor
    · exact h.left a hor
    · exact h.right a hor

public theorem union_subset_eq [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {s₁ s₂ : Set α} :
  s₂.WellFormed → s₁ ⊆ s₂ → s₁ ∪ s₂ = s₂
:= by
  intro h₁ h₂
  rw [← subset_iff_eq (union_wf _ _) h₁]
  constructor
  · simp only [union_subset, h₂, subset_refl, and_self]
  · rw [union_comm]
    exact subset_union _ _

public theorem wellFormed_correct {α} [LT α] [StrictLT α] [DecidableLT α] {s : Set α} :
  s.wellFormed = true ↔ s.WellFormed
:= by
  constructor
  · intros h
    apply (wf_iff_sorted s).mpr
    apply List.isSorted_correct.mpr
    exact h
  · intros h
    apply List.isSorted_correct.mp
    apply (wf_iff_sorted s).mp
    exact h

/-! ### map -/

/-- Analogue of `List.mem_map` but for sets -/
public theorem mem_map [LT α] [DecidableLT α] [StrictLT α] [LT β] [DecidableLT β] [StrictLT β] (b : β) (f : α → β) (s : Set α) :
  b ∈ s.map f ↔ ∃ a ∈ s, f a = b
:= by
  simp [Set.map, ← Set.make_mem, Set.in_list_iff_in_set]

/-! ### filter and differences -/

public theorem filter_wf [LT α] [DecidableLT α] [StrictLT α] (p : α → Bool) (s : Set α) :
  WellFormed s →
  WellFormed (s.filter p)
:= by
  simp only [Set.filter, wf_iff_sorted]
  apply List.filter_sortedBy

public theorem mem_filter [LT α] [DecidableLT α] [StrictLT α] (p : α → Bool) (s : Set α) (e : α):
  e ∈ s.filter p ↔ (e ∈ s ∧ p e)
:= by
  simp only [filter]
  rw [←in_list_iff_in_mk, ←in_list_iff_in_set]
  simp [List.mem_filter]

public theorem difference_wf [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] (s₁ s₂ : Set α) :
  WellFormed s₁ →
  WellFormed (s₁.difference s₂)
:= by apply filter_wf

public theorem mem_difference [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] (s₁ s₂ : Set α) (e : α):
  e ∈ s₁.difference s₂ ↔ (e ∈ s₁ ∧ e ∉ s₂)
:= by simp [difference, mem_filter, ←not_contains_prop_bool_equiv]

public theorem difference_subset [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] (s₁ s₂ : Set α) :
  (s₁.difference s₂) ⊆ s₁
:= by
  rw [subset_def]
  intro s
  rw [mem_difference]
  exact And.left

end Cedar.Data.Set
