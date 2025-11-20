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

import Cedar.Thm.Data.List
import Cedar.Thm.Data.Option
import Cedar.Thm.Data.Set

/-!
# Lemmas about List.mapUnion operator
-/

/-! ### List.mapUnion applied to lists of lists -/

namespace List

theorem mapUnion_pmap_subtype
  [Union β] [EmptyCollection β]
  {p : α → Prop}
  (f : α → β)
  (as : List α)
  (h : ∀ a, a ∈ as → p a) :
    List.mapUnion (λ x : { a : α // p a } => f x.val) (List.pmap Subtype.mk as h)
    =
    List.mapUnion f as
:= by
  simp only [mapUnion]
  rw [foldl_pmap_subtype λ a b => a ∪ f b]

private theorem mem_foldl_union_iff_mem_or_exists {α β} [DecidableEq α] {f : β → List α} {xs : List β} {init : List α} {a : α} :
  a ∈ List.foldl (λ as b => as ∪ f b) init xs ↔ (a ∈ init ∨ ∃ s ∈ xs, a ∈ f s)
:= by
  induction xs generalizing init
  case nil =>
    simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, or_false]
  case cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons, exists_eq_or_imp]
    specialize @ih (init ∪ f hd)
    constructor <;> intro h
    case mp =>
      replace ih := ih.mp h
      rw [List.mem_union_iff, or_assoc] at ih
      exact ih
    case mpr =>
      rw [← or_assoc, ← List.mem_union_iff] at h
      exact ih.mpr h

theorem mem_mapUnion_iff_mem_exists {α β} [DecidableEq α] {f : β → List α} {xs : List β} :
  ∀ e, e ∈ xs.mapUnion f ↔ ∃ s ∈ xs, e ∈ f s
:= by
  intro e
  simp only [List.mapUnion, EmptyCollection.emptyCollection]
  cases xs
  case nil =>
    simp only [foldl_nil, not_mem_nil, false_and, exists_false]
  case cons xhd xtl ih =>
    simp only [foldl_cons, nil_union, mem_cons, exists_eq_or_imp]
    exact mem_foldl_union_iff_mem_or_exists

end List

/-! ### List.mapUnion applied to lists of sets -/

namespace Cedar.Data.Set

theorem mapUnion_wf {α β} [LT α] [StrictLT α] [DecidableLT α] {f : β → Set α} {xs : List β} :
  (xs.mapUnion f).WellFormed
:= by
  simp only [List.mapUnion]
  generalize h : (∅ : Set α) = a
  have ha : a.WellFormed := by
    subst h
    simp only [EmptyCollection.emptyCollection]
    exact Set.empty_wf
  clear h
  induction xs generalizing a
  case nil =>
    simp only [ha, List.foldl_nil]
  case cons xhd xtl ih =>
    simp only [List.foldl_cons]
    exact ih _ (Set.union_wf _ _)

theorem mapUnion_empty {α β} [LT α] [StrictLT α] [DecidableLT α] {f : β → Set α} :
  [].mapUnion f = ∅
:= by
  simp only [List.mapUnion, EmptyCollection.emptyCollection, List.foldl_nil]

private theorem foldl_union_init {α β} [LT α] [StrictLT α] [DecidableLT α] {f : β → Set α} {xs : List β} {a b : Set α} :
  List.foldl (λ acc x => acc ∪ f x) (a ∪ b) xs = a ∪ List.foldl (λ acc x => acc ∪ f x) b xs
:= by
  induction xs generalizing a b
  case nil =>
    simp only [List.foldl_nil]
  case cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [Set.union_assoc]
    rw [ih (a := a) (b := b ∪ f hd)]

theorem mapUnion_cons {α β} [LT α] [StrictLT α] [DecidableLT α] {f : β → Set α} {hd : β} {tl : List β} :
  (∀ b, (f b).WellFormed) →
  (hd :: tl).mapUnion f = f hd ∪ tl.mapUnion f
:= by
  intro hwf
  simp only [List.mapUnion, EmptyCollection.emptyCollection, List.foldl_cons]
  rw [Set.union_empty_left (hwf hd)]
  rw [← Set.union_empty_left (hwf hd)]
  rw [foldl_union_init (a := Set.empty) (b := f hd)]
  rw [← foldl_union_init (a := Set.empty ∪ f hd) (b := Set.empty)]
  have h : Set.empty ∪ f hd ∪ Set.empty = Set.empty ∪ f hd := by
    rw [Set.union_empty_right (Set.union_wf _ _)]
  rw [h]
  rw [foldl_union_init (a := Set.empty) (b := f hd)]

private theorem mem_foldl_union_iff_mem_or_exists {α β} [LT α] [StrictLT α] [DecidableLT α] {f : β → Set α} {xs : List β} {init : Set α} {a : α} :
  a ∈ List.foldl (λ as b => as ∪ f b) init xs ↔ (a ∈ init ∨ ∃ s ∈ xs, a ∈ f s)
:= by
  induction xs generalizing init
  case nil =>
    simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, or_false]
  case cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons, exists_eq_or_imp]
    specialize @ih (init ∪ f hd)
    constructor <;> intro h
    case mp =>
      replace ih := ih.mp h
      rw [Set.mem_union_iff_mem_or, or_assoc] at ih
      exact ih
    case mpr =>
      rw [← or_assoc, ← Set.mem_union_iff_mem_or] at h
      exact ih.mpr h

theorem mem_mapUnion_iff_mem_exists {α β} [LT α] [StrictLT α] [DecidableLT α] {f : β → Set α} {xs : List β} :
  ∀ e, e ∈ xs.mapUnion f ↔ ∃ s ∈ xs, e ∈ f s
:= by
  intro e
  simp only [List.mapUnion, EmptyCollection.emptyCollection]
  cases xs
  case nil =>
    simp only [List.foldl_nil, empty_no_elts, List.not_mem_nil,
      false_and, exists_false]
  case cons hd tl =>
    have h : e ∈ f hd ↔ e ∈ (empty ∪ f hd) := by
      simp only [mem_union_iff_mem_or, empty_no_elts, false_or]
    simp only [List.foldl_cons, List.mem_cons, exists_eq_or_imp, h, mem_foldl_union_iff_mem_or_exists]

theorem mem_mem_implies_mem_mapUnion {α β} [LT α] [StrictLT α] [DecidableLT α] {f : β → Set α} {xs : List β} {e : α} {s : β} :
  e ∈ f s → s ∈ xs → e ∈ xs.mapUnion f
:= by
  intro he hs
  rw [mem_mapUnion_iff_mem_exists]
  exists s

theorem mem_implies_subset_mapUnion {α β} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (f : β → Set α) {xs : List β} {s : β} :
  s ∈ xs → f s ⊆ xs.mapUnion f
:= by
  simp only [subset_def]
  intro hs a ha
  exact mem_mem_implies_mem_mapUnion ha hs

theorem mapUnion_filterMap {α β γ} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {f : β → Set α} {g : γ → Option β} {xs : List γ} :
  (xs.filterMap g).mapUnion f =
  xs.mapUnion λ x => (g x).mapD f Set.empty
:= by
  simp only [List.mapUnion]
  generalize h : (∅ : Set α) = a
  have ha : a ∪ Set.empty = a := by
    subst h
    exact Set.union_idempotent Set.empty_wf
  clear h
  induction xs generalizing a
  case nil => simp only [List.filterMap_nil, List.foldl_nil]
  case cons hd tl ih =>
    simp only [List.filterMap_cons, List.foldl_cons]
    cases g hd <;> simp only [List.foldl_cons]
    case none =>
      simp only [Option.mapD_none]
      rw [ha]
      exact ih a ha
    case some y =>
      simp only [Option.mapD_some]
      apply ih
      apply Set.union_empty_right (Set.union_wf _ _)

theorem mapUnion_congr {α β} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (f g : β → Set α) {xs : List β} :
  (∀ b ∈ xs, f b = g b) → xs.mapUnion f = xs.mapUnion g
:= by
  intro h
  simp only [List.mapUnion]
  generalize h : (∅ : Set α) = a
  clear h
  induction xs generalizing a
  case nil => simp only [List.foldl_nil]
  case cons hd tl ih =>
    simp only [List.foldl_cons]
    have heq := h hd (by simp only [List.mem_cons, true_or])
    rw [heq]
    apply ih
    intro b htl
    apply h
    simp only [List.mem_cons, htl, or_true]

theorem mapUnion_eq_mapUnion_id_map {α β} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (f : β → Set α) {xs : List β} :
  xs.mapUnion f = (xs.map f).mapUnion id
:= by
  simp only [List.mapUnion]
  generalize h : (∅ : Set α) = a
  clear h
  induction xs generalizing a
  case nil => simp only [List.foldl_nil, id_eq, List.map_nil]
  case cons hd tl ih =>
    simp only [List.foldl_cons, id_eq, List.map_cons]
    apply ih

private theorem foldl_union_append {α β} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {g : β → Set α} {xs ys : List β} {a : Set α} :
  List.foldl (λ acc b => acc ∪ g b) a (xs.append ys) = List.foldl (λ acc b => acc ∪ g b) (List.foldl (λ acc b => acc ∪ g b) a xs) ys
:= by
  induction xs generalizing a
  case nil =>
    simp only [List.foldl_nil]
    rfl
  case cons xhd xtl ih =>
    simp only [List.append, List.foldl_cons]
    rw [ih]

theorem mapUnion_append {α β} [LT α] [StrictLT α] [DecidableLT α] {f : β → Set α} {xs ys : List β} :
  (∀ b, (f b).WellFormed) →
  (xs ++ ys).mapUnion f = xs.mapUnion f ++ ys.mapUnion f
:= by
  intro hwf
  induction xs
  case nil =>
    simp only [List.nil_append, mapUnion_empty]
    change _ = Set.empty ∪ ys.mapUnion f
    rw [Set.union_empty_left]
    exact mapUnion_wf
  case cons hd tl ih =>
    simp only [List.cons_append]
    rw [mapUnion_cons hwf, mapUnion_cons hwf, ih]
    change _ ∪ (_ ∪ _) = (_ ∪ _) ∪ _
    symm
    apply Set.union_assoc

private theorem foldl_union_swap_front {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (x₁ x₂ : Set α) {xs : List (Set α)} {a : Set α}:
  (x₁ :: x₂ :: xs).foldl (· ∪ ·) a = (x₂ :: x₁ :: xs).foldl (· ∪ ·) a
:= by
  simp only [List.foldl_cons, Set.union_assoc]
  rw [Set.union_comm x₁]

private theorem foldl_union_swap_middle {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (y : Set α) {xs ys : List (Set α)} {a : Set α}:
  (xs ++ y :: ys).foldl (· ∪ ·) a = (y :: xs ++ ys).foldl (· ∪ ·) a
:= by
  cases xs
  case nil =>
    simp only [List.nil_append, List.foldl_cons, List.singleton_append]
  case cons xhd xtl =>
    rw [eq_comm, List.cons_append, List.cons_append, foldl_union_swap_front y xhd, eq_comm]
    rw [List.foldl_cons, List.cons_append, List.foldl_cons]
    exact foldl_union_swap_middle y

private theorem foldl_union_comm {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {xs ys : List (Set α)} {a : Set α}:
  (xs ++ ys).foldl (· ∪ ·) a = (ys ++ xs).foldl (· ∪ ·) a
:= by
  cases xs <;> cases ys
  case nil.nil =>
    simp only [List.append_nil]
  case nil.cons | cons.nil =>
    simp only [List.append_nil, List.nil_append, List.foldl_cons]
  case cons xhd xtl yhd ytl =>
    rw [foldl_union_swap_middle, foldl_union_swap_middle, ← List.singleton_append, List.append_assoc,
      @List.cons_append _ xhd, foldl_union_swap_middle]
    simp only [List.cons_append, List.foldl_cons, List.nil_append]
    exact foldl_union_comm

theorem mapUnion_comm {α β} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {f : β → Set α} {xs ys : List β} :
  (xs ++ ys).mapUnion f = (ys ++ xs).mapUnion f
:= by
  rw [mapUnion_eq_mapUnion_id_map, eq_comm, mapUnion_eq_mapUnion_id_map, eq_comm]
  simp only [List.mapUnion, id_eq, List.map_append]
  exact foldl_union_comm

private theorem foldl_union_remove_head {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (x : Set α) (xs : List (Set α)) {a : Set α}:
  (x :: xs).foldl (· ∪ ·) a = (x :: (xs.removeAll [x])).foldl (· ∪ ·) a
:= by
  simp only [List.foldl_cons, List.removeAll]
  induction xs generalizing a x
  case nil => simp only [List.foldl_nil, List.filter_nil]
  case cons xhd xtl ih =>
    simp only [List.foldl_cons, List.elem_eq_mem, List.mem_singleton,
      List.filter_cons, Bool.not_eq_true', decide_eq_false_iff_not, ite_not]
    simp only [List.elem_eq_mem, List.mem_singleton] at ih
    have heq : (a ∪ xhd ∪ xhd) = a ∪ xhd := by
      rw [Set.union_comm (a ∪ xhd)]
      apply Set.union_subset_eq (Set.union_wf _ _)
      rw [Set.union_comm]
      exact Set.subset_union _ _
    split
    case isTrue h =>
      subst h
      simp only [heq]
      exact ih xhd
    case isFalse h =>
      simp only [List.foldl_cons]
      rw [Set.union_comm _ xhd, ← Set.union_assoc, Set.union_comm xhd]
      exact @ih x (a ∪ xhd)

private theorem eqv_implies_foldl_union_eq {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {xs ys : List (Set α)} {a : Set α}:
  xs ≡ ys → xs.foldl (· ∪ ·) a = ys.foldl (· ∪ ·) a
:= by
  intro heqv
  cases xs <;> cases ys
  case nil.nil =>
    simp only [List.foldl_nil]
  case nil.cons =>
    replace heqv := List.Equiv.symm heqv
    simp only [List.equiv_nil, reduceCtorEq] at heqv
  case cons.nil =>
    simp only [List.equiv_nil, reduceCtorEq] at heqv
  case cons.cons xhd xtl yhd ytl =>
    have ⟨ytl₁, ytl₂, h⟩ := List.mem_iff_append.mp (List.cons_subset.mp heqv.left).left
    rw [h, foldl_union_comm, foldl_union_remove_head xhd xtl, List.cons_append,
      foldl_union_remove_head xhd (ytl₂ ++ ytl₁)]
    simp only [h] at heqv
    replace heqv : xhd :: xtl ≡ xhd :: (ytl₂ ++ ytl₁) := by
      apply List.Equiv.trans heqv
      apply List.Equiv.trans (List.append_swap_equiv ytl₁ _)
      simp only [List.cons_append, List.Equiv.refl]
    replace heqv : xtl.removeAll [xhd] ≡ (ytl₂ ++ ytl₁).removeAll [xhd] := by
      apply List.cons_equiv_implies_equiv xhd _ _
      · apply List.Equiv.trans (List.Equiv.symm (List.removeAll_singleton_equiv xhd xtl))
        apply List.Equiv.trans heqv
        exact List.removeAll_singleton_equiv xhd (ytl₂ ++ ytl₁)
      · exact List.mem_removeAll_singleton_of_eq xhd xtl
      · exact List.mem_removeAll_singleton_of_eq xhd (ytl₂ ++ ytl₁)
    simp only [List.foldl_cons]
    exact eqv_implies_foldl_union_eq heqv
termination_by xs.length
decreasing_by
  simp_wf
  rename_i xhd xtl hxs _ _ _ _ _ _
  simp only [hxs, List.length_cons]
  have _ := List.length_removeAll_le xtl [xhd]
  omega

-- Note that the converse doesn't hold. For example, let f = g = id,
-- xs = [{a}, {b}], and ys = [{a, b}]
theorem map_eqv_implies_mapUnion_eq {α β γ} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {f : β → Set α} {g : γ → Set α} {xs : List β} {ys : List γ} :
  xs.map f ≡ ys.map g → xs.mapUnion f = ys.mapUnion g
:= by
  intro hm
  rw [mapUnion_eq_mapUnion_id_map, eq_comm, mapUnion_eq_mapUnion_id_map, eq_comm]
  simp only [List.mapUnion, id_eq]
  exact eqv_implies_foldl_union_eq hm

end Cedar.Data.Set
