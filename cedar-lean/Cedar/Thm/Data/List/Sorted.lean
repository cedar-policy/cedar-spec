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

import Cedar.Data.List
import Cedar.Thm.Data.List.Equiv

namespace List

open Cedar.Data

/-! ### Sorted -/

inductive SortedBy [LT β] (f : α → β) : List α → Prop where
  | nil : SortedBy f []
  | cons_nil {x} : SortedBy f (x :: nil)
  | cons_cons {x y ys} :
      f x < f y →
      SortedBy f (y :: ys) →
      SortedBy f (x :: y :: ys)

abbrev Sorted [LT α] (xs : List α) := SortedBy id xs

theorem tail_sortedBy [LT β] {f : α → β} {x : α} {xs : List α} :
  SortedBy f (x :: xs) → SortedBy f xs
:= by
  intro h₁; cases h₁
  exact SortedBy.nil
  assumption

theorem sortedBy_implies_head_lt_tail [LT β] [StrictLT β] {f : α → β} {x : α} {xs : List α} :
  SortedBy f (x :: xs) → ∀ y, y ∈ xs → f x < f y
:= by
  intro h₁ y h₂
  induction xs generalizing y
  case nil => contradiction
  case cons hd tl ih =>
    cases h₂
    case head => cases h₁; assumption
    case tail h₂ =>
      apply ih _ _ h₂
      cases h₁
      case cons_cons h₃ h₄ =>
        cases h₄
        case _ => exact SortedBy.cons_nil
        case cons_cons _ _ hd' tl' h₅ h₆ =>
          apply SortedBy.cons_cons _ h₅
          exact StrictLT.transitive (f x) (f hd) (f hd') h₃ h₆

theorem sortedBy_equiv_implies_head_eq [LT β] [StrictLT β] (f : α → β) {x y : α} {xs ys : List α} :
  SortedBy f (x :: xs) →
  SortedBy f (y :: ys) →
  (x :: xs) ≡ (y :: ys) →
  x = y
:= by
  intro h₁ h₂
  unfold List.Equiv; intro h₃
  simp only [cons_subset, mem_cons] at h₃
  replace ⟨⟨h₃, _⟩, ⟨h₄, _⟩⟩ := h₃
  cases h₃ <;> cases h₄ <;> try { assumption }
  case _ _ h₅ => simp [h₅]
  case _ h₅ h₆ =>
    have hc₁ := sortedBy_implies_head_lt_tail h₁ y h₆
    have hc₂ := sortedBy_implies_head_lt_tail h₂ x h₅
    have hc₃ := StrictLT.asymmetric (f x) (f y) hc₁
    contradiction

theorem sortedBy_equiv_implies_tail_subset [LT β] [StrictLT β] (f : α → β) {x : α} {xs ys : List α} :
  SortedBy f (x :: xs) →
  SortedBy f (x :: ys) →
  (x :: xs) ⊆ (x :: ys) →
  xs ⊆ ys
:= by
  intro h₁ h₂ h₃
  simp only [cons_subset, mem_cons, true_or, true_and] at h₃
  simp only [subset_def]
  simp only [subset_def, mem_cons] at h₃
  intro y h₄
  specialize h₃ h₄
  cases h₃
  · rename_i h₃ ; subst h₃
    have h₅ := sortedBy_implies_head_lt_tail h₁ y h₄
    have h₆ := StrictLT.irreflexive (f y)
    contradiction
  · assumption

theorem sortedBy_equiv_implies_tail_equiv [LT β] [StrictLT β] (f : α → β) {x : α} {xs ys : List α} :
  SortedBy f (x :: xs) →
  SortedBy f (x :: ys) →
  (x :: xs) ≡ (x :: ys) →
  xs ≡ ys
:= by
  unfold List.Equiv
  intro h₁ h₂ h₃
  replace ⟨h₃, h₄⟩ := h₃
  apply And.intro
  exact sortedBy_equiv_implies_tail_subset f h₁ h₂ h₃
  exact sortedBy_equiv_implies_tail_subset f h₂ h₁ h₄

theorem sortedBy_equiv_implies_eq [LT β] [StrictLT β] (f : α → β) {xs ys : List α} :
  SortedBy f xs → SortedBy f ys → xs ≡ ys → xs = ys
:= by
  intro h₁ h₂ h₃
  induction xs generalizing ys
  case nil =>
    apply Eq.symm
    rw [←List.subset_nil]
    unfold List.Equiv at h₃
    exact h₃.right
  case cons xhd xtl ih =>
    cases ys
    case nil =>
      unfold List.Equiv at h₃
      rw [←List.subset_nil]
      exact h₃.left
    case cons yhd ytl =>
      simp only [cons.injEq]
      have h₅ := sortedBy_equiv_implies_head_eq f h₁ h₂ h₃
      simp only [h₅, true_and]
      subst h₅
      apply ih
      exact (tail_sortedBy h₁)
      exact (tail_sortedBy h₂)
      exact (sortedBy_equiv_implies_tail_equiv f h₁ h₂ h₃)

theorem sortedBy_cons [LT β] [StrictLT β] {f : α → β} {x : α} {ys : List α} :
  SortedBy f ys →
  (∀ y, y ∈ ys → f x < f y) →
  SortedBy f (x :: ys)
:= by
  intro h₁ h₂
  cases ys
  case nil => exact SortedBy.cons_nil
  case cons hd tl =>
    apply SortedBy.cons_cons _ h₁
    apply h₂
    simp only [mem_cons, true_or]

theorem map_eq_implies_sortedBy [LT β] [StrictLT β] {f : α → β} {g : γ → β} {xs : List α} {ys : List γ} :
  xs.map f = ys.map g →
  (SortedBy f xs ↔ SortedBy g ys)
:= by
  intro h₁
  constructor
  case mp =>
    intro h₂
    cases xs <;> cases ys <;> simp only [map_nil, map_cons, cons.injEq] at h₁
    case nil.nil => exact SortedBy.nil
    case cons.cons xhd xtl yhd ytl =>
      replace ⟨h₁, h₃⟩ := h₁
      have ih := map_eq_implies_sortedBy h₃
      cases ytl <;> simp only [map_nil, map_cons, map_eq_nil] at *
      case nil => exact SortedBy.cons_nil
      case cons yhd' ytl =>
        simp only [tail_sortedBy h₂, true_iff] at ih
        apply SortedBy.cons_cons _ ih
        rw [← h₁]
        cases xtl <;> simp only [map_nil, map_cons, cons.injEq] at h₃
        case cons xhd' xtl =>
          rw [← h₃.left]
          apply sortedBy_implies_head_lt_tail h₂
          simp only [mem_cons, true_or]
  case mpr =>
    intro h₂
    cases xs <;> cases ys <;> simp only [map_nil, map_cons, cons.injEq] at h₁
    case nil.nil => exact SortedBy.nil
    case cons.cons xhd xtl yhd ytl =>
      replace ⟨h₁, h₃⟩ := h₁
      have ih := map_eq_implies_sortedBy h₃
      cases xtl <;> simp only [map_nil, map_cons, map_eq_nil] at *
      case nil => exact SortedBy.cons_nil
      case cons xhd' xtl =>
        simp only [tail_sortedBy h₂, iff_true] at ih
        apply SortedBy.cons_cons _ ih
        rw [h₁]
        cases ytl <;> simp only [map_nil, map_cons, cons.injEq] at h₃
        case cons yhd' ytl =>
          rw [h₃.left]
          apply sortedBy_implies_head_lt_tail h₂
          simp only [mem_cons, true_or]

theorem filter_sortedBy [LT β] [StrictLT β] [DecidableLT β] {f : α → β} (p : α → Bool) {xs : List α} :
  SortedBy f xs → SortedBy f (xs.filter p)
:= by
  intro h₁
  induction xs
  case nil => simp only [filter_nil, SortedBy.nil]
  case cons hd tl ih =>
    simp only [filter_cons]
    specialize ih (tail_sortedBy h₁)
    split
    · apply sortedBy_cons ih
      intro y h₂
      apply sortedBy_implies_head_lt_tail h₁
      rw [List.mem_filter] at h₂
      exact h₂.left
    · exact ih

theorem filterMap_sortedBy [LT β] [StrictLT β] [DecidableLT β] {f : α → β} {g : α → Option γ} {f' : γ → β} {xs : List α} :
  (∀ x y, g x = some y → f x = f' y) →
  SortedBy f xs →
  SortedBy f' (xs.filterMap g)
:= by
  intro h₁ h₂
  induction xs
  case nil => simp only [filterMap_nil, SortedBy.nil]
  case cons hd tl ih =>
    simp only [filterMap_cons]
    specialize ih (tail_sortedBy h₂)
    split
    case h_1 => exact ih
    case h_2 ac heq =>
      cases htl : filterMap g tl
      case nil =>
        exact SortedBy.cons_nil
      case cons hd' tl' =>
        rw [htl] at ih
        apply SortedBy.cons_cons _ ih
        rw [← h₁ hd ac heq]
        have hhd : hd' ∈ filterMap g tl := by simp only [htl, mem_cons, true_or]
        simp only [mem_filterMap] at hhd
        have ⟨x, hx, hgx⟩ := hhd
        rw [← h₁ x hd' hgx]
        exact sortedBy_implies_head_lt_tail h₂ x hx

theorem mem_of_sortedBy_unique {α β} [LT β] [StrictLT β] [DecidableLT β] [DecidableEq β]
  {f : α → β} {x y : α} {xs : List α} :
  xs.SortedBy f → x ∈ xs → y ∈ xs → f x = f y →
  x = y
:= by
  intro hsrt hx hy hf
  induction xs
  case nil =>
    simp only [not_mem_nil] at hx
  case cons hd tl ih =>
    simp only [mem_cons] at hx hy
    specialize ih (tail_sortedBy hsrt)
    have hlt := sortedBy_implies_head_lt_tail hsrt
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · simp only [hx, hy]
    · subst hx
      specialize hlt y hy
      simp only [hf, StrictLT.irreflexive] at hlt
    · subst hy
      specialize hlt x hx
      simp only [hf, StrictLT.irreflexive] at hlt
    · exact ih hx hy

end List
