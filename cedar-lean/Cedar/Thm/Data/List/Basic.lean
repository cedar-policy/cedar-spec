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
import Cedar.Data.LT
import Cedar.Thm.Data.Control
import Batteries.Logic

/-!

# List properties

This file contains useful custom definitions and lemmas about Lists.

-/

namespace List

open Cedar.Data

/-! ### Equiv -/

def Equiv {α} (a b : List α) : Prop :=
  a ⊆ b ∧ b ⊆ a

infix:50 " ≡ " => Equiv

theorem Equiv.refl {a : List α} :
  a ≡ a
:= by unfold List.Equiv; simp only [Subset.refl, and_self]

theorem Equiv.symm {a b : List α} :
  a ≡ b → b ≡ a
:= by unfold List.Equiv; simp only [and_imp]; intro h₁ h₂; simp [h₁, h₂]

theorem Equiv.trans {a b c : List α} :
  a ≡ b → b ≡ c → a ≡ c
:= by
  unfold List.Equiv
  simp only [and_imp]
  intro h₁ h₂ h₃ h₄
  apply And.intro
  exact List.Subset.trans h₁ h₃
  exact List.Subset.trans h₄ h₂

theorem equiv_nil (xs : List α) :
  xs ≡ [] ↔ xs = []
:= by
  constructor <;> intro h
  · simp only [Equiv, nil_subset, and_true] at h
    rw [← List.subset_nil]
    exact h
  · subst h
    exact Equiv.refl

theorem cons_equiv_cons (x : α) (xs ys : List α) :
  xs ≡ ys → x :: xs ≡ x :: ys
:= by
  unfold List.Equiv
  intro h₁
  have ⟨h₁, h₂⟩ := h₁
  apply And.intro
  all_goals {
    apply List.cons_subset_cons; assumption
  }

theorem dup_head_equiv (x : α) (xs : List α) :
  x :: x :: xs ≡ x :: xs
:= by unfold List.Equiv; simp [List.subset_def]

theorem swap_cons_cons_equiv (x₁ x₂ : α) (xs : List α) :
  x₁ :: x₂ :: xs ≡ x₂ :: x₁ :: xs
:= by
  unfold List.Equiv
  simp only [subset_def, mem_cons, forall_eq_or_imp, true_or, or_true, true_and]
  apply And.intro
  all_goals { intro a h₁; simp [h₁] }

theorem filter_equiv (f : α → Bool) (xs ys : List α) :
  xs ≡ ys → xs.filter f ≡ ys.filter f
:= by
  simp only [Equiv, subset_def, and_imp]
  intros h₁ h₂
  apply And.intro <;>
  intro a h₃ <;>
  rw [mem_filter] <;> rw [mem_filter] at h₃
  exact And.intro (h₁ h₃.left) h₃.right
  exact And.intro (h₂ h₃.left) h₃.right

theorem map_equiv (f : α → β) (xs ys : List α) :
  xs ≡ ys → xs.map f ≡ ys.map f
:= by
  intro h
  have ⟨a, b⟩ := h
  apply And.intro <;>
  simp only [subset_def, mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] <;>
  intro p h <;>
  exists p <;>
  rw [List.subset_def] at a b <;>
  simp only [and_true]
  · exact a h
  · exact b h

theorem filterMap_equiv (f : α → Option β) (xs ys : List α) :
  xs ≡ ys → xs.filterMap f ≡ ys.filterMap f
:= by
  simp only [Equiv, subset_def, mem_filterMap, forall_exists_index, and_imp]
  intros h₁ h₂
  apply And.intro <;>
  intro b a h₃ h₄ <;>
  exists a <;>
  simp only [h₄, and_true]
  · exact h₁ h₃
  · exact h₂ h₃

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

theorem mem_of_sortedBy_implies_find? {α β} [LT β] [StrictLT β] [DecidableLT β] [DecidableEq β]
  {f : α → β} {x : α} {xs : List α} :
  x ∈ xs → xs.SortedBy f →
  xs.find? (fun y => f y == f x) = x
:= by
  intro h₁ h₂
  induction xs
  case nil =>
    simp only [not_mem_nil] at h₁
  case cons hd tl ih =>
    simp only [mem_cons] at h₁
    simp only [find?_cons]
    split <;> rename_i heq
    · simp only [beq_iff_eq] at heq
      simp only [Option.some.injEq]
      rcases h₁ with h₁ | h₁
      · simp only [h₁]
      · have h₃ := sortedBy_implies_head_lt_tail h₂ x h₁
        simp only [heq, StrictLT.irreflexive] at h₃
    · simp only [beq_eq_false_iff_ne, ne_eq] at heq
      rcases h₁ with h₁ | h₁
      · simp only [h₁, not_true_eq_false] at heq
      · exact ih h₁ (tail_sortedBy h₂)

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

/-! ### Forallᵥ -/

def Forallᵥ {α β γ} (p : β → γ → Prop) (kvs₁ : List (α × β)) (kvs₂ : List (α × γ)) : Prop :=
  List.Forall₂ (λ kv₁ kv₂ => kv₁.fst = kv₂.fst ∧ p kv₁.snd kv₂.snd) kvs₁ kvs₂

theorem forallᵥ_def {α β γ} {p : β → γ → Prop} {kvs₁ : List (α × β)} {kvs₂ : List (α × γ)} :
  List.Forallᵥ p kvs₁ kvs₂ = List.Forall₂ (λ kv₁ kv₂ => kv₁.fst = kv₂.fst ∧ p kv₁.snd kv₂.snd) kvs₁ kvs₂
:= by simp only [Forallᵥ]

end List
