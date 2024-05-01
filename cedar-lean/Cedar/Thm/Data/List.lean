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
import Std.Logic

/-!

# List properties

This file contains useful definitions and lemmas about Lists and the additional
list operators defined in `Cedar.Data.List`.

-/

namespace List

open Cedar.Data

/-! ### Equiv -/

def Equiv {α} (a b : List α) : Prop :=
  a ⊆ b ∧ b ⊆ a

infix:50 " ≡ " => Equiv

theorem Equiv.refl {a : List α} :
  a ≡ a
:= by unfold List.Equiv; simp

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
  case left  => exact a h
  case right => exact b h

theorem filterMap_equiv (f : α → Option β) (xs ys : List α) :
  xs ≡ ys → xs.filterMap f ≡ ys.filterMap f
:= by
  simp only [Equiv, subset_def, mem_filterMap, forall_exists_index, and_imp]
  intros h₁ h₂
  apply And.intro <;>
  intro b a h₃ h₄ <;>
  exists a <;>
  simp only [h₄, and_true]
  case left  => exact h₁ h₃
  case right => exact h₂ h₃

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
      apply ih
      case _ =>
        cases h₁
        case cons_cons h₃ h₄ =>
          cases h₄
          case _ => exact SortedBy.cons_nil
          case cons_cons _ _ hd' tl' h₅ h₆ =>
            apply SortedBy.cons_cons _ h₅
            apply StrictLT.transitive (f x) (f hd) (f hd') h₃ h₆
      case _ => assumption

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
  case inr => assumption
  case inl _ h₅ =>
    subst h₅
    have h₆ := sortedBy_implies_head_lt_tail h₁ y h₄
    have h₇ := StrictLT.irreflexive (f y)
    contradiction

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
    case inl =>
      apply sortedBy_cons ih
      intro y h₂
      apply sortedBy_implies_head_lt_tail h₁
      rw [List.mem_filter] at h₂
      exact h₂.left
    case inr => exact ih

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
  List.Forall₂ (fun kv₁ kv₂ => kv₁.fst = kv₂.fst ∧ p kv₁.snd kv₂.snd) kvs₁ kvs₂


/-! ### insertCanonical -/

theorem insertCanonical_singleton [LT β] [DecidableLT β] (f : α → β)  (x : α) :
  insertCanonical f x [] = [x]
:= by unfold insertCanonical; rfl

theorem insertCanonical_not_nil [DecidableEq β] [LT β] [DecidableLT β] (f : α → β) (x : α) (xs : List α) :
  insertCanonical f x xs ≠ []
:= by
  unfold insertCanonical
  cases xs with
  | nil => simp
  | cons hd tl =>
    simp only [gt_iff_lt, ne_eq]
    intro h
    split at h <;> try trivial
    split at h <;> trivial

theorem insertCanonical_sortedBy [LT β] [StrictLT β] [DecidableLT β] {f : α → β} {xs : List α} (x : α) :
  SortedBy f xs →
  SortedBy f (insertCanonical f x xs)
:= by
  intro h₁
  induction xs
  case nil => simp [insertCanonical, SortedBy.cons_nil]
  case cons hd tl ih =>
    simp only [insertCanonical, gt_iff_lt]
    split
    case inl h₂ =>
      apply SortedBy.cons_cons h₂ h₁
    case inr h₂ =>
      split
      case inl h₃ =>
        cases h₁
        case cons_nil =>
          apply SortedBy.cons_cons h₃
          apply SortedBy.cons_nil
        case cons_cons y ys h₄ h₅ =>
          specialize ih h₄
          simp only [insertCanonical, gt_iff_lt]
          split
          case inl h₆ =>
            apply SortedBy.cons_cons h₃
            apply SortedBy.cons_cons h₆ h₄
          case inr h₆ =>
            split
            case inl h₇ =>
              apply SortedBy.cons_cons h₅
              simp only [insertCanonical, h₆, ↓reduceIte, gt_iff_lt, h₇] at ih
              exact ih
            case inr h₇ =>
              have h₈ := StrictLT.if_not_lt_gt_then_eq (f x) (f y) h₆ h₇
              apply SortedBy.cons_cons h₃
              cases h₄
              case cons_nil => exact SortedBy.cons_nil
              case cons_cons z zs h₉ h₁₀ =>
                apply SortedBy.cons_cons (by simp [h₈, h₁₀]) h₉
      case inr h₃ =>
        have h₄ := StrictLT.if_not_lt_gt_then_eq (f x) (f hd) h₂ h₃
        cases h₁
        case cons_nil => exact SortedBy.cons_nil
        case cons_cons h₅ h₆ =>
          exact SortedBy.cons_cons (by simp only [h₄, h₆]) h₅

theorem insertCanonical_cases [LT β] [DecidableLT β] (f : α → β) (x y : α) (ys : List α) :
  (f x < f y ∧ insertCanonical f x (y :: ys) = x :: y :: ys) ∨
  (¬ f x < f y ∧ f x > f y ∧ insertCanonical f x (y :: ys) = y :: insertCanonical f x ys) ∨
  (¬ f x < f y ∧ ¬ f x > f y ∧ insertCanonical f x (y :: ys) = x :: ys)
:= by
  generalize h₁ : insertCanonical f x ys = xys
  unfold insertCanonical
  simp only [gt_iff_lt, ite_eq_left_iff]
  by_cases (f x < f y)
  case pos _ _ h₂ => simp [h₂]
  case neg _ _ h₂ =>
    simp only [h₂, not_false_eq_true, forall_const, false_and, ↓reduceIte, true_and,
      ite_eq_right_iff, cons.injEq, false_or]
    by_cases (f x > f y)
    case pos _ _ h₃ => simp [h₃, h₁]
    case neg _ _ h₃ => simp [h₃]

theorem insertCanonical_subset [LT β] [DecidableLT β] (f : α → β) (x : α) (xs : List α) :
  insertCanonical f x xs ⊆ x :: xs
:= by
  induction xs
  case nil => simp only [insertCanonical, Subset.refl]
  case cons hd tl ih =>
    rcases (insertCanonical_cases f x hd tl) with h₁ | h₁ | h₁
    case inl => simp only [h₁, Subset.refl]
    case inr.inl =>
      simp only [h₁, cons_subset, mem_cons, true_or, or_true, true_and]
      apply Subset.trans ih
      simp only [cons_subset, mem_cons, true_or, true_and]
      exact Subset.trans (List.subset_cons hd tl) (List.subset_cons x (hd :: tl))
    case inr.inr =>
      simp only [h₁, cons_subset, mem_cons, true_or, true_and]
      exact Subset.trans (List.subset_cons hd tl) (List.subset_cons x (hd :: tl))

theorem insertCanonical_equiv [LT α] [StrictLT α] [DecidableLT α] (x : α) (xs : List α) :
  x :: xs ≡ insertCanonical id x xs
:= by
  unfold insertCanonical
  induction xs
  case nil => simp only ; exact Equiv.refl
  case cons hd tl ih =>
    simp only [id_eq, gt_iff_lt]
    split
    case inl => exact Equiv.refl
    case inr _ _ h₁ =>
      split
      case inr _ _ h₂ =>
        have h₃ := StrictLT.if_not_lt_gt_then_eq x hd h₁ h₂
        subst h₃
        exact dup_head_equiv x tl
      case inl _ _ h₂ =>
        cases tl
        case nil =>
          simp only [insertCanonical_singleton id x]
          apply swap_cons_cons_equiv
        case cons hd' tl' =>
          simp only [id_eq, gt_iff_lt] at ih
          have h₃ := insertCanonical_cases id x hd' tl'
          simp only [id_eq] at h₃
          cases h₃
          case inl _ _ _ h₃ =>
            simp only [h₃]
            unfold List.Equiv
            simp only [cons_subset, mem_cons, true_or, or_true, true_and]
            apply And.intro
            all_goals {
              simp only [subset_def, mem_cons]
              intro a h₄
              simp [h₄]
            }
          case inr _ _ _ h₃ =>
            cases h₃
            case inr _ _ _ h₃ =>
              replace ⟨h₃, h₄, h₅⟩ := h₃
              simp only [h₅]
              unfold GT.gt at h₄
              have h₆ := StrictLT.if_not_lt_gt_then_eq x hd' h₃ h₄
              subst h₆
              unfold List.Equiv
              simp
            case inl _ _ _ h₃ =>
              replace ⟨h₃, h₄, h₅⟩ := h₃
              simp only [h₅]
              simp only [h₃, h₄] at ih
              have h₆ := swap_cons_cons_equiv x hd (hd' :: tl')
              apply Equiv.trans h₆
              apply cons_equiv_cons
              exact ih

theorem insertCanonical_preserves_forallᵥ {α β γ} [LT α] [StrictLT α] [DecidableLT α] {p : β → γ → Prop}
  {kv₁ : α × β} {kv₂ : α × γ} {kvs₁ : List (α × β)} {kvs₂ : List (α × γ)}
  (h₁ : kv₁.fst = kv₂.fst ∧ p kv₁.snd kv₂.snd)
  (h₂ : Forallᵥ p kvs₁ kvs₂) :
  Forallᵥ p (insertCanonical Prod.fst kv₁ kvs₁) (insertCanonical Prod.fst kv₂ kvs₂)
:= by
  simp only [Forallᵥ] at *
  cases h₂
  case nil =>
    simp only [insertCanonical_singleton, forall₂_cons, Forall₂.nil, and_true]
    apply h₁
  case cons hd₁ hd₂ tl₁ tl₂ h₃ h₄ =>
    simp only [insertCanonical, gt_iff_lt]
    split <;> split
    case inl.inl =>
      apply Forall₂.cons (by exact h₁)
      apply Forall₂.cons (by exact h₃) (by exact h₄)
    case inl.inr h₅ h₆ =>
      simp only [h₁, h₃] at h₅
      have _ := StrictLT.asymmetric kv₂.fst hd₂.fst h₅
      split <;> contradiction
    case inr.inl h₅ h₆ =>
      simp only [h₁, h₃] at h₅ h₆
      split
      case inl => contradiction
      case inr =>
        apply Forall₂.cons (by exact h₃)
        apply insertCanonical_preserves_forallᵥ h₁ h₄
    case inr.inr h₅ h₆ =>
      simp only [h₁, h₃] at h₅ h₆
      split
      case inl => contradiction
      case inr => apply Forall₂.cons (by exact h₁) (by exact h₄)

theorem insertCanonical_map_fst {α β γ} [LT α] [StrictLT α] [DecidableLT α] (xs : List (α × β)) (f : β → γ) (x : α × β) :
  insertCanonical Prod.fst (Prod.map id f x) (map (Prod.map id f) xs) =
  map (Prod.map id f) (insertCanonical Prod.fst x xs)
:= by
  induction xs generalizing x
  case nil => simp [insertCanonical, canonicalize, Prod.map]
  case cons hd tl ih =>
    simp only [insertCanonical, Prod.map, id_eq, map_cons, gt_iff_lt]
    split
    case inl => simp [Prod.map]
    case inr =>
      split
      case inl =>
        specialize ih x
        simp only [Prod.map, id_eq] at ih
        simp [ih, Prod.map]
      case inr => simp [Prod.map]

theorem insertCanonical_map_fst_canonicalize {α β γ} [LT α] [StrictLT α] [DecidableLT α] (xs : List (α × β)) (f : β → γ) (x : α × β) :
  insertCanonical Prod.fst (Prod.map id f x) (canonicalize Prod.fst (map (Prod.map id f) xs)) =
  map (Prod.map id f) (insertCanonical Prod.fst x (canonicalize Prod.fst xs))
:= by
  induction xs generalizing x
  case nil => simp [insertCanonical, canonicalize, Prod.map]
  case cons hd tl ih =>
    simp only [canonicalize, ih hd]
    apply insertCanonical_map_fst (insertCanonical Prod.fst hd (canonicalize Prod.fst tl))

/-! ## canonicalize -/

theorem canonicalize_nil [LT β] [DecidableLT β] (f : α → β) :
  canonicalize f [] = []
:= by unfold canonicalize; rfl

theorem canonicalize_nil' [DecidableEq β] [LT β] [DecidableLT β] (f : α → β) (xs : List α) :
  xs = [] ↔ (canonicalize f xs) = []
:= by
  constructor
  case mp =>
    intro h₁ ; subst h₁
    exact canonicalize_nil f
  case mpr =>
    intro h₁
    cases xs with
    | nil => trivial
    | cons x xs =>
      exfalso
      unfold canonicalize at h₁
      apply insertCanonical_not_nil f x (canonicalize f xs)
      exact h₁

theorem canonicalize_not_nil [DecidableEq β] [LT β] [DecidableLT β] (f : α → β) (xs : List α) :
  xs ≠ [] ↔ (canonicalize f xs) ≠ []
:= by
  constructor
  case mp =>
    intro h₀
    cases xs with
    | nil => contradiction
    | cons hd tl =>
      unfold canonicalize
      apply insertCanonical_not_nil
  case mpr =>
    unfold canonicalize
    intro h₀
    cases xs <;> simp only [ne_eq, not_true_eq_false] at h₀; simp

theorem canonicalize_cons [LT β] [DecidableLT β] (f : α → β) (xs : List α) (a : α) :
  canonicalize f xs = canonicalize f ys → canonicalize f (a :: xs) = canonicalize f (a :: ys)
:= by
  intro h₁
  unfold canonicalize
  simp [h₁]

theorem canonicalize_sortedBy [LT β] [StrictLT β] [DecidableLT β] (f : α → β) (xs : List α) :
  SortedBy f (canonicalize f xs)
:= by
  induction xs
  case nil => simp [canonicalize_nil, SortedBy.nil]
  case cons hd tl ih =>
    unfold canonicalize
    apply insertCanonical_sortedBy
    exact ih

theorem sortedBy_implies_canonicalize_eq [LT β] [StrictLT β] [DecidableLT β] {f : α → β} {xs : List α} :
  SortedBy f xs → (canonicalize f xs) = xs
:= by
  intro h₁
  induction xs <;> simp only [canonicalize]
  case cons hd tl ih =>
    cases h₁
    case cons_nil => simp [canonicalize, insertCanonical]
    case cons_cons h₁ h₂ =>
      specialize ih h₁
      simp [ih, insertCanonical, h₂]

theorem canonicalize_subseteq [LT β] [StrictLT β] [DecidableLT β] (f : α → β) (xs : List α) :
  xs.canonicalize f ⊆ xs
:= by
  induction xs <;> simp only [canonicalize, Subset.refl]
  case cons hd tl ih =>
    have h := insertCanonical_subset f hd (canonicalize f tl)
    apply Subset.trans h
    simp only [cons_subset, mem_cons, true_or, true_and]
    apply Subset.trans ih
    simp

/-
Note that `canonicalize_equiv` does not hold for all functions `f`.
To see why, consider xs = [(1, false), (1, true)], f = Prod.fst.
Then `canonicalize f xs = [(1, false)] !≡ xs`.
-/
theorem canonicalize_equiv [LT α] [StrictLT α] [DecidableLT α] (xs : List α) :
  xs ≡ canonicalize id xs
:= by
  induction xs
  case nil => simp [canonicalize_nil, Equiv.refl]
  case cons hd tl ih =>
    unfold canonicalize
    generalize h₁ : canonicalize id tl = ys
    simp only [h₁] at ih
    have h₂ := insertCanonical_equiv hd ys
    apply Equiv.trans _ h₂
    apply cons_equiv_cons
    exact ih

theorem equiv_implies_canonical_eq [LT α] [StrictLT α] [DecidableLT α] (xs ys : List α) :
  xs ≡ ys → (canonicalize id xs) = (canonicalize id ys)
:= by
  intro h₁
  apply sortedBy_equiv_implies_eq id
  exact (canonicalize_sortedBy id xs)
  exact (canonicalize_sortedBy id ys)
  have h₂ := Equiv.symm (canonicalize_equiv xs)
  have h₃ := Equiv.symm (canonicalize_equiv ys)
  apply Equiv.trans h₂
  apply Equiv.symm
  apply Equiv.trans h₃
  apply Equiv.symm
  exact h₁

theorem canonicalize_idempotent {α β} [LT β] [StrictLT β] [DecidableLT β] (f : α → β) (xs : List α) :
  canonicalize f (canonicalize f xs) = canonicalize f xs
:= sortedBy_implies_canonicalize_eq (canonicalize_sortedBy f xs)

/-
Note that a more general version of `canonicalize_id_filter` does not hold.
In particular, we can't replace `id` with an arbitrary function `f`.
To see why, consider xs = [(1, false), (1, true)], f = Prod.fst, p = Prod.snd.
Then `(canonicalize f xs).filter p = []` but `(xs.filter p).canonicalize f = [(1, true)]`.

#eval (canonicalize Prod.fst [(1, false), (1, true)]).filter Prod.snd
#eval ([(1, false), (1, true)].filter Prod.snd).canonicalize Prod.fst
-/
theorem canonicalize_id_filter {α} [LT α] [StrictLT α] [DecidableLT α] (p : α → Bool) (xs : List α) :
  (canonicalize id xs).filter p = (xs.filter p).canonicalize id
:= by
  have h₁ : (canonicalize id xs).filter p ≡ xs.filter p := by
    apply filter_equiv
    apply Equiv.symm
    apply canonicalize_equiv
  have h₂ := canonicalize_equiv (filter p xs)
  exact sortedBy_equiv_implies_eq id
    (filter_sortedBy p (canonicalize_sortedBy id xs))
    (canonicalize_sortedBy id (filter p xs))
    (Equiv.trans h₁ h₂)

theorem canonicalize_preserves_forallᵥ {α β γ} [LT α] [StrictLT α] [DecidableLT α] (p : β → γ → Prop) (kvs₁ : List (α × β)) (kvs₂ : List (α × γ)) :
  List.Forallᵥ p kvs₁ kvs₂ →
  List.Forallᵥ p (List.canonicalize Prod.fst kvs₁) (List.canonicalize Prod.fst kvs₂)
:= by
  simp only [Forallᵥ]
  intro h₁
  cases h₁
  case nil => simp [canonicalize_nil]
  case cons hd₁ hd₂ tl₁ tl₂ h₂ h₃ =>
    simp only [canonicalize]
    have h₄ := canonicalize_preserves_forallᵥ p tl₁ tl₂ h₃
    apply insertCanonical_preserves_forallᵥ h₂ h₄

theorem canonicalize_of_map_fst {α β γ} [LT α] [StrictLT α] [DecidableLT α] (xs : List (α × β)) (f : β → γ) :
  List.canonicalize Prod.fst (List.map (Prod.map id f) xs) =
  List.map (Prod.map id f) (List.canonicalize Prod.fst xs)
:= by
  cases xs
  case nil => simp [canonicalize]
  case cons hd tl =>
    simp only [canonicalize]
    exact insertCanonical_map_fst_canonicalize tl f hd

/-! ### any -/

theorem any_of_mem {f : α → Bool} {x : α} {xs : List α}
  (h₁ : x ∈ xs)
  (h₂ : f x) :
  any xs f = true
:= by
  cases xs <;> simp only [mem_cons, not_mem_nil] at h₁
  case cons hd tl =>
    simp only [any_cons, Bool.or_eq_true, any_eq_true]
    rcases h₁ with h₁ | h₁
    subst h₁
    simp only [h₂, true_or]
    apply Or.inr
    exists x

/-! ### all -/

/--
  Copied from Mathlib. We can delete this if it gets added to Std.
-/
theorem all_pmap_subtype
  {p : α → Prop}
  (f : α → Bool)
  (as : List α)
  (h : ∀ a, a ∈ as → p a)
  : List.all (List.pmap Subtype.mk as h) (λ x : { a : α // p a } => f x.val)
    =
    List.all as f
:= by
  induction as <;> simp [*]

/-! ### map and map₁ -/

/--
  Copied from Mathlib. We can delete this if it gets added to Std.
-/
theorem map_congr {f g : α → β} : ∀ {l : List α},
  (∀ x ∈ l, f x = g x) → map f l = map g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [map, map, h₁, map_congr h₂]

/--
  Copied from Mathlib. We can delete this if it gets added to Std.
-/
theorem map_pmap_subtype
  {p : α → Prop}
  (f : α → β)
  (as : List α)
  (h : ∀ a, a ∈ as → p a)
  : List.map (λ x : { a : α // p a } => f x.val) (List.pmap Subtype.mk as h)
    =
    List.map f as
:= by
  induction as <;> simp [*]

/--
  Not actually a special case of `map_pmap_subtype` -- you can use this in
  places you can't use `map_pmap_subtype` because the LHS function (being
  mapped) doesn't fit the `map_pmap_subtype` form but does fit this form (where
  the application of `f` is not the outermost AST node of the function,
  basically)
-/
theorem map_pmap_subtype_snd
  {p : (α × β) → Prop}
  (f : β → γ)
  (xs : List (α × β))
  (h : ∀ pair ∈ xs, p pair)
  : List.map (λ x : { pair : (α × β) // p pair } => (x.val.fst, f x.val.snd)) (List.pmap Subtype.mk xs h)
    =
    xs.map λ pair => (pair.fst, f pair.snd)
:= by
  induction xs <;> simp [*]

theorem map₁_eq_map (f : α → β) (as : List α) :
  as.map₁ (λ x : {x // x ∈ as} => f x.val) =
  as.map f
:= by
  simp [map₁, attach, map_pmap_subtype]

theorem map_attach₂ {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {xs : List (α × β)} (f : (α × β) → γ) :
  xs.attach₂.map (λ x : { x : α × β // sizeOf x.snd < 1 + sizeOf xs } => f x.1) =
  xs.map f
:= by
  simp [attach₂, map_pmap_subtype]

/--
  Not actually a special case of `map_attach₂` -- you can use this in places you
  can't use `map_attach₂` because the LHS function (being mapped) doesn't fit
  the `map_attach₂` form but does fit this form (where the application of `f` is
  not the outermost AST node of the function, basically)
-/
theorem map_attach₂_snd {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {xs : List (α × β)} (f : β → γ) :
  xs.attach₂.map (λ x : {x : α × β // sizeOf x.snd < 1 + sizeOf xs } => match x with | ⟨(a, b), _⟩ => (a, f b)) =
  xs.map λ (a, b) => (a, f b)
:= by
  simp [attach₂, map_pmap_subtype_snd]

/-! ### Forall₂ -/

/--
  Copied from Mathlib
-/
theorem forall₂_nil_left_iff {l} : Forall₂ R nil l ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

/--
  Copied from Mathlib
-/
theorem forall₂_nil_right_iff {l} : Forall₂ R l nil ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

/--
  Copied from Mathlib
-/
theorem Forall₂.imp (H : ∀ a b, R a b → S a b) {l₁ l₂} (h : Forall₂ R l₁ l₂) : Forall₂ S l₁ l₂ := by
  induction h <;> constructor <;> solve_by_elim

/--
  Copied from Mathlib
-/
theorem forall₂_cons_left_iff {a l u} :
    Forall₂ R (a :: l) u ↔ ∃ b u', R a b ∧ Forall₂ R l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

/--
  Copied from Mathlib
-/
theorem forall₂_cons_right_iff {b l u} :
    Forall₂ R u (b :: l) ↔ ∃ a u', R a b ∧ Forall₂ R u' l ∧ u = a :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂

/--
  Note the converse is not true:
  counterexample `R` is `=`, `xs` is `[1]`, `ys` is `[1, 2]`
-/
theorem forall₂_implies_all_left {α β} {R : α → β → Prop} {xs : List α} {ys : List β} :
  List.Forall₂ R xs ys →
  ∀ x ∈ xs, ∃ y ∈ ys, R x y
:= by
  intro h
  induction h
  case nil =>
    simp only [not_mem_nil, false_and, exists_false, imp_self, implies_true]
  case cons xhd yhd xtl ytl hhd _ ih =>
    intro x hx
    simp only [mem_cons] at hx
    rcases hx with hx | hx
    case inl =>
      subst hx
      exists yhd
      simp only [mem_cons, true_or, hhd, and_self]
    case inr =>
      have ⟨y, ih⟩ := ih x hx
      exists y
      simp only [mem_cons, ih, or_true, and_self]

theorem forall₂_implies_all_right {α β} {R : α → β → Prop} {xs : List α} {ys : List β} :
  List.Forall₂ R xs ys →
  ∀ y ∈ ys, ∃ x ∈ xs, R x y
:= by
  intro h
  induction h
  case nil =>
    simp only [not_mem_nil, false_and, exists_false, imp_self, implies_true]
  case cons xhd yhd xtl ytl hhd _ ih =>
    intro y hy
    simp only [mem_cons] at hy
    rcases hy with hy | hy
    case inl =>
      subst hy
      exists xhd
      simp only [mem_cons, true_or, hhd, and_self]
    case inr =>
      have ⟨x, ih⟩ := ih y hy
      exists x
      simp only [mem_cons, ih, or_true, and_self]

/- not needed? -/
theorem forall₂_congr {R₁ R₂ : α → β → Prop} {as : List α} {bs : List β} :
  List.Forall₂ as bs (R := λ a b => R₁ a b ↔ R₂ a b) →
  List.Forall₂ R₁ as bs = List.Forall₂ R₂ as bs
:= by
  cases as <;> cases bs <;> simp
  case nil.cons hd tl | cons.nil hd tl =>
    simp [List.forall₂_nil_left_iff, List.forall₂_nil_right_iff]
  case cons.cons ahd atl bhd btl =>
    intro h₁ h₂
    have h₃ := forall₂_congr (as := atl) (bs := btl) h₂
    simp [h₃]
    intro _
    exact h₁

/-! ### mapM, mapM', and mapM₁ -/

/--
  `mapM` with a function that always produces `pure`
-/
theorem mapM_pure {α β} [Monad m] [LawfulMonad m] {f : α → β} {xs : List α} :
  xs.mapM ((λ a => pure (f a)) : α → m β) = pure (xs.map f)
:= by
  induction xs
  case nil => simp
  case cons hd tl ih => simp [ih]

theorem mapM_some {xs : List α} :
  xs.mapM some = some xs
:= by
  -- Probably could be proved as a corollary of `mapM_pure`, but I couldn't
  -- easily get that to work, and the direct inductive proof is very short
  induction xs
  case nil => simp
  case cons hd tl ih => simp [ih]

theorem mapM_map {α β γ} [Monad m] [LawfulMonad m] {f : α → β} {g : β → m γ} {xs : List α} :
  List.mapM g (xs.map f) = xs.mapM λ x => g (f x)
:= by
  induction xs
  case nil => simp
  case cons hd tl ih => simp [ih]

theorem mapM_pmap_subtype [Monad m] [LawfulMonad m]
  {p : α → Prop}
  (f : α → m β)
  (as : List α)
  (h : ∀ a, a ∈ as → p a)
  : List.mapM (λ x : { a : α // p a } => f x.val) (List.pmap Subtype.mk as h)
    =
    List.mapM f as
:= by
  rw [←List.mapM'_eq_mapM]
  induction as <;> simp [*]

theorem mapM₁_eq_mapM [Monad m] [LawfulMonad m]
  (f : α → m β)
  (as : List α) :
  List.mapM₁ as (λ x : { x // x ∈ as } => f x.val) =
  List.mapM f as
:= by
  simp [mapM₁, attach, mapM_pmap_subtype]

theorem mapM_implies_nil {f : α → Except β γ} {as : List α}
  (h₁ : List.mapM f as = Except.ok []) :
  as = []
:= by
  rw [←List.mapM'_eq_mapM] at h₁
  cases as
  case nil => rfl
  case cons hd tl =>
    simp only [List.mapM'] at h₁
    cases h₂ : f hd <;> simp only [h₂, Except.bind_err, Except.bind_ok] at h₁
    cases h₃ : List.mapM' f tl <;>
    simp [h₃, pure, Except.pure] at h₁

theorem mapM_head_tail {α β γ} {f : α → Except β γ} {x : α} {xs : List α} {y : γ} {ys : List γ} :
  (List.mapM f (x :: xs)) = Except.ok (y :: ys) →
  (List.mapM f xs) = Except.ok ys
:= by
  simp only [← mapM'_eq_mapM, mapM'_cons]
  cases h₁ : f x <;>
  simp only [h₁, Except.bind_ok, Except.bind_err, false_implies]
  cases h₂ : mapM' f xs <;>
  simp [h₂, pure, Except.pure]

theorem mapM'_ok_iff_forall₂ {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .ok ys ↔
  List.Forall₂ (λ x y => f x = .ok y) xs ys
:= by
  constructor
  case mp =>
    intro h₁
    induction xs generalizing ys
    case nil =>
      simp only [mapM'_nil, pure, Except.pure, Except.ok.injEq] at h₁
      subst h₁
      exact List.Forall₂.nil
    case cons xhd xtl ih =>
      simp only [mapM'_cons, pure, Except.pure] at h₁
      cases h₂ : f xhd <;>
      simp only [h₂, Except.bind_err, Except.bind_ok] at h₁
      rename_i yhd
      cases h₃ : mapM' f xtl <;>
      simp only [h₃, Except.bind_err, Except.bind_ok] at h₁
      rename_i ytl
      simp only [Except.ok.injEq] at h₁
      subst h₁
      exact List.Forall₂.cons h₂ (ih h₃)
  case mpr =>
    intro h₁
    induction xs generalizing ys
    case nil =>
      simp only [forall₂_nil_left_iff] at h₁
      simp only [mapM'_nil, pure, Except.pure, h₁]
    case cons xhd xtl ih =>
      simp only [mapM'_cons, pure, Except.pure]
      replace ⟨yhd, ytl, h₁, h₃, h₄⟩ := forall₂_cons_left_iff.mp h₁
      subst ys
      cases h₂ : f xhd
      case error e => simp [h₁] at h₂
      case ok y' =>
        simp [h₁] at h₂
        subst y'
        specialize @ih ytl h₃
        simp only [ih, Except.bind_err, Except.bind_ok]

theorem mapM_ok_iff_forall₂ {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM f xs = .ok ys ↔
  List.Forall₂ (λ x y => f x = .ok y) xs ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_ok_iff_forall₂

/--
  Note that the converse is not true:
  counterexample `xs` is `[1]`, `ys` is `[1, 2]`, `f` is `Except.ok`

  But for a limited converse, see `all_ok_implies_mapM'_ok`
-/
theorem mapM'_ok_implies_all_ok {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .ok ys →
  ∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y
:= by
  intro h
  exact forall₂_implies_all_left (mapM'_ok_iff_forall₂.mp h)

theorem mapM_ok_implies_all_ok {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM f xs = .ok ys →
  ∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_ok_implies_all_ok

theorem all_ok_implies_mapM'_ok {α β γ} {f : α → Except γ β} {xs : List α} :
  (∀ x ∈ xs, ∃ y, f x = .ok y) →
  ∃ ys, List.mapM' f xs = .ok ys
:= by
  intro h₁
  induction xs
  case nil => exists []
  case cons xhd xtl ih =>
    simp at h₁
    replace ⟨⟨yhd, h₁⟩, h₂⟩ := h₁
    replace ⟨ytl, ih⟩ := ih h₂
    exists yhd :: ytl
    simp [h₁, ih, pure, Except.pure]

theorem all_ok_implies_mapM_ok {α β γ} {f : α → Except γ β} {xs : List α} :
  (∀ x ∈ xs, ∃ y, f x = .ok y) →
  ∃ ys, List.mapM f xs = .ok ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact all_ok_implies_mapM'_ok

/--
  Note that the converse is not true:
  counterexample `ys` is `[1]`, `xs` is `[1, 2]`, `f` is `Except.ok`

  But for a limited converse, see `all_from_ok_implies_mapM'_ok`
-/
theorem mapM'_ok_implies_all_from_ok {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .ok ys →
  ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
:= by
  intro h
  exact forall₂_implies_all_right (mapM'_ok_iff_forall₂.mp h)

theorem mapM_ok_implies_all_from_ok {α β γ} {f : α → Except γ β} {xs : List α} {ys : List β} :
  List.mapM f xs = .ok ys →
  ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_ok_implies_all_from_ok

theorem all_from_ok_implies_mapM'_ok {α β γ} {f : α → Except γ β} {ys : List β} :
  (∀ y ∈ ys, ∃ x, f x = .ok y) →
  ∃ xs, List.mapM' f xs = .ok ys
:= by
  intro h₁
  induction ys
  case nil => exists []
  case cons yhd ytl ih =>
    simp at h₁
    replace ⟨⟨xhd, h₁⟩, h₂⟩ := h₁
    replace ⟨xtl, ih⟩ := ih h₂
    exists xhd :: xtl
    simp [h₁, ih, pure, Except.pure]

theorem all_from_ok_implies_mapM_ok {α β γ} {f : α → Except γ β} {ys : List β} :
  (∀ y ∈ ys, ∃ x, f x = .ok y) →
  ∃ xs, List.mapM f xs = .ok ys
:= by
  intro h
  have ⟨xs, h₂⟩ := all_from_ok_implies_mapM'_ok h
  rw [List.mapM'_eq_mapM] at h₂
  exists xs

theorem mapM'_some_iff_forall₂ {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .some ys ↔
  List.Forall₂ (λ x y => f x = .some y) xs ys
:= by
  constructor
  case mp =>
    intro h₁
    induction xs generalizing ys
    case nil =>
      simp only [mapM'_nil, pure, Option.some.injEq] at h₁
      subst h₁
      exact List.Forall₂.nil
    case cons xhd xtl ih =>
      simp only [mapM'_cons, pure, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h₁
      replace ⟨yhd, h₁, ytl, h₂, h₃⟩ := h₁
      subst h₃
      exact List.Forall₂.cons h₁ (ih h₂)
  case mpr =>
    intro h₁
    induction xs generalizing ys
    case nil =>
      simp only [forall₂_nil_left_iff] at h₁
      simp only [mapM'_nil, pure, Except.pure, h₁]
    case cons xhd xtl ih =>
      simp only [mapM'_cons, pure, Except.pure]
      replace ⟨yhd, ytl, h₁, h₃, h₄⟩ := forall₂_cons_left_iff.mp h₁
      subst ys
      cases h₂ : f xhd
      case none => simp [h₁] at h₂
      case some y' =>
        simp [h₁] at h₂
        subst y'
        simp [@ih ytl h₃]

theorem mapM_some_iff_forall₂ {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM f xs = .some ys ↔
  List.Forall₂ (λ x y => f x = .some y) xs ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_some_iff_forall₂

/--
  Note that the converse is not true:
  counterexample `xs` is `[1]`, `ys` is `[1, 2]`, `f` is `Option.some`
-/
theorem mapM'_some_implies_all_some {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .some ys →
  ∀ x ∈ xs, ∃ y ∈ ys, f x = .some y
:= by
  intro h
  exact forall₂_implies_all_left (mapM'_some_iff_forall₂.mp h)

theorem mapM_some_implies_all_some {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM f xs = .some ys →
  ∀ x ∈ xs, ∃ y ∈ ys, f x = .some y
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_some_implies_all_some

/--
  Note that the converse is not true:
  counterexample `ys` is `[1]`, `xs` is `[1, 2]`, `f` is `Option.some`
-/
theorem mapM'_some_implies_all_from_some {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .some ys →
  ∀ y ∈ ys, ∃ x ∈ xs, f x = .some y
:= by
  intro h
  exact forall₂_implies_all_right (mapM'_some_iff_forall₂.mp h)

theorem mapM_some_implies_all_from_some {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM f xs = .some ys →
  ∀ y ∈ ys, ∃ x ∈ xs, f x = .some y
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_some_implies_all_from_some

theorem mapM'_none_iff_exists {α β} {f : α → Option β} {xs : List α} :
  List.mapM' f xs = none ↔ ∃ x ∈ xs, f x = none
:= by
  constructor
  case mp =>
    intro h₁
    cases xs
    case nil => simp at h₁
    case cons xhd xtl =>
      cases h₂ : f xhd <;> simp [h₂]
      case some yhd =>
        simp [h₂] at h₁
        apply mapM'_none_iff_exists.mp
        by_contra h₃
        rw [← ne_eq] at h₃
        replace ⟨ytl, h₃⟩ := Option.ne_none_iff_exists'.mp h₃
        exact h₁ ytl h₃
  case mpr =>
    intro h₁
    replace ⟨x, h₁, h₂⟩ := h₁
    cases xs <;> simp at h₁
    case cons xhd xtl =>
      simp
      intro yhd h₃ ytl h₄
      rcases h₁ with h₁ | h₁
      case inl => subst h₁ ; simp [h₂] at h₃
      case inr =>
        replace h₄ := mapM'_some_implies_all_some h₄
        replace ⟨y, _, h₅⟩ := h₄ x h₁
        simp [h₂] at h₅

theorem mapM_none_iff_exists {α β} {f : α → Option β} {xs : List α} :
  List.mapM f xs = none ↔ ∃ x ∈ xs, f x = none
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_none_iff_exists

theorem mapM'_some_eq_filterMap {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM' f xs = .some ys →
  List.filterMap f xs = ys
:= by
  intro h
  induction xs generalizing ys
  case nil =>
    simp only [mapM'_nil, Option.pure_def, Option.some.injEq, filterMap_nil] at *
    exact h
  case cons hd tl ih =>
    simp only [filterMap_cons]
    simp only [mapM'_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
      Option.some.injEq] at h
    replace ⟨hd', h, tl', hm, hys⟩ := h
    subst hys
    simp only [h, cons.injEq, true_and]
    exact ih hm

theorem mapM_some_eq_filterMap {α β} {f : α → Option β} {xs : List α} {ys : List β} :
  List.mapM f xs = .some ys →
  List.filterMap f xs = ys
:= by
  rw [← List.mapM'_eq_mapM]
  exact mapM'_some_eq_filterMap

/-! ### foldlM -/

theorem foldlM_of_assoc_some (f : α → α → Option α) (x₀ x₁ x₂ x₃ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄))
  (h₂ : f x₀ x₁ = some x₂)
  (h₃ : List.foldlM f x₂ xs = some x₃):
  (do let y ← List.foldlM f x₁ xs ; f x₀ y) = some x₃
:= by
  cases xs
  case nil =>
    simp only [Option.bind_eq_bind, List.foldlM, pure, Option.some.injEq, Option.bind_some_fun] at *
    subst h₃; exact h₂
  case cons hd tl =>
    simp only [Option.bind_eq_bind, List.foldlM, Option.bind_eq_some] at *
    cases h₄ : f x₂ hd <;> simp only [h₄, false_and, exists_false, Option.some.injEq, exists_eq_left'] at h₃
    case some x₄ =>
    have h₅ := h₁ x₀ x₁ hd
    simp only [h₂, h₄, Option.some_bind] at h₅
    cases h₆ : f x₁ hd <;> simp only [h₆, Option.some_bind, Option.none_bind] at h₅
    case some x₅ =>
    have h₇ := List.foldlM_of_assoc_some f x₂ hd x₄ x₃ tl h₁ h₄ h₃
    cases h₈ : List.foldlM f hd tl <;> simp only [h₈, Option.bind_some_fun, Option.bind_none_fun] at h₇
    case some x₆ =>
    rw [eq_comm] at h₅
    cases h₉ : List.foldlM f x₅ tl <;> simp only [h₉, Option.some.injEq, exists_eq_left', false_and, exists_false]
    case none =>
      have h₁₀ := List.foldlM_of_assoc_some f x₀ x₅ x₄ x₃ tl h₁ h₅ h₃
      simp [h₉] at h₁₀
    case some x₇ =>
      have h₁₀ := List.foldlM_of_assoc_some f x₁ hd x₅ x₇ tl h₁ h₆ h₉
      simp only [h₈, Option.bind_some_fun] at h₁₀
      specialize h₁ x₀ x₁ x₆
      simp only [h₂, h₁₀, Option.some_bind] at h₁
      simp [←h₁, h₇]

theorem foldlM_of_assoc_none' (f : α → α → Option α) (x₀ x₁ x₂ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄))
  (h₂ : f x₀ x₁ = none)
  (h₃ : List.foldlM f x₁ xs = some x₂):
  f x₀ x₂ = none
:= by
  cases xs
  case nil =>
    simp only [foldlM_nil, pure, Option.some.injEq] at h₃ ; subst h₃; exact h₂
  case cons hd tl =>
    simp only [List.foldlM, Option.bind_eq_bind, Option.bind_eq_some] at h₃
    cases h₄ : f x₁ hd <;> simp only [h₄, false_and, exists_false, Option.some.injEq, exists_eq_left'] at h₃
    case some x₃ =>
    have h₅ := List.foldlM_of_assoc_some f x₁ hd x₃ x₂ tl h₁ h₄ h₃
    cases h₆ : List.foldlM f hd tl <;> simp only [h₆, Option.bind_some_fun, Option.bind_none_fun] at h₅
    case some x₄ =>
    specialize h₁ x₀ x₁ x₄
    simp only [h₂, h₅, Option.bind_none_fun, Option.bind_some_fun] at h₁
    simp [h₁]

theorem foldlM_of_assoc_none (f : α → α → Option α) (x₀ x₁ x₂ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄))
  (h₂ : f x₀ x₁ = some x₂)
  (h₃ : List.foldlM f x₂ xs = none):
  (do let y ← List.foldlM f x₁ xs ; f x₀ y) = none
:= by
  cases xs
  case nil => simp [List.foldlM] at h₃
  case cons hd tl =>
    simp only [List.foldlM, Option.bind_eq_bind, Option.bind_eq_none, Option.bind_eq_some,
      forall_exists_index, and_imp]
    cases h₄ : f x₁ hd <;> simp only [false_implies, implies_true, Option.some.injEq, forall_eq']
    case some x₃ =>
    cases h₅ : List.foldlM f x₃ tl <;> simp only [false_implies, implies_true, Option.some.injEq, forall_eq']
    case some x₄ =>
    have h₆ := List.foldlM_of_assoc_some f x₁ hd x₃ x₄ tl h₁ h₄ h₅
    cases h₇ : List.foldlM f hd tl <;> simp only [h₇, Option.bind_some_fun, Option.bind_none_fun] at h₆
    case some x₅ =>
    simp only [List.foldlM, Option.bind_eq_bind, Option.bind_eq_none] at h₃
    cases h₈ : f x₂ hd <;> simp only [h₈, false_implies, implies_true, Option.some.injEq, forall_eq'] at h₃
    case none =>
      have h₉ := List.foldlM_of_assoc_none' f x₂ hd x₅ tl h₁ h₈ h₇
      have h₁₀ := h₁ x₀ x₁ x₅
      simp only [h₂, h₆, Option.bind_some_fun] at h₁₀
      simp [←h₁₀, h₉]
    case some x₆ =>
      have h₉ := List.foldlM_of_assoc_none f x₂ hd x₆ tl h₁ h₈ h₃
      simp only [h₇, Option.bind_some_fun] at h₉
      have h₁₀ := h₁ x₀ x₁ x₅
      simp only [h₂, h₆, Option.bind_some_fun] at h₁₀
      simp [←h₁₀, h₉]

theorem foldlM_of_assoc (f : α → α → Option α) (x₀ x₁ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄) ) :
  List.foldlM f x₀ (x₁ :: xs) =
  (do let y ← List.foldlM f x₁ xs ; f x₀ y)
:= by
  simp only [List.foldlM, Option.bind_eq_bind]
  cases h₂ : f x₀ x₁ <;> simp only [Option.some_bind, Option.none_bind]
  case none =>
    induction xs generalizing x₁
    case nil => simp [h₂]
    case cons hd tl ih =>
      simp only [List.foldlM, Option.bind_eq_bind]
      cases h₃ : f x₁ hd <;> simp only [Option.some_bind, Option.none_bind]
      case some x₂ =>
      apply ih x₂
      specialize h₁ x₀ x₁ hd
      simp only [h₂, h₃, Option.bind_some_fun, Option.bind_none_fun] at h₁
      rw [eq_comm] at h₁ ; exact h₁
  case some x₂ =>
    rw [eq_comm]
    cases h₃ : List.foldlM f x₂ xs
    case none =>
      exact List.foldlM_of_assoc_none f x₀ x₁ x₂ xs h₁ h₂ h₃
    case some x₃ =>
      exact List.foldlM_of_assoc_some f x₀ x₁ x₂ x₃ xs h₁ h₂ h₃

/-! ### find? -/

theorem find?_pair_map {α β γ} [BEq α] (f : β → γ) (xs : List (α × β)) (k : α)  :
  Option.map (λ x => (x.fst, f x.snd)) (List.find? (λ x => x.fst == k) xs)  =
  List.find? (λ x => x.fst == k) (List.map (λ x => (x.fst, f x.snd)) xs)
:= by
  induction xs
  case nil => simp
  case cons hd tl ih =>
    cases h₁ : hd.fst == k <;> simp only [map_cons]
    case false =>
      rw [Bool.eq_false_iff, ne_eq] at h₁
      have h₂ := @List.find?_cons_of_neg _
        (λ (x : α × β) => x.fst == k) hd tl h₁
      have h₃ := @List.find?_cons_of_neg _
        (λ (x : α × γ) => x.fst == k) (hd.fst, f hd.snd)
        (map (λ x => (x.fst, f x.snd)) tl)
      simp only [h₁, not_false_eq_true, forall_const] at h₃
      simp only [h₂, h₃]
      exact ih
    case true =>
      have h₂ := @List.find?_cons_of_pos _
        (λ (x : α × β) => x.fst == k) hd tl h₁
      have h₃ := @List.find?_cons_of_pos _
        (λ (x : α × γ) => x.fst == k) (hd.fst, f hd.snd)
        (map (λ x => (x.fst, f x.snd)) tl)
      simp only [h₁, forall_const] at h₃
      simp [h₂, h₃]

theorem find?_fst_map_implies_find? {α β γ} [BEq α] {f : β → γ} {xs : List (α × β)} {k : α} {fx : α × γ}:
  List.find? (λ x => x.fst == k) (List.map (Prod.map id f) xs) = .some fx  →
  ∃ x, xs.find? (λ x => x.fst == k) = .some x ∧ fx = Prod.map id f x
:= by
  intro h
  induction xs
  case nil => simp at h
  case cons hd tl ih =>
    simp only [map_cons, find?_cons] at h
    split at h
    case h_1 heq =>
      exists hd
      simp only [Option.some.injEq] at h
      simp only [h, and_true]
      simp only [Prod.map, id_eq] at heq
      simp only [find?_cons, heq]
    case h_2 heq =>
      replace ⟨x, ih⟩ := ih h
      exists x
      simp only [Prod.map, id_eq] at heq
      simp [find?_cons, heq, ih]

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
    split
    case h_1 heq =>
      simp only [beq_iff_eq] at heq
      simp only [Option.some.injEq]
      rcases h₁ with h₁ | h₁
      case inl => simp only [h₁]
      case inr =>
        have h₃ := sortedBy_implies_head_lt_tail h₂
        specialize h₃ x h₁
        simp only [heq, StrictLT.irreflexive] at h₃
    case h_2 heq =>
      simp only [beq_eq_false_iff_ne, ne_eq] at heq
      rcases h₁ with h₁ | h₁
      case inl =>
        simp only [h₁, not_true_eq_false] at heq
      case inr =>
        exact ih h₁ (tail_sortedBy h₂)

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
    rcases hx with hx | hx <;>
    rcases hy with hy | hy
    case inl.inl => simp only [hx, hy]
    case inr.inr => exact ih hx hy
    case inl.inr =>
      subst hx
      specialize hlt y hy
      simp only [hf, StrictLT.irreflexive] at hlt
    case inr.inl =>
      subst hy
      specialize hlt x hx
      simp only [hf, StrictLT.irreflexive] at hlt

/-! ### filterMap -/

/--
  our own variant of map_congr, for filterMap
-/
theorem filterMap_congr {f g : α → Option β} : ∀ {l : List α},
  (∀ x ∈ l, f x = g x) → filterMap f l = filterMap g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [filterMap, filterMap, h₁, filterMap_congr h₂]

theorem filterMap_empty_iff_all_none {f : α → Option β} {xs : List α} :
  xs.filterMap f = [] ↔ ∀ x ∈ xs, f x = none
:= by
  constructor
  case mp =>
    induction xs
    case nil => simp
    case cons hd tl ih =>
      intro h₁ a h₂
      simp only [List.filterMap_cons] at h₁
      split at h₁ <;> try simp only at h₁
      case h_1 h₃ =>
        rcases (List.mem_cons.mp h₂) with h₄ | h₄
        case inl => subst h₄ ; assumption
        case inr => apply ih h₁ a ; assumption
  case mpr =>
    intro h₁
    induction xs
    case nil => simp
    case cons hd tl ih =>
      simp only [List.filterMap_cons]
      split
      case h_1 =>
        apply ih ; clear ih
        intro a h₂
        apply h₁ a
        exact List.mem_cons_of_mem hd h₂
      case h_2 b h₂ =>
        exfalso
        specialize h₁ hd
        simp only [mem_cons, true_or, forall_const] at h₁
        simp [h₁] at h₂

theorem filterMap_nonempty_iff_exists {f : α → Option β} {xs : List α} :
  xs.filterMap f ≠ [] ↔ ∃ x ∈ xs, (f x).isSome
:= by
  constructor
  case mp =>
    intro h₁
    replace ⟨b, h₁⟩ := List.exists_mem_of_ne_nil (xs.filterMap f) h₁
    replace ⟨x, h₁⟩ := (List.mem_filterMap f xs).mp h₁
    exists x
    simp [h₁, Option.isSome]
  case mpr =>
    intro h₁ h₂
    rw [filterMap_empty_iff_all_none] at h₂
    replace ⟨x, h₁, h₃⟩ := h₁
    specialize h₂ x h₁
    simp [h₂, Option.isSome] at h₃

theorem f_implies_g_then_subset {f g : α → Option β} {xs : List α} :
  (∀ a b, f a = some b → g a = some b) →
  xs.filterMap f ⊆ xs.filterMap g
:= by
  intro h₁
  simp only [subset_def, mem_filterMap, forall_exists_index, and_imp]
  intro b a h₂ h₃
  exists a
  apply And.intro h₂
  exact h₁ a b h₃

end List
