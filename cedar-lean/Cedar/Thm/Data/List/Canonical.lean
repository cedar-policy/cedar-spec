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

import Cedar.Thm.Data.List.Basic

/-!

# Properties of list canonicalization

This file contains lemmas about list canonicalization.

-/

namespace List

open Cedar.Data

/-! ### insertCanonical -/

theorem insertCanonical_singleton [LT β] [DecidableLT β] (f : α → β)  (x : α) :
  insertCanonical f x [] = [x]
:= by unfold insertCanonical; rfl

theorem insertCanonical_not_nil [DecidableEq β] [LT β] [DecidableLT β] (f : α → β) (x : α) (xs : List α) :
  insertCanonical f x xs ≠ []
:= by
  unfold insertCanonical
  cases xs
  case nil => simp only [ne_eq, not_false_eq_true]
  case cons hd tl =>
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
    split <;> rename_i h₂
    · exact SortedBy.cons_cons h₂ h₁
    · split
      case inl h₃ =>
        cases h₁
        case cons_nil =>
          apply SortedBy.cons_cons h₃
          apply SortedBy.cons_nil
        case cons_cons y ys h₄ h₅ =>
          specialize ih h₄
          simp only [insertCanonical, gt_iff_lt]
          split <;> rename_i h₆
          · apply SortedBy.cons_cons h₃
            exact SortedBy.cons_cons h₆ h₄
          · split <;> rename_i h₇
            · apply SortedBy.cons_cons h₅
              simp only [insertCanonical, h₆, ↓reduceIte, gt_iff_lt, h₇] at ih
              exact ih
            · have h₈ := StrictLT.if_not_lt_gt_then_eq (f x) (f y) h₆ h₇
              apply SortedBy.cons_cons h₃
              cases h₄
              case cons_nil => exact SortedBy.cons_nil
              case cons_cons z zs h₉ h₁₀ =>
                exact SortedBy.cons_cons (by simp [h₈, h₁₀]) h₉
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
    · simp only [h₁, Subset.refl]
    · simp only [h₁, cons_subset, mem_cons, true_or, or_true, true_and]
      apply Subset.trans ih
      simp only [cons_subset, mem_cons, true_or, true_and]
      exact Subset.trans (List.subset_cons hd tl) (List.subset_cons x (hd :: tl))
    · simp only [h₁, cons_subset, mem_cons, true_or, true_and]
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
          cases h₃ <;> rename_i h₃
          case inl =>
            simp only [h₃]
            unfold List.Equiv
            simp only [cons_subset, mem_cons, true_or, or_true, true_and]
            apply And.intro
            all_goals {
              simp only [subset_def, mem_cons]
              intro a h₄
              simp [h₄]
            }
          case inr =>
            cases h₃ <;> rename_i h₃
            case inr =>
              replace ⟨h₃, h₄, h₅⟩ := h₃
              simp only [h₅]
              unfold GT.gt at h₄
              have h₆ := StrictLT.if_not_lt_gt_then_eq x hd' h₃ h₄
              subst h₆
              unfold List.Equiv
              simp only [cons_subset, mem_cons, true_or, or_true, Subset.refl, and_self,
                subset_cons]
            case inl =>
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
    split <;> split <;> rename_i h₅ h₆
    · apply Forall₂.cons (by exact h₁)
      exact Forall₂.cons (by exact h₃) (by exact h₄)
    · simp only [h₁, h₃] at h₅
      have _ := StrictLT.asymmetric kv₂.fst hd₂.fst h₅
      split <;> contradiction
    · simp only [h₁, h₃] at h₅ h₆
      split
      · contradiction
      · apply Forall₂.cons (by exact h₃)
        exact insertCanonical_preserves_forallᵥ h₁ h₄
    · simp only [h₁, h₃] at h₅ h₆
      split
      · contradiction
      · exact Forall₂.cons (by exact h₁) (by exact h₄)

theorem insertCanonical_map_fst {α β γ} [LT α] [StrictLT α] [DecidableLT α] (xs : List (α × β)) (f : β → γ) (x : α × β) :
  insertCanonical Prod.fst (Prod.map id f x) (map (Prod.map id f) xs) =
  map (Prod.map id f) (insertCanonical Prod.fst x xs)
:= by
  induction xs generalizing x
  case nil => simp [insertCanonical, canonicalize, Prod.map]
  case cons hd tl ih =>
    simp only [insertCanonical, Prod.map, id_eq, map_cons, gt_iff_lt]
    split
    · simp [Prod.map]
    · split
      · specialize ih x
        simp only [Prod.map, id_eq] at ih
        simp [ih, Prod.map]
      · simp [Prod.map]

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
    cases xs <;> simp only [ne_eq, not_true_eq_false, not_false_eq_true] at *

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
    simp only [subset_cons]

/-- Corollary of `canonicalize_subseteq` -/
theorem in_canonicalize_in_list [LT β] [StrictLT β] [DecidableLT β] {f : α → β} {x : α} {xs : List α} :
  x ∈ xs.canonicalize f → x ∈ xs
:= by
  intro h₁
  have h₂ := canonicalize_subseteq f xs
  simp [List.subset_def] at h₂
  exact h₂ h₁

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

/-
Note that `equiv_implies_canonical_eq` does not hold for all functions `f`.
To see why, consider the `example` immediately below this.
-/
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

/--
  Illustration that `equiv_implies_canonical_eq` does not hold for
  all functions `f` -- in particular, does not hold for `Prod.fst`.

  (One `canonicalize` produces `[(1, false)]`, and the other
  produces `[(1, true)]`.)
-/
example :
  xs = [(1, false), (1, true)] →
  ys = [(1, true), (1, false)] →
  xs ≡ ys ∧ (canonicalize Prod.fst xs) ≠ (canonicalize Prod.fst ys)
:= by
  intro h₁ h₂
  subst h₁ h₂
  simp [List.Equiv]
  decide

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

end List
