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
import Cedar.Thm.Data.List.Sorted

namespace List

open Cedar.Data

/-! ### find? -/

theorem find?_pair_map {α β γ} [BEq α] (f : β → γ) (xs : List (α × β)) (k : α)  :
  Option.map (λ x => (x.fst, f x.snd)) (List.find? (λ x => x.fst == k) xs)  =
  List.find? (λ x => x.fst == k) (List.map (λ x => (x.fst, f x.snd)) xs)
:= by
  induction xs
  case nil => simp only [find?_nil, Option.map_none', map_nil]
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
    split at h <;> rename_i heq
    · exists hd
      simp only [Option.some.injEq] at h
      simp only [h, and_true]
      simp only [Prod.map, id_eq] at heq
      simp only [find?_cons, heq]
    · replace ⟨x, ih⟩ := ih h
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

end List
