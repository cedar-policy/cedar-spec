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
import Cedar.Thm.Data.Control

namespace List

open Cedar.Data

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

end List
