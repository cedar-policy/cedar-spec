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

import Cedar.Data.List
import Cedar.Spec

/-!
This file contains useful lemmas about Std and List functions.
-/

namespace Cedar.Thm

open Cedar.Data

/--
  A generic lemma that relates List.mapM to List.map. Not in Std AFAICT.
-/
theorem if_f_produces_pure_then_mapM_f_is_pure_map {α β} [Monad m] [LawfulMonad m] {f : α → β} {xs : List α} :
  xs.mapM ((fun a => pure (f a)) : α → m β) = pure (xs.map f)
:= by
  induction xs
  case nil => simp
  case cons x xs h => simp [h]

/--
  A generic lemma about composing List.mapM with List.map. Not in Std AFAICT.
-/
theorem mapM_map {α β γ} [Monad m] [LawfulMonad m] {f : α → β} {g : β → m γ} {xs : List α} :
  List.mapM g (xs.map f) = xs.mapM fun x => g (f x)
:= by
  induction xs
  case nil => simp
  case cons x xs h => simp [h]

/--
  A generic lemma about the behavior of List.mapM in the Option monad
-/
theorem mapM_some_iff_f_some_on_all_elements {f : α → Option β} {xs : List α} :
  Option.isSome (xs.mapM f) ↔ ∀ x ∈ xs, Option.isSome (f x)
:= by
  rw [← List.mapM'_eq_mapM]
  constructor
  case mp =>
    induction xs
    case nil => simp
    case cons x xs h_ind =>
      simp [List.mapM'_cons]
      intro h₁
      unfold List.mapM' at h₁
      constructor
      case left =>
        cases h₂ : (f x) <;> simp [h₂] at h₁
        simp
      case right =>
        intro a
        apply h_ind
        rw [Option.isSome_iff_exists] at h₁
        replace ⟨xs₁, h₁⟩ := h₁
        cases h₂ : (f x) <;> simp [h₂] at h₁
        replace ⟨xs₂, ⟨h₁, h₂⟩⟩ := h₁
        simp [Option.bind] at h₁
        sorry
  case mpr =>
    intro h
    induction xs
    case nil => simp [List.mapM']
    case cons y ys h_ind =>
      have h₂ := h y ; simp at h₂
      rw [List.mapM'_cons]
      sorry

/--
  Corollary of the above
-/
theorem mapM_none_iff_f_none_on_some_element {f : α → Option β} {xs : List α} :
  xs.mapM f = none ↔ ∃ x ∈ xs, f x = none
:= by
  constructor
  case mp =>
    intro h₁
    by_contra h₂
    replace h₂ := forall_not_of_not_exists h₂
    simp only [not_and] at h₂
    rw [← Option.not_isSome_iff_eq_none] at h₁
    rw [mapM_some_iff_f_some_on_all_elements] at h₁
    apply h₁ ; clear h₁
    intro x h₁
    specialize h₂ x h₁
    rw [← ne_eq] at h₂
    rw [Option.ne_none_iff_isSome] at h₂
    exact h₂
  case mpr =>
    intro h₁
    replace ⟨x, h₁, h₂⟩ := h₁
    rw [← Option.not_isSome_iff_eq_none]
    intro h₃
    rw [mapM_some_iff_f_some_on_all_elements] at h₃
    specialize h₃ x h₁
    simp [h₂] at h₃

/--
  A generic lemma about the behavior of List.mapM in the Except monad
-/
theorem mapM_ok_iff_f_ok_on_all_elements {f : α → Except ε β} {xs : List α} :
  Except.isOk (xs.mapM f) ↔ ∀ x ∈ xs, Except.isOk (f x)
:= by
  rw [← List.mapM'_eq_mapM]
  simp [Except.isOk, Except.toBool]
  constructor
  case mp =>
    induction xs
    case nil =>
      intro _ x h₂
      simp at h₂
    case cons y ys h_ind =>
      intro h₁ x h₂
      unfold List.mapM' at h₁
      cases h₄ : (f y) <;> simp [h₄] at h₁
      case error => cases h₁
      case ok b =>
        rcases (List.mem_cons.mp h₂) with h₅ | h₅
        case inl => rw [← h₅] at h₄; simp [h₄]
        case inr =>
          apply h_ind ; clear h_ind
          case a =>
            split at h₁ <;> split <;> simp
            case h_1.h_2 h₅ _ _ h₆ =>
              simp [h₆] at h₅
              cases h₅
            case h_2.h_2 => simp at h₁
          case a => exact h₅
  case mpr =>
    induction xs
    case nil => simp [List.mapM', pure, Except.pure]
    case cons x xs h_ind =>
      intro h₂
      split <;> simp
      case h_2 err h₃ =>
        cases h₄ : (f x) <;> simp [h₄] at h₂
        case ok b =>
          specialize h_ind h₂
          split at h_ind <;> simp at h_ind
          case h_1 err h₆ =>
            simp [h₄, h₆, List.mapM', pure, Except.pure] at h₃
            cases h₃

/--
  Another generic lemma about the behavior of List.mapM in the Option monad
-/
theorem mem_mapM_some {f : α → Option β} {xs : List α} {y : β} :
  xs.mapM f = some ys → y ∈ ys → ∃ x ∈ xs, f x = some y
:= by
  sorry

/--
  Another generic lemma about the behavior of List.mapM in the Except monad
-/
theorem mem_mapM_ok {f : α → Except ε β} {xs : List α} {y : β} :
  xs.mapM f = .ok ys → y ∈ ys → ∃ x ∈ xs, f x = .ok y
:= by
  sorry
