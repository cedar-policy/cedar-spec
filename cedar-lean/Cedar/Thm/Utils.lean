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
  A generic lemma about the behavior of List.mapM in the Option monad

  The `mp` direction is a corollary of `mapM_eq_some` below, if we ever prove that
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
  Analogue of `mapM_some_iff_f_some_on_all_elements` for Map.mapMOnValues
-/
theorem mapMOnValues_some_iff_f_some_on_all_values [LT α] [DecidableLT α] {f : β → Option γ} {m : Map α β} :
  Option.isSome (m.mapMOnValues f) ↔ ∀ v ∈ m.values, Option.isSome (f v)
:= by
  constructor
  case mp =>
    sorry
  case mpr =>
    sorry

/--
  A generic lemma about the behavior of List.mapM in the Option monad.
-/
theorem mapM_eq_some {f : α → Option β} {xs : List α} {ys : List β} {x : α} :
  (xs.mapM f = some ys) → x ∈ xs → ∃ y ∈ ys, f x = some y
:= by
  rw [← List.mapM'_eq_mapM]
  intro h₁ h₂
  sorry

/--
  Corollary of `mapM_some_iff_f_some_on_all_elements`
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
  Analogue of `mapM_eq_some` for Map.mapMOnValues in the Option monad
-/
theorem mapMOnValues_eq_some [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} {k : α} {v : β} :
  (m₁.mapMOnValues f = some m₂) → (k, v) ∈ m₁.kvs → ∃ v', (k, v') ∈ m₂.kvs ∧ f v = some v'
:= by
  intro h₁ h₂
  sorry

/--
  Analogue of `mapM_none_iff_f_none_on_some_element` for Map.mapMOnValues

  Corollary of `mapMOnValues_some_iff_f_some_on_all_values`
-/
theorem mapMOnValues_none_iff_f_none_on_some_value [LT α] [DecidableLT α] {f : β → Option γ} {m : Map α β} :
  m.mapMOnValues f = none ↔ ∃ v ∈ m.values, f v = none
:= by
  -- As of this writing, this proof is nearly syntactically identical to the
  -- proof of `mapM_none_iff_f_none_on_some_element`
  constructor
  case mp =>
    intro h₁
    by_contra h₂
    replace h₂ := forall_not_of_not_exists h₂
    simp only [not_and] at h₂
    rw [← Option.not_isSome_iff_eq_none] at h₁
    rw [mapMOnValues_some_iff_f_some_on_all_values] at h₁
    apply h₁ ; clear h₁
    intro v h₁
    specialize h₂ v h₁
    rw [← ne_eq] at h₂
    rw [Option.ne_none_iff_isSome] at h₂
    exact h₂
  case mpr =>
    intro h₁
    replace ⟨v, h₁, h₂⟩ := h₁
    rw [← Option.not_isSome_iff_eq_none]
    intro h₃
    rw [mapMOnValues_some_iff_f_some_on_all_values] at h₃
    specialize h₃ v h₁
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
  Corollary of the above
-/
theorem mapM_err_iff_f_err_on_some_element {f : α → Except ε β} {xs : List α} :
  ¬ Except.isOk (xs.mapM f) ↔ ∃ x ∈ xs, ¬ Except.isOk (f x)
:= by
  sorry

/--
  Another generic lemma about the behavior of List.mapM in the Option monad
-/
theorem mem_mapM_some {f : α → Option β} {xs : List α} {ys : List β} {y : β} :
  xs.mapM f = some ys → y ∈ ys → ∃ x ∈ xs, f x = some y
:= by
  sorry

/--
  Analogue of `mem_mapM_some` for Map.mapMOnValues in the Option monad
-/
theorem mem_mapMOnValues_some [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} {k : α} {y : γ} :
  m₁.mapMOnValues f = some m₂ → (k, y) ∈ m₂.kvs → ∃ v, (k, v) ∈ m₁.kvs ∧ f v = some y
:= by
  sorry

/--
  Another generic lemma about the behavior of List.mapM in the Except monad
-/
theorem mem_mapM_ok {f : α → Except ε β} {xs : List α} {ys : List β} {y : β} :
  xs.mapM f = .ok ys → y ∈ ys → ∃ x ∈ xs, f x = .ok y
:= by
  sorry

/--
  Another generic lemma about the behavior of List.mapM in the Except monad
-/
theorem mem_mapM_err {f : α → Except ε β} {xs : List α} {e : ε} :
  xs.mapM f = .error e ↔ ∃ x ∈ xs, f x = .error e
:= by
  sorry
