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

import Std

/-!
This file contains useful auxiliary lemmas about standard Lean datatypes and
functions.
-/


-- The `Except.bind_*` theorems let `simp` reduce terms that use the `do` notation.
@[simp] theorem Except.bind_ok_T (a : α) (f : α → ExceptT ε Id β) :
  (bind (Except.ok a) f : ExceptT ε Id β) = f a
:= by rfl

@[simp] theorem Except.bind_ok (a : α) (f : α → Except ε β) :
  (bind (Except.ok a) f : Except ε β) = f a
:= by rfl

@[simp] theorem Except.bind_err (e : ε) (f : α → Except ε β) :
  (bind (Except.error e) f : Except ε β) = (Except.error e)
:= by rfl

-- The `Option.bind_*` theorems let `simp` reduce terms that use the `do` notation.
@[simp] theorem Option.bind_some_T (a : α) (f : α → OptionT Id β) :
  (bind (Option.some a) f : OptionT Id β) = f a
:= by rfl

@[simp] theorem Option.bind_some_fun (a : α) (f : α → Option β) :
  (bind (Option.some a) f : Option β) = f a
:= by rfl

@[simp] theorem Option.bind_none_fun (f : α → Option β) :
  (bind Option.none f : Option β) = Option.none
:= by rfl

-- Nat lemmas to help with termination proofs.

theorem Nat.lt_add_of_one_and_other (n m : Nat) :
  n < 1 + m + n
:= by
  rw [Nat.add_comm]
  apply Nat.lt_add_of_pos_right
  apply Nat.add_pos_left
  apply Nat.one_pos

-- List.mapM lemmas

theorem List.mapM_implies_nil {f : α → Except β γ} {as : List α}
  (h₁ : List.mapM f as = Except.ok []) :
  as = []
:= by
  rw [←List.mapM'_eq_mapM] at h₁
  cases as
  case nil => rfl
  case cons hd tl =>
    simp [List.mapM'] at h₁
    cases h₂ : f hd <;> simp [h₂] at h₁
    cases h₃ : List.mapM' f tl <;>
    simp [h₃, pure, Except.pure] at h₁

theorem List.mapM_head_tail {α β γ} {f : α → Except β γ} {x : α} {xs : List α} {y : γ} {ys : List γ} :
  (List.mapM f (x :: xs)) = Except.ok (y :: ys) →
  (List.mapM f xs) = Except.ok ys
:= by
  simp [←List.mapM'_eq_mapM]
  cases h₁ : f x <;>
  simp [h₁]
  cases h₂ : mapM' f xs <;>
  simp [h₂, pure, Except.pure]

theorem List.foldlM_of_assoc_some (f : α → α → Option α) (x₀ x₁ x₂ x₃ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄))
  (h₂ : f x₀ x₁ = some x₂)
  (h₃ : List.foldlM f x₂ xs = some x₃):
  (do let y ← List.foldlM f x₁ xs ; f x₀ y) = some x₃
:= by
  cases xs
  case nil =>
    simp [List.foldlM, pure] at *
    subst h₃; exact h₂
  case cons hd tl =>
    simp [List.foldlM] at *
    cases h₄ : f x₂ hd <;> simp [h₄] at h₃
    rename_i x₄
    rcases (h₁ x₀ x₁ hd) with h₅
    simp [h₂, h₄] at h₅
    cases h₆ : f x₁ hd <;> simp [h₆] at h₅
    rename_i x₅
    rcases (List.foldlM_of_assoc_some f x₂ hd x₄ x₃ tl h₁ h₄ h₃) with h₇
    cases h₈ : List.foldlM f hd tl <;> simp [h₈] at h₇
    rename_i x₆
    rw [eq_comm] at h₅
    cases h₉ : List.foldlM f x₅ tl <;> simp [h₉]
    case none =>
      rcases (List.foldlM_of_assoc_some f x₀ x₅ x₄ x₃ tl h₁ h₅ h₃) with h₁₀
      simp [h₉] at h₁₀
    case some x₇ =>
      rcases (List.foldlM_of_assoc_some f x₁ hd x₅ x₇ tl h₁ h₆ h₉) with h₁₀
      simp [h₈] at h₁₀
      specialize h₁ x₀ x₁ x₆
      simp [h₂, h₁₀] at h₁
      simp [←h₁, h₇]

theorem List.foldlM_of_assoc_none' (f : α → α → Option α) (x₀ x₁ x₂ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄))
  (h₂ : f x₀ x₁ = none)
  (h₃ : List.foldlM f x₁ xs = some x₂):
  f x₀ x₂ = none
:= by
  cases xs
  case nil =>
    simp [pure] at h₃ ; subst h₃; exact h₂
  case cons hd tl =>
    simp [List.foldlM] at h₃
    cases h₄ : f x₁ hd <;> simp [h₄] at h₃
    rename_i x₃
    rcases (List.foldlM_of_assoc_some f x₁ hd x₃ x₂ tl h₁ h₄ h₃) with h₅
    cases h₆ : List.foldlM f hd tl <;> simp [h₆] at h₅
    rename_i x₄
    specialize h₁ x₀ x₁ x₄
    simp [h₂, h₅] at h₁
    simp [h₁]

theorem List.foldlM_of_assoc_none (f : α → α → Option α) (x₀ x₁ x₂ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄))
  (h₂ : f x₀ x₁ = some x₂)
  (h₃ : List.foldlM f x₂ xs = none):
  (do let y ← List.foldlM f x₁ xs ; f x₀ y) = none
:= by
  cases xs
  case nil =>
    simp [List.foldlM] at h₃
  case cons hd tl =>
    simp [List.foldlM]
    cases h₄ : f x₁ hd <;> simp [h₄]
    rename_i x₃
    cases h₅ : List.foldlM f x₃ tl <;> simp [h₅]
    rename_i x₄
    rcases (List.foldlM_of_assoc_some f x₁ hd x₃ x₄ tl h₁ h₄ h₅) with h₆
    cases h₇ : List.foldlM f hd tl <;> simp [h₇] at h₆
    rename_i x₅
    simp [List.foldlM] at h₃
    cases h₈ : f x₂ hd <;> simp [h₈] at h₃
    case none =>
      rcases (List.foldlM_of_assoc_none' f x₂ hd x₅ tl h₁ h₈ h₇) with h₉
      rcases (h₁ x₀ x₁ x₅) with h₁₀
      simp [h₂, h₆] at h₁₀
      simp [←h₁₀, h₉]
    case some x₆ =>
      rcases (List.foldlM_of_assoc_none f x₂ hd x₆ tl h₁ h₈ h₃) with h₉
      simp [h₇] at h₉
      rcases (h₁ x₀ x₁ x₅) with h₁₀
      simp [h₂, h₆] at h₁₀
      simp [←h₁₀, h₉]

theorem List.foldlM_of_assoc (f : α → α → Option α) (x₀ x₁ : α) (xs : List α)
  (h₁ : ∀ x₁ x₂ x₃,
    (do let x₄ ← f x₁ x₂ ; f x₄ x₃) =
    (do let x₄ ← f x₂ x₃ ; f x₁ x₄) ) :
  List.foldlM f x₀ (x₁ :: xs) =
  (do let y ← List.foldlM f x₁ xs ; f x₀ y)
:= by
  simp [List.foldlM]
  cases h₂ : f x₀ x₁ <;> simp [h₂]
  case none =>
    induction xs generalizing x₁
    case nil => simp [h₂]
    case cons hd tl ih =>
      simp [List.foldlM]
      cases h₃ : f x₁ hd <;> simp [h₃]
      rename_i x₂
      specialize h₁ x₀ x₁ hd
      simp [h₂, h₃] at h₁
      specialize ih x₂
      apply ih
      rw [eq_comm] at h₁ ; exact h₁
  case some x₂ =>
    rw [eq_comm]
    cases h₃ : List.foldlM f x₂ xs
    case none =>
      exact List.foldlM_of_assoc_none f x₀ x₁ x₂ xs h₁ h₂ h₃
    case some x₃ =>
      exact List.foldlM_of_assoc_some f x₀ x₁ x₂ x₃ xs h₁ h₂ h₃
