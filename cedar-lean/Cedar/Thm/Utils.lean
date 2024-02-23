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
theorem if_f_produces_pure_then_mapM_f_is_pure_map {α β} [Monad m] [LawfulMonad m] {f : α → β} {list : List α} :
  list.mapM ((fun a => pure (f a)) : α → m β) = pure (list.map f)
:= by
  induction list
  case nil => simp
  case cons x xs h => simp [h]

/--
  A generic lemma about composing List.mapM with List.map. Not in Std AFAICT.
-/
theorem mapM_over_map {α β γ} [Monad m] [LawfulMonad m] {f : α → β} {g : β → m γ} {list : List α} :
  List.mapM g (list.map f) = list.mapM fun x => g (f x)
:= by
  induction list
  case nil => simp
  case cons x xs h => simp [h]

/--
  A generic lemma about the behavior of List.mapM in the Option monad
-/
theorem mapM_some_iff_f_some_on_all_elements {f : α → Option β} {list : List α} :
  Option.isSome (list.mapM f) ↔ ∀ x ∈ list, Option.isSome (f x)
:= by
  rw [←List.mapM'_eq_mapM]
  constructor
  case mp =>
    induction list
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
        replace ⟨list₁, h₁⟩ := h₁
        cases h₂ : (f x) <;> simp [h₂] at h₁
        replace ⟨list₂, ⟨h₁, h₂⟩⟩ := h₁
        simp [Option.bind] at h₁
        sorry
  case mpr =>
    intro h
    induction list
    case nil => simp [List.mapM']
    case cons y ys h_ind =>
      have h₂ := h y ; simp at h₂
      rw [List.mapM'_cons]
      sorry
