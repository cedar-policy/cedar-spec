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

import Init.Classical
import Std

/-!
This file contains utilities for working with strict and decidable LT relations.
-/

namespace Cedar.Data

class StrictLT (α) [LT α] : Prop where
  asymmetric : ∀ (a b : α), a < b → ¬ b < a
  transitive : ∀ (a b c : α), a < b → b < c → a < c
  connected  : ∀ (a b : α), a ≠ b → (a < b ∨ b < a)

theorem StrictLT.irreflexive [LT α] [StrictLT α] (x : α) :
  ¬ x < x
:= by
  by_contra h₁
  have h₂ := StrictLT.asymmetric x x h₁
  contradiction

theorem StrictLT.if_not_lt_gt_then_eq [LT α] [StrictLT α] (x y : α) :
  ¬ x < y → ¬ y < x → x = y
:= by
  intro h₁ h₂
  by_contra h₃
  have h₄ := StrictLT.connected x y h₃
  simp [h₁, h₂] at h₄

theorem StrictLT.not_eq [LT α] [StrictLT α] (x y : α) :
  x < y → ¬ x = y
:= by
  intro h₁
  by_contra h₂
  subst h₂
  have h₃ := StrictLT.irreflexive x
  contradiction

abbrev DecidableLT (α) [LT α] := DecidableRel (α := α) (· < ·)

end Cedar.Data

----- Theorems and instances -----

open Cedar.Data

theorem List.lt_cons_cases [LT α] {x y : α} {xs ys : List α} :
  x :: xs < y :: ys →
  (x < y ∨ (¬ x < y ∧ ¬ y < x ∧ xs < ys))
:= by
  intro h₁
  cases h₁
  case head _ h₁ => simp [h₁]
  case tail _ h₁ h₂ h₃ => simp [h₁, h₂]; assumption

theorem List.cons_lt_cons [LT α] [StrictLT α] (x : α) (xs ys : List α) :
  xs < ys → x :: xs < x :: ys
:= by
  intro h₁
  apply List.lt.tail (StrictLT.irreflexive x) (StrictLT.irreflexive x) h₁

theorem List.lt_irrefl [LT α] [StrictLT α] (xs : List α) :
  ¬ xs < xs
:= by
  induction xs
  case nil => by_contra; contradiction
  case cons _ _ hd tl ih =>
    by_contra h₁
    have h₂ := StrictLT.irreflexive hd
    cases tl
    case nil =>
      have h₃ := List.lt_cons_cases h₁
      simp [h₂] at h₃
      contradiction
    case cons _ _ hd' tl' =>
      have h₃ := List.lt_cons_cases h₁
      simp [h₂] at h₃
      contradiction

theorem List.lt_trans [LT α] [StrictLT α] {xs ys zs : List α} :
  xs < ys → ys < zs → xs < zs
:= by
  intro h₁ h₂
  cases h₁
  case nil => cases h₂ <;> apply List.lt.nil
  case head _ _ xhd xtl yhd ytl h₃ =>
    cases h₂
    case head _ _ zhd ztl h₄ =>
      apply List.lt.head
      apply StrictLT.transitive _ _ _ h₃ h₄
    case tail _ _ zhd ztl h₄ h₅ h₆ =>
      have h₇ := StrictLT.if_not_lt_gt_then_eq yhd zhd h₄ h₅
      subst h₇
      apply List.lt.head
      exact h₃
  case tail _ _ xhd xtl yhd ytl h₃ h₄ h₅ =>
    cases h₂
    case head _ _ zhd ztl h₆ =>
      have h₇ := StrictLT.if_not_lt_gt_then_eq xhd yhd h₃ h₄
      subst h₇
      apply List.lt.head
      exact h₆
    case tail _ _ zhd ztl h₆ h₇ h₈ =>
      have h₉ := StrictLT.if_not_lt_gt_then_eq xhd yhd h₃ h₄
      subst h₉
      apply List.lt.tail h₆ h₇
      apply List.lt_trans h₅ h₈

theorem List.lt_asymm [LT α] [StrictLT α] {xs ys : List α} :
  xs < ys → ¬ ys < xs
:= by
  intro h₁
  cases xs
  case nil =>
    by_contra h₂
    contradiction
  case cons _ _ hd tl =>
    cases ys
    case nil => contradiction
    case cons _ _ hd' tl' =>
      by_contra h₂
      have h₃ := List.lt_trans h₁ h₂
      have h₄ := List.lt_irrefl (hd :: tl)
      contradiction

theorem List.lt_conn [LT α] [StrictLT α] {xs ys : List α} :
  xs ≠ ys → (xs < ys ∨ ys < xs)
:= by
  intro h₁
  by_contra h₂
  simp [not_or] at h₂
  have ⟨h₂, h₃⟩ := h₂
  cases xs <;> cases ys
  case nil.nil => contradiction
  case nil.cons _ _ xhd xtl _ =>
    have h₄ := List.lt.nil xhd xtl
    contradiction
  case cons.nil _ _ yhd ytl _ =>
    have h₄ := List.lt.nil yhd ytl
    contradiction
  case cons.cons _ _ xhd xtl yhd ytl _ =>
    by_cases (xhd < yhd)
    case pos h₄ =>
      have h₅ := List.lt.head xtl ytl h₄
      contradiction
    case neg h₄ =>
      by_cases (yhd < xhd)
      case pos h₅ =>
        have h₆ := List.lt.head ytl xtl h₅
        contradiction
      case neg h₅ =>
        have h₆ := StrictLT.if_not_lt_gt_then_eq xhd yhd h₄ h₅
        subst h₆
        simp at h₁
        cases (List.lt_conn h₁)
        case inl _ _ h₆ =>
          have h₇ := List.cons_lt_cons xhd xtl ytl h₆
          contradiction
        case inr _ _ h₆ =>
          have h₇ := List.cons_lt_cons xhd ytl xtl h₆
          contradiction

instance List.strictLT (α) [LT α] [StrictLT α] : StrictLT (List α) where
  asymmetric _ _   := List.lt_asymm
  transitive _ _ _ := List.lt_trans
  connected  _ _   := List.lt_conn

def Bool.lt (a b : Bool) : Bool := match a,b with
  | false, true => true
  | _, _ => false

instance : LT Bool where
  lt a b := Bool.lt a b

instance Bool.decLt (a b : Bool) : Decidable (a < b) :=
  if h : Bool.lt a b then isTrue h else isFalse h

instance Bool.strictLT : StrictLT Bool where
  asymmetric a b   := by
    simp [LT.lt, Bool.lt]
    split <;> simp
  transitive a b c := by
    simp [LT.lt, Bool.lt]
    split <;> simp
  connected  a b   := by
    simp [LT.lt, Bool.lt]
    split <;> simp only [not_false_eq_true, _root_.or_false, imp_self]
    split <;> simp only [not_false_eq_true, _root_.or_true, imp_self]
    cases a <;> cases b <;> simp at *

instance Nat.strictLT : StrictLT Nat where
  asymmetric a b   := Nat.lt_asymm
  transitive a b c := Nat.lt_trans
  connected  a b   := by omega

instance Int.strictLT : StrictLT Int where
  asymmetric a b   := by omega
  transitive a b c := Int.lt_trans
  connected  a b   := by omega

theorem UInt32.lt_iff {x y : UInt32} : x < y ↔ x.1.1 < y.1.1 := by
  cases x; cases y; simp only [LT.lt]

theorem UInt32.ext_iff {x y : UInt32} : x = y ↔ x.1.1 = y.1.1 :=
  ⟨by simp_all, UInt32.ext⟩

instance UInt32.strictLT : StrictLT UInt32 where
  asymmetric a b   := by apply Nat.strictLT.asymmetric
  transitive a b c := by apply Nat.strictLT.transitive
  connected  a b   := by
    simp [UInt32.lt_iff, UInt32.ext_iff]
    omega

instance Char.strictLT : StrictLT Char where
  asymmetric a b   := by apply UInt32.strictLT.asymmetric
  transitive a b c := by apply UInt32.strictLT.transitive
  connected  a b   := by
    intro h₁
    apply UInt32.strictLT.connected
    by_contra h₂
    have h₄ : a = b := by apply Char.eq_of_val_eq h₂
    contradiction

instance String.strictLT : StrictLT String where
  asymmetric a b   := by
    simp [String.lt_iff]
    have h : StrictLT (List Char) := by apply List.strictLT
    apply h.asymmetric
  transitive a b c := by
    simp [String.lt_iff]
    have h : StrictLT (List Char) := by apply List.strictLT
    apply h.transitive
  connected  a b   := by
    simp [String.lt_iff, String.ext_iff]
    have h : StrictLT (List Char) := by apply List.strictLT
    apply h.connected
