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
import Std.Data.List.Basic
import Std.Data.List.Lemmas
/-!
This file defines a simple set data type, backed by a sorted duplicate-free
list. Functions on sets assume but don't require their inputs to be well-formed
(sorted and duplicate-free). Separate theorems show that these functions produce
well-formed outputs when given well-formed inputs.

Use Set.make to construct well-formed sets from lists.
-/

namespace Cedar.Data

inductive Set (α : Type u) where
| mk (l : List α)
deriving Repr, DecidableEq, Inhabited, Lean.ToJson

namespace Set

def elts {α : Type u} : (Set α) -> (List α)
| .mk elts => elts

open Except

----- Definitions -----

-- Creates an ordered/duplicate free list froma  set provided the underlying set is well formed.
def toList {α : Type u} (s : Set α) : List α := s.elts

/- Creates a well-formed set from the given list. -/
def make [LT α] [DecidableLT α] (elts : List α) : Set α :=
  Set.mk (elts.canonicalize (·))

/-- Empty set ∅ -/
def empty {α} : Set α := .mk []

/-- s == ∅ -/
def isEmpty {α} [DecidableEq α] (s : Set α) : Bool :=
  s == empty

/-- elt ∈ s -/
def contains {α} [BEq α] (s : Set α) (elt : α) : Bool :=
  s.elts.elem elt                    -- can use binary search instead

/-- s₁ ⊆ s₂ -/
def subset {α} [BEq α] (s₁ s₂ : Set α) : Bool :=
  s₁.elts.all s₂.contains

/-- s₁ ∩ s₂ ≠ ∅ -/
def intersects {α} [BEq α] (s₁ s₂ : Set α) : Bool :=
  s₁.elts.any s₂.contains

/-- s₁ ∩ s₂ -/
def intersect {α} [BEq α] (s₁ s₂ : Set α) : Set α :=
  Set.mk (s₁.elts.filter s₂.contains) -- well-formed by construction

/-- s₁ ∪ s₂ -/
def union {α} [LT α] [DecidableLT α] (s₁ s₂ : Set α) : Set α :=
  make (s₁.elts ++ s₂.elts)           -- enforce well-formedness

/-- Filters `s` using `f`. -/
def filter {α} (f : α → Bool) (s : Set α) : Set α :=
  Set.mk (s.elts.filter f)            -- well-formed by construction

/-- Maps `f` to `s`.-/
def map {α β} [LT β] [DecidableLT β] (f : α → β) (s : Set α) : Set β :=
  make (s.elts.map f)                 -- enforce well-formedness

/-- Maps `f` to `s` and returns the result of `err` if any error is encounterd. -/
def mapOrErr {α β ε} [DecidableEq β] [LT β] [DecidableRel (α := β) (· < ·)] (f : α → Except ε β) (s : Set α) (err : ε) : Except ε (Set β) :=
  match s.elts.mapM f with
  | .ok elts => ok (make elts)    -- enforce well-formedness
  | _        => error err         -- return fixed error to be order-independent

/-- Returns true if all elements of `s` satisfy `f`. -/
def all {α} (f : α → Bool) (s : Set α) : Bool :=
  s.elts.all f

/-- Returns true if some element of `s` satisfies `f`. -/
def any {α} (f : α → Bool) (s : Set α) : Bool :=
  s.elts.any f

def size {α} (s : Set α) : Nat :=
  s.elts.length

def singleton {α} (a : α) : Set α :=
  Set.mk [a]

def foldl {α β} (f : α → β → α) (init : α) (s : Set β) : α :=
  s.elts.foldl f init

----- Props and Theorems -----

instance [LT α] : LT (Set α) where
lt a b := a.elts < b.elts

instance decLt [LT α] [DecidableLT α] : (n m : Set α) -> Decidable (n < m)
  | .mk nelts, .mk melts => List.hasDecidableLt nelts melts

instance : Membership α (Set α) where -- enables ∈ notation
  mem v s := v ∈ s.elts

theorem contains_prop_bool_equiv [DecidableEq α] {v : α} {s : Set α} :
  s.contains v = true ↔ v ∈ s
:= by
  apply Iff.intro
  intro h0
  apply List.mem_of_elem_eq_true
  assumption
  intro h0
  apply List.elem_eq_true_of_mem
  assumption

theorem in_list_in_set {α : Type u} (v : α) (s : Set α) :
  v ∈ s.elts → v ∈ s
:= by
  intro h0
  apply h0

theorem in_set_in_list {α : Type u} (v : α) (s : Set α) :
  v ∈ s → v ∈ s.elts
:= by
  simp [elts, Membership.mem]


theorem mem_cons_self {α : Type u} (hd : α) (tl : List α) :
  hd ∈ Set.mk (hd :: tl)
:= by
  simp [Membership.mem, elts]
  apply List.mem_cons_self hd tl

theorem mem_cons_of_mem {α : Type u} (a : α) (hd : α) (tl : List α) :
  a ∈ Set.mk tl → a ∈ Set.mk (hd :: tl)
:= by
  simp [Membership.mem, elts] ; intro h₁
  apply List.mem_cons_of_mem hd h₁


theorem in_set_means_list_non_empty {α : Type u} (v : α) (s : Set α) :
  v ∈ s.elts → ¬(s.elts = [])
:= by
  intros h0 h1
  rw [List.eq_nil_iff_forall_not_mem] at h1
  specialize h1 v
  contradiction

theorem make_non_empty [DecidableEq α] [LT α] [DecidableLT α] (xs : List α) :
  xs ≠ [] ↔ (Set.make xs).isEmpty = false
:= by
  unfold isEmpty; unfold empty; unfold make
  simp only [beq_eq_false_iff_ne, ne_eq, mk.injEq]
  apply List.canonicalize_not_nil

theorem make_eq_if_eqv [LT α] [DecidableLT α] [StrictLT α] (xs ys : List α) :
  xs ≡ ys → Set.make xs = Set.make ys
:= by
  intro h; unfold make; simp
  apply List.if_equiv_strictLT_then_canonical _ _ h

theorem make_eqv [LT α] [DecidableLT α] [StrictLT α] {xs ys : List α} :
  Set.make xs = Set.mk ys → xs ≡ ys
:= by
  simp [make] ; intro h₁
  rcases (List.canonicalize_equiv xs) with h₂
  subst h₁
  exact h₂

theorem make_mem [LT α] [DecidableLT α] [StrictLT α] (x : α) (xs : List α) :
  x ∈ xs ↔ x ∈ Set.make xs
:= by
  simp [make, Membership.mem, elts]
  rcases (List.canonicalize_equiv xs) with h₁
  simp [List.Equiv, List.subset_def] at h₁
  rcases h₁ with ⟨h₁, h₂⟩
  constructor <;> intro h₃
  case mp => apply h₁ h₃
  case mpr => apply h₂ h₃

theorem make_any_iff_any [LT α] [DecidableLT α] [StrictLT α] (f : α → Bool) (xs : List α) :
  (Set.make xs).any f = xs.any f
:= by
  simp [make, any, elts]
  rcases (List.canonicalize_equiv xs) with h₁
  simp [List.Equiv, List.subset_def] at h₁
  rcases h₁ with ⟨hl₁, hr₁⟩
  cases h₃ : List.any xs f
  case false =>
    by_contra h₄
    simp only [Bool.not_eq_false, List.any_eq_true] at h₄
    rcases h₄ with ⟨x, h₄, h₅⟩
    specialize hr₁ h₄
    simp [List.any_of_mem hr₁ h₅] at h₃
  case true =>
    simp [List.any_eq_true] at *
    rcases h₃ with ⟨x, h₃, h₄⟩
    exists x ; simp [h₄]
    apply hl₁ h₃

end Set

end Cedar.Data
