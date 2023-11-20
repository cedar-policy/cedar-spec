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
deriving Repr
deriving instance DecidableEq, Repr, Inhabited, Lean.ToJson for Set

namespace Set

private def elts {α : Type u} : (Set α) -> (List α)
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
  mem v s := s.elts.Mem v

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

end Set

end Cedar.Data
