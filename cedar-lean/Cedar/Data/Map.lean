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

import Cedar.Data.Set
/-!

This file defines a simple map data types, backed by a sorted duplicate-free
list of key-value. Functions maps assume but don't require that their inputs are
well-formed (sorted and duplicate-free). Separate theorems show that these
functions produce well-formed outputs when given well-formed inputs.

Use Map.make to construct well-formed maps from lists of key-value pairs.
-/

namespace Cedar.Data

inductive Map (α : Type u) (β : Type v) where
| mk : List (α × β) -> Map α β
deriving Repr, DecidableEq, Repr, Inhabited

namespace Map

def kvs {α : Type u} {β : Type v} : Map α β → List (Prod α β)
| .mk kvs => kvs


open Except

----- Definitions -----

-- produces an ordered and duplicate free list provided the given map is well formed
def toList {α : Type u} {β : Type v} (m : Map α β) : List (Prod α β) := m.kvs

/- Creates a well-formed map from the given list of pairs. -/
def make {α β} [LT α] [DecidableLT α] (kvs : List (α × β)) : Map α β :=
  Map.mk (kvs.canonicalize Prod.fst)

/-- Empty map -/
def empty {α β} : Map α β := .mk []

/-- Returns the keys of `m` as a set. -/
def keys {α β} (m : Map α β) : Set α :=
  Set.mk (m.kvs.map Prod.fst) -- well-formed by construction

/-- Returns the binding for `k` in `m`, if any. -/
def find? {α β} [BEq α] (m : Map α β) (k : α) : Option β :=
  match m.kvs.find? (fun ⟨k', _⟩ => k' == k) with
  | some (_, v) => some v
  | _           => none

/-- Returns true if `m` contains a mapping for the key `k`. -/
def contains {α β} [BEq α] (m : Map α β) (k : α) : Bool :=
  (m.find? k).isSome

/-- Returns the binding for `k` in `m` or `err` if none is found. -/
def findOrErr {α β ε} [BEq α] (m : Map α β) (k : α) (err: ε) : Except ε β :=
  match m.find? k with
  | some v => ok v
  | _      => error err

/-- Returns the binding for `k` in `m`, or panics if none is found. -/
def find! {α β} [Repr α] [BEq α] [Inhabited β] (m : Map α β) (k : α) : β :=
  match m.find? k with
  | some v => v
  | _      => panic! s!"find!: key {repr k} not found"

/-- Filters `m` using `f`. -/
def filter {α β} (f : α → β → Bool) (m : Map α β) : Map α β :=
  Map.mk (m.kvs.filter (fun ⟨k, v⟩ => f k v))

def size {α β} (m : Map α β) : Nat :=
  m.kvs.length

def mapOnValues {α β γ} [LT α] [DecidableLT α] (f : β → γ) (m : Map α β) : Map α γ :=
  Map.mk (m.kvs.map (λ (k,v) => (k, f v)))

def mapOnKeys {α β γ} [LT γ] [DecidableLT γ] (f : α → γ) (m : Map α β) : Map γ β :=
  Map.make (m.kvs.map (λ (k,v) => (f k, v)))

----- Props and Theorems -----

instance [LT (Prod α β)] : LT (Map α β) where
lt a b := a.kvs < b.kvs

instance decLt [LT (Prod α β)] [DecidableRel (α:=(Prod α β)) (·<·)] : (n m : Map α β) → Decidable (n < m)
  | .mk nkvs, .mk mkvs => List.hasDecidableLt nkvs mkvs

instance : Membership α (Map α β) where
  mem a m := List.Mem a (m.kvs.map Prod.fst)

theorem in_list_in_map {α : Type u} (k : α) (v : β) (m : Map α β) :
  (k, v) ∈ m.kvs → k ∈ m
:= by
  intro h₀
  have h₁ : k ∈ (List.map Prod.fst m.kvs) := by simp ; exists (k, v)
  apply h₁

theorem contains_iff_some_find? {α β} [BEq α] {m : Map α β} {k : α} :
  m.contains k ↔ ∃ v, m.find? k = .some v
:= by simp [contains, Option.isSome_iff_exists]

theorem not_contains_of_empty {α β} [BEq α] (k : α) :
  ¬ (Map.empty : Map α β).contains k
:= by simp [contains, empty, find?, List.find?]

end Map

end Cedar.Data
