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

import Cedar.Data.Map
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List

/-!
# Map properties

This file proves useful properties of canonical list-based maps defined in
`Cedar.Data.Map`.
-/

namespace Cedar.Data.Map

/-! ### Well-formed maps -/

def WellFormed {α β} [LT α] [DecidableLT α] (m : Map α β) :=
  m = Map.make m.toList

/-
  In well-formed maps, if there are two pairs with the same key, then they have
  the same value
-/
theorem key_maps_to_one_value [BEq α] [LT α] [DecidableLT α] (k : α) (v₁ v₂ : β) (m : Map α β) :
  m.WellFormed →
  (k, v₁) ∈ m.kvs →
  (k, v₂) ∈ m.kvs →
  v₁ = v₂
:= by
  unfold WellFormed toList
  intro wf h₁ h₂
  sorry

/-
  In well-formed maps, if a key maps to a value, then all equal keys (by BEq)
  also map to that value
-/
theorem equal_keys_same_value [BEq α] [LT α] [DecidableLT α] (k₁ k₂ : α) (v : β) (m : Map α β) :
  m.WellFormed →
  (k₁, v) ∈ m.kvs →
  k₁ == k₂ →
  (k₂, v) ∈ m.kvs
:= by
  unfold WellFormed toList
  intro wf h₁ h₂
  sorry

/-! ### contains, mem, and find? -/

theorem in_list_in_map {α : Type u} (k : α) (v : β) (m : Map α β) :
  (k, v) ∈ m.kvs → k ∈ m
:= by
  intro h₀
  have h₁ : k ∈ (List.map Prod.fst m.kvs) := by simp only [List.mem_map] ; exists (k, v)
  apply h₁

theorem in_list_some_find? [DecidableEq α] [LT α] [DecidableLT α] (k : α) (v : β) (m : Map α β) :
  m.WellFormed →
  ((k, v) ∈ m.kvs ↔ m.find? k = some v)
:= by
  intro h₁
  unfold find?
  constructor
  case mp =>
    intro h₂
    cases h₃ : m.kvs.find? λ x => match x with | (k', _) => k' == k
    case none =>
      exfalso
      rw [List.find?_eq_none] at h₃
      specialize h₃ (k, v) h₂
      apply h₃ ; clear h₃
      simp
    case some kv =>
      simp
      have h₄ := List.find?_some h₃
      simp at h₄
      subst h₄
      replace h₃ := List.mem_of_find?_eq_some h₃
      apply (key_maps_to_one_value kv.fst v kv.snd m h₁ h₂ _).symm
      trivial
  case mpr =>
    intro h₂
    cases h₃ : m.kvs.find? λ x => match x with | (k', _) => k' == k
    case none => simp [h₃] at h₂
    case some kv =>
      simp [h₃] at h₂
      subst h₂
      have h₄ := List.mem_of_find?_eq_some h₃
      replace h₃ := List.find?_some h₃
      split at h₃ ; rename_i k' v
      simp
      exact equal_keys_same_value k' k v m h₁ h₄ h₃

/- currently unused -/
/-
theorem contains_iff_in_map [BEq α] (k : α) (m : Map α β) :
  m.contains k ↔ k ∈ m
:= by
  simp [contains, Option.isSome_iff_exists]
  constructor
  case mp =>
    simp [find?]
    intro v h₁
    apply in_list_in_map k v m
    split at h₁ <;> simp at h₁
    subst h₁
    case h_1 k' v h₁ =>
      have h₂ := List.mem_of_find?_eq_some h₁ ; simp at h₂
      have h₃ := List.find?_some h₁ ; simp at h₃
      simp [h₃] at h₂
-/

theorem contains_iff_some_find? {α β} [BEq α] {m : Map α β} {k : α} :
  m.contains k ↔ ∃ v, m.find? k = .some v
:= by simp [contains, Option.isSome_iff_exists]

theorem not_contains_of_empty {α β} [BEq α] (k : α) :
  ¬ (Map.empty : Map α β).contains k
:= by simp [contains, empty, find?, List.find?]

theorem in_values_iff_some_find? {α β} [DecidableEq α] [LT α] [DecidableLT α] {m : Map α β} {v : β} :
  m.WellFormed →
  (v ∈ m.values ↔ ∃ k, m.find? k = .some v)
:= by
  simp [values]
  intro wf
  constructor
  case mp =>
    intro h₁
    replace ⟨⟨k, v'⟩, ⟨h₁, h₂⟩⟩ := h₁
    exists k
    simp [Prod.snd] at h₂
    subst v'
    rw [← in_list_some_find? k v m wf]
    trivial
  case mpr =>
    intro h₁
    replace ⟨k, h₁⟩ := h₁
    rw [← in_list_some_find? k v m wf] at h₁
    exists (k, v)

/-! ### make -/

theorem make_wf [LT α] [StrictLT α] [DecidableLT α] (xs : List (α × β)) :
  WellFormed (Map.make xs)
:= by
  simp only [WellFormed, make, toList, kvs, List.canonicalize_idempotent]

theorem make_mem_list_mem [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  x ∈ (Map.make xs).kvs → x ∈ xs
:= by
  simp only [kvs, make]
  intro h₁
  have h₂ := List.canonicalize_subseteq Prod.fst xs
  simp [List.subset_def] at h₂
  exact h₂ h₁

theorem make_nil_is_empty {α β} [LT α] [DecidableLT α] :
  (Map.make [] : Map α β) = Map.empty
:= by simp [make, empty, List.canonicalize_nil]

/-! ### find? and mapOnValues -/

theorem mapOnValues_wf [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} :
  m.WellFormed ↔ (m.mapOnValues f).WellFormed
:= by
  unfold mapOnValues WellFormed
  sorry

theorem mapOnValues_empty {α β γ} [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} :
  (empty : Map α β).mapOnValues f = empty
:= by
  simp [mapOnValues, empty]

theorem find?_mapOnValues {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) (m : Map α β) (k : α)  :
  (m.find? k).map f = (m.mapOnValues f).find? k
:= by
  simp [Map.find?, Map.mapOnValues, Map.kvs, ←List.find?_pair_map]
  cases h : List.find? (fun x => x.fst == k) m.1 <;>
  simp only [Option.map_none', Option.map_some']

theorem find?_mapOnValues_some {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} {v : β} :
  m.find? k = .some v →
  (m.mapOnValues f).find? k = .some (f v)
:= by
  intro h₁
  rw [← find?_mapOnValues f m k]
  simp [Option.map, h₁]

theorem find?_mapOnValues_none {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} :
  m.find? k = .none →
  (m.mapOnValues f).find? k = .none
:= by
  intro h₁
  rw [← find?_mapOnValues f m k]
  simp [Option.map, h₁]

theorem mapOnValues_eq_make_map {α β γ} [LT α] [StrictLT α] [DecidableLT α] (f : β → γ) {m : Map α β}
  (wf : m.WellFormed) :
  m.mapOnValues f = Map.make (m.toList.map λ kv => (kv.fst, f kv.snd))
:= by
  unfold WellFormed at wf
  simp [mapOnValues, toList, kvs, make] at *
  rw [wf] ; simp only ; rw [eq_comm]
  have h₁ : Prod.map id f = (fun (x : α × β) => (x.fst, f x.snd)) := by unfold Prod.map ; simp only [id_eq]
  simp only [← h₁, ← List.canonicalize_of_map_fst, List.canonicalize_idempotent]

theorem mapOnValues_contains {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} :
  Map.contains m k = Map.contains (Map.mapOnValues f m) k
:= by
  simp only [contains, Option.isSome]
  split
  case h_1 h => simp [find?_mapOnValues_some f h]
  case h_2 h => simp [find?_mapOnValues_none f h]

theorem values_mapOnValues [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} :
  (m.mapOnValues f).values = m.values.map f
:= by
  unfold mapOnValues values
  simp [kvs]
  repeat rw [← List.map_map]
  induction m.1
  case nil => simp
  case cons kv tail h_ind =>
    simp [List.map_cons]
    repeat rw [← List.map_map]
    trivial

theorem findOrErr_mapOnValues [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} {e : Error} :
  (m.mapOnValues f).findOrErr k e = (m.findOrErr k e).map f
:= by
  unfold findOrErr
  rw [← find?_mapOnValues]
  cases m.find? k <;> simp [Except.map]

theorem findOrErr_ok_iff_find?_some [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} {e : Error} :
  m.findOrErr k e = .ok v ↔ m.find? k = some v
:= by
  unfold findOrErr
  cases m.find? k <;> simp

theorem in_values_iff_findOrErr_ok [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {v : β} {e : Error}
  (wf : m.WellFormed) :
  v ∈ m.values ↔ ∃ k, m.findOrErr k e = .ok v
:= by
  simp [values, findOrErr_ok_iff_find?_some]
  constructor
  case mp =>
    intro h₁
    replace ⟨⟨k, v'⟩, ⟨h₁, h₂⟩⟩ := h₁
    simp at h₂
    subst v'
    exists k
    simp [← in_list_some_find? k v m wf]
    trivial
  case mpr =>
    intro h₁
    replace ⟨k, h₁⟩ := h₁
    exists (k, v)
    simp [in_list_some_find? k v m wf]
    trivial

/- not currently needed -/
theorem mapM_on_kvs_eqv_mapM_on_map [LT α] [DecidableLT α] (f : β → Option γ) {m : Map α β} :
  (m.kvs.mapM λ x => f x.snd) = (m.mapMOnValues f).map Map.values
:= by
  sorry

/-! ### sizeOf -/

theorem sizeOf_lt_of_value [SizeOf α] [SizeOf β] {m : Map α β} {k : α} {v : β}
  (h : (k, v) ∈ m.1) :
  sizeOf v < sizeOf m
:= by
  simp only [Membership.mem] at h
  replace h := List.sizeOf_lt_of_mem h
  have _ : sizeOf v < sizeOf (k, v) := by
    simp only [sizeOf, Prod._sizeOf_1]
    omega
  have _ : sizeOf m.1 < sizeOf m := by
    simp only [sizeOf, _sizeOf_1]
    omega
  omega

end Cedar.Data.Map
