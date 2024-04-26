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

theorem wf_implies_sorted {α β} [LT α] [DecidableLT α] [StrictLT α] {m : Map α β} :
  m.WellFormed → m.toList.SortedBy Prod.fst
:= by
  intro h
  rw [WellFormed, make] at h
  rw [h, toList, kvs]
  simp only [List.canonicalize_sortedBy]

theorem sorted_implies_wf {α β} [LT α] [DecidableLT α] [StrictLT α] {m : Map α β} :
  m.toList.SortedBy Prod.fst → m.WellFormed
:= by
  intro h
  rw [toList, kvs] at *
  replace h := List.sortedBy_implies_canonicalize_eq h
  rw [WellFormed, toList, kvs, make, h]

/-! ### contains and mem -/

theorem in_list_in_map {α : Type u} (k : α) (v : β) (m : Map α β) :
  (k, v) ∈ m.kvs → k ∈ m
:= by
  intro h₀
  have h₁ : k ∈ (List.map Prod.fst m.kvs) := by simp only [List.mem_map] ; exists (k, v)
  apply h₁

theorem contains_iff_some_find? {α β} [BEq α] {m : Map α β} {k : α} :
  m.contains k ↔ ∃ v, m.find? k = .some v
:= by simp [contains, Option.isSome_iff_exists]

theorem not_contains_of_empty {α β} [BEq α] (k : α) :
  ¬ (Map.empty : Map α β).contains k
:= by simp [contains, empty, find?, List.find?]

/-! ### make and mk -/

theorem make_wf [LT α] [StrictLT α] [DecidableLT α] (xs : List (α × β)) :
  WellFormed (Map.make xs)
:= by
  simp only [WellFormed, make, toList, kvs, List.canonicalize_idempotent]

theorem mk_wf [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  xs.SortedBy Prod.fst → (Map.mk xs).WellFormed
:= by
  intro h
  replace h := List.sortedBy_implies_canonicalize_eq h
  rw [← h, WellFormed, make, toList, kvs]
  simp only [List.canonicalize_idempotent]

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

theorem find?_mapOnValues {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) (m : Map α β) (k : α)  :
  (m.find? k).map f = (m.mapOnValues f).find? k
:= by
  simp [Map.find?, Map.mapOnValues, Map.kvs, ←List.find?_pair_map]
  cases __ : List.find? (fun x => x.fst == k) m.1 <;>
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
  (h₁ : m.WellFormed) :
  m.mapOnValues f = Map.make (m.toList.map λ kv => (kv.fst, f kv.snd))
:= by
  simp [Map.WellFormed] at h₁
  simp [Map.mapOnValues, Map.toList, Map.kvs, Map.make] at *
  rw [h₁] ; simp only ; rw [eq_comm]
  have h₂ : Prod.map id f = (fun (x : α × β) => (x.fst, f x.snd)) := by unfold Prod.map ; simp only [id_eq]
  simp only [← h₂, ← List.canonicalize_of_map_fst, List.canonicalize_idempotent]

theorem find?_mem_toList {α β} [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β}
  (h₁ : m.find? k = .some v) :
  (k, v) ∈ m.toList
:= by
  simp [Map.toList, Map.kvs, Map.find?] at *
  split at h₁ <;> simp at h₁
  subst h₁
  rename_i h₂
  have h₃ := List.find?_some h₂
  simp at h₃ ; subst h₃
  exact List.mem_of_find?_eq_some h₂

theorem mem_toList_find? {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β}
  (h₁ : m.WellFormed)
  (h₂ : (k, v) ∈ m.toList) :
  m.find? k = .some v
:= by
  rw [WellFormed, make] at h₁
  generalize hm : toList m = l
  rw [hm] at h₁ h₂
  subst h₁
  simp only [toList, kvs] at hm
  rw [hm]
  have hsrt := List.canonicalize_sortedBy Prod.fst l
  rw [hm] at hsrt
  have h := List.mem_of_sortedBy_implies_find? h₂ hsrt
  simp only at h
  simp only [find?, kvs, h]

theorem mapOnValues_contains {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} :
  Map.contains m k = Map.contains (Map.mapOnValues f m) k
:= by
  simp only [contains, Option.isSome]
  split
  case h_1 h => simp [find?_mapOnValues_some f h]
  case h_2 h => simp [find?_mapOnValues_none f h]


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
  rename_i v_lt_kv m1_lt_m
  let a := sizeOf v
  let c := sizeOf m.1
  let d := sizeOf m
  have v_lt_m1 : a < c := by apply Nat.lt_trans v_lt_kv h
  have v_lt_m : a < d := by apply Nat.lt_trans v_lt_m1 m1_lt_m
  have ha : a = sizeOf v := by simp
  have hd : d = sizeOf m := by simp
  rw [ha, hd] at v_lt_m
  exact v_lt_m


end Cedar.Data.Map
