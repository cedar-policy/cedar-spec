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
import Cedar.Data.SizeOf
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Set

/-!
# Map properties

This file proves useful properties of canonical list-based maps defined in
`Cedar.Data.Map`.
-/

namespace Cedar.Data.Map

/-! ### Well-formed maps -/

def WellFormed {α β} [LT α] [DecidableLT α] (m : Map α β) :=
  m = Map.make m.toList

theorem if_wellformed_then_exists_make [LT α] [DecidableLT α] (m : Map α β) :
  WellFormed m → ∃ list, m = Map.make list
:= by
  intro h₁
  exists m.kvs

theorem wf_iff_sorted {α β} [LT α] [DecidableLT α] [StrictLT α] {m : Map α β} :
  m.WellFormed ↔ m.toList.SortedBy Prod.fst
:= by
  constructor
  case mp =>
    intro h
    rw [WellFormed, make] at h
    rw [h, toList, kvs]
    simp only [List.canonicalize_sortedBy]
  case mpr =>
    intro h
    rw [toList, kvs] at *
    replace h := List.sortedBy_implies_canonicalize_eq h
    rw [WellFormed, toList, kvs, make, h]

/--
  In well-formed maps, if there are two pairs with the same key, then they have
  the same value
-/
theorem key_maps_to_one_value [DecidableEq α] [LT α] [DecidableLT α] [StrictLT α] (k : α) (v₁ v₂ : β) (m : Map α β) :
  m.WellFormed →
  (k, v₁) ∈ m.kvs →
  (k, v₂) ∈ m.kvs →
  v₁ = v₂
:= by
  simp only [wf_iff_sorted, toList]
  intro wf h₁ h₂
  have h₃ := List.mem_of_sortedBy_unique wf h₁ h₂ (by simp)
  injection h₃

/--
  If two maps have exactly equal (k,v) sets, then the maps are equal

  This doesn't require WellFormed, but we use it in the proof of
  `eq_iff_kvs_equiv` below

  Surprisingly this is not a one-line proof.
-/
theorem eq_iff_kvs_eq {m₁ m₂ : Map α β} :
  m₁.kvs = m₂.kvs ↔ m₁ = m₂
:= by
  constructor
  case mp =>
    unfold kvs
    intro h
    match m₁ with
    | mk kvs₁ => match m₂ with
      | mk kvs₂ => simp at h ; subst h ; rfl
  case mpr => intro h ; subst h ; rfl

/--
  If two well-formed maps have equivalent (k,v) sets, then the maps are actually
  equal
-/
theorem eq_iff_kvs_equiv [LT α] [DecidableLT α] [StrictLT α] {m₁ m₂ : Map α β}
  (wf₁ : m₁.WellFormed)
  (wf₂ : m₂.WellFormed) :
  m₁.kvs ≡ m₂.kvs ↔ m₁ = m₂
:= by
  constructor
  case mp =>
    intro h₁
    simp [wf_iff_sorted, toList] at wf₁ wf₂
    have h₂ := List.sortedBy_equiv_implies_eq Prod.fst wf₁ wf₂ h₁
    exact eq_iff_kvs_eq.mp h₂
  case mpr =>
    intro h₁
    subst h₁
    exact List.Equiv.refl

/-! ### contains, mem, kvs, keys, values -/

theorem keys_wf [LT α] [DecidableLT α] [StrictLT α] (m : Map α β) :
  m.WellFormed → m.keys.WellFormed
:= by
  unfold keys
  intro wf
  simp only [wf_iff_sorted, toList] at wf
  simp only [Set.wf_iff_sorted]
  simp only [Set.elts]
  apply (List.map_eq_implies_sortedBy _).mp wf
  simp only [List.map_map]
  apply List.map_congr
  simp only [Function.comp_apply, id_eq, implies_true]

theorem kvs_nil_iff_empty {m : Map α β} :
  m.kvs = [] ↔ m = Map.empty
:= by
  unfold kvs empty
  constructor <;> intro h
  case mp => match m with
    | mk [] => trivial
    | mk ((k, v) :: kvs) => trivial
  case mpr => simp [h]

theorem mk_kvs_id (m : Map α β) :
  mk m.kvs = m
:= by simp only [kvs]

theorem in_list_in_map {α : Type u} (k : α) (v : β) (m : Map α β) :
  (k, v) ∈ m.kvs → k ∈ m
:= by
  intro h₀
  have h₁ : k ∈ (List.map Prod.fst m.kvs) := by simp only [List.mem_map] ; exists (k, v)
  apply h₁

theorem in_list_in_keys {k : α} {v : β} {m : Map α β} :
  (k, v) ∈ m.kvs → k ∈ m.keys
:= by
  intro h₀
  simp [keys, ← Set.in_list_iff_in_mk]
  exists (k, v)

theorem in_list_in_values {k : α} {v : β} {m : Map α β} :
  (k, v) ∈ m.kvs → v ∈ m.values
:= by
  simp only [values, List.mem_map]
  intro h₁
  exists (k, v)

/-- kinda the converse of `in_list_in_values` -/
theorem in_values_exists_key {m : Map α β} {v : β} :
  v ∈ m.values → ∃ k, (k, v) ∈ m.kvs
:= by
  simp only [values, List.mem_map, forall_exists_index, and_imp]
  intro (k, v) h₁ h₂
  subst h₂
  exists k

theorem in_keys_exists_value {m : Map α β} {k : α} :
  k ∈ m.keys → ∃ v, (k, v) ∈ m.kvs
:= by
  simp [keys, ← Set.in_list_iff_in_mk]
  intro (k', v) h₁ h₂
  simp only at h₂ ; subst k'
  exists v

theorem values_cons {m : Map α β} :
  m.kvs = (k, v) :: tl →
  m.values = v :: (mk tl).values
:= by
  unfold values kvs
  intro h₁
  simp [h₁]

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

theorem make_eq_mk [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  xs.SortedBy Prod.fst ↔ Map.make xs = Map.mk xs
:= by
  constructor <;> intro h
  case mp =>
    simp only [make, List.sortedBy_implies_canonicalize_eq h]
  case mpr =>
    simp only [make, mk.injEq] at h
    rw [← h]
    exact List.canonicalize_sortedBy _ _

/--
  Note that the converse of this is not true:
  counterexample `xs = [(1, false), (1, true)]`.
  (The property here would not hold for either `x = (1, false)` or `x = (1, true)`.)

  For a limited converse, see `mem_list_mem_make` below.
-/
theorem make_mem_list_mem [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  x ∈ (Map.make xs).kvs → x ∈ xs
:= by
  simp only [kvs, make]
  intro h₁
  have h₂ := List.canonicalize_subseteq Prod.fst xs
  simp only [List.subset_def] at h₂
  exact h₂ h₁

/--
  Very similar to `make_mem_list_mem` above
-/
theorem mem_values_make [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  v ∈ (Map.make xs).values → v ∈ xs.map Prod.snd
:= by
  -- despite the similarity to `make_mem_list_mem`, the proof does not currently
  -- use `make_mem_list_mem`
  simp only [values, make]
  simp only [List.mem_map, forall_exists_index, and_imp]
  intro (k, v) h₁ h₂
  exists (k, v)
  subst h₂
  simp only [and_true]
  have h₂ := List.canonicalize_subseteq Prod.fst xs
  simp only [List.subset_def] at h₂
  exact h₂ h₁

/--
  This limited converse of `make_mem_list_mem` requires that the input list is
  SortedBy Prod.fst.
-/
theorem mem_list_mem_make [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  xs.SortedBy Prod.fst →
  x ∈ xs → x ∈ (Map.make xs).kvs
:= by
  simp only [kvs, make]
  intro h₁ h₂
  have h₃ := List.sortedBy_implies_canonicalize_eq h₁
  rw [← h₃] at h₂
  exact h₂

theorem make_nil_is_empty {α β} [LT α] [DecidableLT α] :
  (Map.make [] : Map α β) = Map.empty
:= by simp [make, empty, List.canonicalize_nil]

/--
  Note that the converse of this is not true:
  counterexample `xs = [(1, false)]`, `ys = []`, `ab = (1, false)`.
-/
theorem make_cons [LT α] [DecidableLT α] {xs ys : List (α × β)} {ab : α × β} :
  make xs = make ys → make (ab :: xs) = make (ab :: ys)
:= by
  simp only [make, mk.injEq]
  apply List.canonicalize_cons

theorem make_of_make_is_id [LT α] [DecidableLT α] [StrictLT α] (xs : List (α × β)) :
  Map.make (Map.kvs (Map.make xs)) = Map.make xs
:= by
  simp only [make, mk.injEq]
  have h₁ := List.canonicalize_idempotent Prod.fst xs
  unfold id at h₁
  exact h₁

/-! ### find?, findOrErr, and mapOnValues -/

/--
  Converse is available at `in_list_iff_find?_some` (requires `wf` though)

  Inverse is available at `find?_notmem_keys` (requires `wf` though)
-/
theorem find?_mem_toList {α β} [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β}
  (h₁ : m.find? k = .some v) :
  (k, v) ∈ m.toList
:= by
  unfold toList kvs find? at *
  split at h₁ <;> simp only [Option.some.injEq] at h₁
  subst h₁
  rename_i h₂
  have h₃ := List.find?_some h₂
  simp only [beq_iff_eq] at h₃ ; subst h₃
  exact List.mem_of_find?_eq_some h₂

/--
  The `mpr` direction of this does not need the `wf` precondition and, in fact,
  is available separately as `find?_mem_toList` above
-/
theorem in_list_iff_find?_some [DecidableEq α] [LT α] [DecidableLT α] [StrictLT α] {k : α} {v : β} {m : Map α β}
  (wf : m.WellFormed) :
  (k, v) ∈ m.kvs ↔ m.find? k = some v
:= by
  unfold find?
  constructor
  case mp =>
    intro h₁
    cases h₂ : m.kvs.find? λ x => match x with | (k', _) => k' == k
    case none =>
      exfalso
      rw [List.find?_eq_none] at h₂
      apply h₂ (k, v) h₁ ; clear h₂
      simp only [beq_self_eq_true]
    case some kv =>
      simp only [Option.some.injEq]
      have h₃ := List.find?_some h₂
      simp only [beq_iff_eq] at h₃
      subst h₃
      replace h₃ := List.mem_of_find?_eq_some h₂
      apply (key_maps_to_one_value kv.fst v kv.snd m wf h₁ _).symm
      trivial
  case mpr => exact find?_mem_toList

/-- Inverse of `find?_mem_toList`, except that this requires `wf` -/
theorem find?_notmem_keys [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α}
  (wf : m.WellFormed) :
  m.find? k = none ↔ k ∉ m.keys
:= by
  unfold find? at *
  constructor <;> intro h₁
  case mp =>
    split at h₁ <;> simp at h₁
    rename_i h₂
    intro h₃
    replace ⟨v, h₃⟩ := in_keys_exists_value h₃
    apply h₂ k v ; clear h₂
    replace h₃ := (in_list_iff_find?_some wf).mp h₃
    unfold find? at h₃
    split at h₃ <;> simp only [Option.some.injEq] at h₃
    · subst v ; rename_i k' v h₂
      simp only [h₂, Option.some.injEq, Prod.mk.injEq, and_true]
      simpa using List.find?_some h₂
  case mpr =>
    split <;> simp <;> rename_i k' v h₂
    · apply h₁ ; clear h₁
      have h₃ := List.find?_some h₂ ; simp at h₃ ; subst k'
      replace h₂ := List.mem_of_find?_eq_some h₂
      exact in_list_in_keys h₂

theorem mapOnValues_wf [DecidableEq α] [LT α] [DecidableLT α] [StrictLT α] {f : β → γ} {m : Map α β} :
  m.WellFormed ↔ (m.mapOnValues f).WellFormed
:= by
  simp only [wf_iff_sorted, toList]
  apply List.map_eq_implies_sortedBy
  simp only [kvs, mapOnValues, List.map_map]
  apply List.map_congr
  simp

theorem mapOnValues_empty {α β γ} [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} :
  (empty : Map α β).mapOnValues f = empty
:= by
  simp [mapOnValues, empty]

theorem find?_mapOnValues {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) (m : Map α β) (k : α)  :
  (m.find? k).map f = (m.mapOnValues f).find? k
:= by
  simp only [find?, kvs, mapOnValues, ← List.find?_pair_map]
  cases m.1.find? (λ x => x.fst == k) <;> simp only [Option.map_none', Option.map_some']

theorem find?_mapOnValues_some {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} {v : β} :
  m.find? k = .some v →
  (m.mapOnValues f).find? k = .some (f v)
:= by
  intro h₁
  rw [← find?_mapOnValues]
  simp [Option.map, h₁]

theorem find?_mapOnValues_none {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} :
  m.find? k = .none →
  (m.mapOnValues f).find? k = .none
:= by
  intro h₁
  rw [← find?_mapOnValues]
  simp [Option.map, h₁]

theorem mapOnValues_eq_make_map {α β γ} [LT α] [StrictLT α] [DecidableLT α] (f : β → γ) {m : Map α β}
  (wf : m.WellFormed) :
  m.mapOnValues f = Map.make (m.toList.map λ kv => (kv.fst, f kv.snd))
:= by
  unfold WellFormed at wf
  simp only [make, toList, kvs, mapOnValues, mk.injEq] at *
  rw [wf] ; simp only ; rw [eq_comm]
  have h₁ : Prod.map id f = (λ (x : α × β) => (x.fst, f x.snd)) := by unfold Prod.map ; simp only [id_eq]
  simp only [← h₁, ← List.canonicalize_of_map_fst, List.canonicalize_idempotent]

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
  split <;> rename_i h
  · simp [find?_mapOnValues_some f h]
  · simp [find?_mapOnValues_none f h]

theorem keys_mapOnValues [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] (f : β → γ) (m : Map α β) :
  (m.mapOnValues f).keys = m.keys
:= by
  unfold mapOnValues keys kvs
  simp only [List.map_map, Set.mk.injEq]
  induction m.1
  case nil => simp only [List.map_nil]
  case cons hd tl ih =>
    simp only [List.map_cons, Function.comp_apply, List.cons.injEq, true_and]
    exact ih

theorem values_mapOnValues [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} :
  (m.mapOnValues f).values = m.values.map f
:= by
  unfold mapOnValues values kvs
  induction m.1
  case nil => simp only [List.map_nil]
  case cons hd tl ih =>
    simp only [List.map_cons, List.cons.injEq, true_and]
    exact ih

/-- `findOrErr` cannot return any error other than `e` -/
theorem findOrErr_returns [DecidableEq α] (m : Map α β) (k : α) (e : Error) :
  (∃ v, m.findOrErr k e = .ok v) ∨
  m.findOrErr k e = .error e
:= by
  unfold findOrErr
  cases m.find? k <;> simp

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
  cases m.find? k <;> simp only [Except.ok.injEq, Option.some.injEq]

theorem findOrErr_err_iff_find?_none [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {e : Error} :
  m.findOrErr k e = .error e ↔ m.find? k = none
:= by
  unfold findOrErr
  cases m.find? k <;> simp only

/--
  The converse requires the `wf` precondition, and is available in
  `findOrErr_ok_iff_in_kvs` below
-/
theorem findOrErr_ok_implies_in_kvs [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} {e : Error} :
  m.findOrErr k e = .ok v → (k, v) ∈ m.kvs
:= by
  simp only [findOrErr_ok_iff_find?_some]
  exact find?_mem_toList

/--
  The `mp` direction of this does not need the `wf` precondition and, in fact,
  is available separately as `findOrErr_ok_implies_in_kvs` above
-/
theorem findOrErr_ok_iff_in_kvs [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} {e : Error}
  (wf : m.WellFormed) :
  m.findOrErr k e = .ok v ↔ (k, v) ∈ m.kvs
:= by
  constructor
  case mp => exact findOrErr_ok_implies_in_kvs
  case mpr =>
    simp only [findOrErr_ok_iff_find?_some]
    exact (in_list_iff_find?_some wf).mp

/--
  The converse requires the `wf` precondition, and is available in
  `findOrErr_ok_iff_in_values` below
-/
theorem findOrErr_ok_implies_in_values [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} {e : Error} :
  m.findOrErr k e = .ok v → v ∈ m.values
:= by
  intro h₁
  simp [values]
  simp [findOrErr_ok_iff_find?_some] at h₁
  exists (k, v)
  have h₂ := find?_mem_toList h₁ ; simp [toList] at h₂
  simp [h₁, h₂, and_true]

/--
  The `mp` direction of this does not need the `wf` precondition and, in fact,
  is available separately as `findOrErr_ok_implies_in_values` above
-/
theorem findOrErr_ok_iff_in_values [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {v : β} {e : Error}
  (wf : m.WellFormed) :
  (∃ k, m.findOrErr k e = .ok v) ↔ v ∈ m.values
:= by
  constructor
  case mp =>
    intro ⟨k, h₁⟩
    exact findOrErr_ok_implies_in_values h₁
  case mpr =>
    simp only [values, List.mem_map, findOrErr_ok_iff_find?_some]
    intro h₁
    replace ⟨⟨k, v'⟩, ⟨h₁, h₂⟩⟩ := h₁
    simp only at h₂
    subst v'
    exists k
    simp [h₁, ← in_list_iff_find?_some wf]

theorem findOrErr_err_iff_not_in_keys [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} {e : Error}
  (wf : m.WellFormed) :
  m.findOrErr k e = .error e ↔ k ∉ m.keys
:= by
  simp [findOrErr_err_iff_find?_none]
  exact find?_notmem_keys wf

/--
  The converse requires two extra preconditions (`m` is `WellFormed` and `f` is
  injective) and is available as `in_mapOnValues_in_kvs`
-/
theorem in_kvs_in_mapOnValues [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} {v : β} :
  (k, v) ∈ m.kvs → (k, f v) ∈ (m.mapOnValues f).kvs
:= by
  unfold mapOnValues
  intro h₁
  simp only [kvs, List.mem_map, Prod.mk.injEq]
  exists (k, v)

/--
  We can remove the attach for the sake of proofs
-/
theorem mapOnValuesAttachIsMapOnValues
  {α : Type u} {β γ : Type v} [LT α] [DecidableLT α]
  {m : Map α β}
  {f : β → γ} :
  m.mapOnValues f = m.mapOnValuesAttach (λ prod => f prod.val)
  := by
  rw [← eq_iff_kvs_eq]
  simp [mapOnValues, mapOnValuesAttach]
  rw [← List.map₁_eq_map]

theorem mapOnValues_cons
  {α : Type u} {β γ : Type v} [LT α] [DecidableLT α] [BEq α ]
  {f : β → γ}
  {kv : α × β}
  {kvs : List (α × β)}
  :
  (Map.mk (kv :: kvs)).mapOnValues f =
  Map.mk ((kv.fst, f kv.snd) :: ((Map.mk kvs).mapOnValues f).kvs)
  := by
  rw [← eq_iff_kvs_eq]
  simp [mapOnValues, List.map]

/--
  Keys are not effected by mapping on values
  ie: the domain of a map is unchanged by map on values
-/
theorem mapOnValuesAttach_preservesContains
  {α : Type u} {β γ : Type v} [LT α] [DecidableLT α] [BEq α ] [LawfulBEq α] [DecidableEq α]
  {m : Map α β}
  {f : β → γ}
  {k : α} :
  (m.contains k ) = (m.mapOnValuesAttach (λ v => f v.val)).contains k
  := by
  rw [← mapOnValuesAttachIsMapOnValues]
  cases hcontains : (m.contains k) <;> cases m <;> rename_i kvs
  case true =>
    induction kvs
    case nil =>
      simp [contains, find?, List.find?] at hcontains
    case cons head tail ih =>
      cases head
      rename_i key value
      cases heq_head_key : decide (key = k) <;> simp at heq_head_key
      case _ =>
        have beq_false : (key == k) = false := by
          rw [beq_eq_false_iff_ne]
          assumption
        rw [mapOnValues_cons]
        simp [contains, find?, List.find?, beq_false]
        simp [contains, find?, List.find?] at ih
        apply ih
        simp [contains, find?, List.find?, beq_false] at hcontains
        assumption
      case _ =>
        subst heq_head_key
        simp [contains, find?, List.find?]
  case false =>
    induction kvs
    case nil =>
      simp [contains, find?, List.find?]
    case cons head tail ih =>
      cases head
      rename_i key value
      cases heq_head_key : decide (key = k) <;> simp at heq_head_key
      case _ =>
        have beq_false : (key == k) = false := by
          rw [beq_eq_false_iff_ne]
          assumption
        rw [mapOnValues_cons]
        simp [contains, find?, List.find?, beq_false]
        simp [contains, find?, List.find?] at ih
        apply ih
        simp [contains, find?, List.find?, beq_false] at hcontains
        assumption
      case _ =>
        subst heq_head_key
        simp [contains, find?, List.find?] at hcontains

/--
  An adapter that makes the above lemma easier to apply in context
-/
theorem mapOnValuesAttach_preservesContains_adapter
  {α : Type u} {β γ : Type v} [LT α] [DecidableLT α] [BEq α ] [LawfulBEq α] [DecidableEq α]
  {m : Map α β}
  {f : {x // ∃ k, (k,x) ∈ m.kvs} → γ}
  {k : α}
  {h₁ : ∃ (f' : β → γ), f = (λ prod => f' prod.val)} :
  (m.contains k ) = (m.mapOnValuesAttach f).contains k
  := by
  replace ⟨f', h₁⟩ := h₁
  rw [h₁]
  apply mapOnValuesAttach_preservesContains

theorem mapOnValuesAttach_preservesKeys
  {α : Type u} {β γ : Type v} [LT α] [DecidableLT α] [BEq α ] [LawfulBEq α] [DecidableEq α]
  {m : Map α β}
  {f : β → γ}
  {k : α}
  {h : m.contains k = true} :
  (m.mapOnValuesAttach (λ v => f v.val)).contains k = true
  := by
  rw [← mapOnValuesAttachIsMapOnValues]
  cases m
  rename_i kvs
  induction kvs
  case nil =>
    simp [mapOnValues, List.map, contains, find?, kvs] at h
  case cons head tail ih =>
    simp [contains, find?, kvs, List.find?] at h
    simp [contains, find?, kvs, List.find?]
    cases heq_head : (head.fst == k)
    case true =>
      simp
    case false =>
      simp
      cases htail : (mk tail).contains k
      case true =>
        have hrecur : (mapOnValues f (mk tail)).contains k = true := by
          apply ih
          assumption
        simp [mapOnValues, contains, find?, kvs ] at hrecur
        cases h' : List.find? (fun x => x.fst == k) (List.map (fun x => (x.fst, f x.snd)) tail)
        case none =>
          rw [h'] at hrecur
          simp at hrecur
        case some =>
          simp
      case false =>
        exfalso
        rw [heq_head] at h
        simp at h
        simp [contains, find?, kvs] at htail
        cases h' : List.find? (fun x => x.fst == k) tail
        case none =>
          rw [h'] at h
          simp at h
        case some =>
          rw [h'] at htail
          simp at htail

theorem mapOnValuesAttach_preservesKeys_adapter
  {α : Type u} {β γ : Type v} [LT α] [DecidableLT α] [BEq α ] [LawfulBEq α] [DecidableEq α]
  {m : Map α β}
  {f : { x // ∃ k, (k,x) ∈ m.kvs} → γ}
  {k : α}
  {h₁ : m.contains k = true}
  {h₂ : ∃ (f' : β → γ), f = λ val => f' val.val } :
  (m.mapOnValuesAttach f).contains k = true
  := by
  replace ⟨f', h₂⟩ := h₂
  rw [h₂]
  apply mapOnValuesAttach_preservesKeys
  assumption

theorem mapOnValues_maps
  {α : Type u} {β γ : Type v} [LT α] [DecidableLT α] [BEq α] [LawfulBEq α] [DecidableEq α]
  {m : Map α β}
  {f : β → γ}
  {k : α}
  {v : β}
  {h₁ : m.find? k = some v} :
  (m.mapOnValuesAttach (λ prod => f prod.val)).find? k = .some (f v)
  := by
  rw [← mapOnValuesAttachIsMapOnValues]
  cases m
  rename_i kvs
  induction kvs
  case nil =>
    simp [find?, List.find?] at h₁
  case cons head tail ih =>
    cases head
    rename_i key value
    cases heq : decide (key = k) <;> simp at heq
    case _ =>
      have beq_false : (key == k) = false := by
        apply beq_false_of_ne
        assumption
      simp [find?, List.find?, beq_false] at h₁
      rw [mapOnValues_cons]
      simp [find?, List.find?, beq_false]
      apply ih
      split at h₁ <;> simp at h₁
      rename_i heq
      subst h₁
      simp [find?, heq]
    case _ =>
      subst heq
      rw [mapOnValues_cons]
      simp [find?, List.find?] at h₁
      simp [find?, List.find?]
      subst h₁
      rfl

theorem mapOnValues_maps_adapter
  {α : Type u} {β γ : Type v}
  [LT α] [DecidableLT α] [BEq α] [LawfulBEq α] [DecidableEq α]
  {m : Map α β}
  {f : {x // ∃ k, (k,x) ∈ m.kvs} → γ}
  {f': β → γ}
  {k : α}
  {v : β}
  {h₁ : m.find? k = some v}
  {h₂ : f = λ prod => f' prod.val} :
  (m.mapOnValuesAttach f).find? k = .some (f' v)
  := by
  rw [h₂]
  apply mapOnValues_maps
  assumption

theorem mapOnValuesAttachFunEq
  {α : Type u} {β γ : Type v}
  [LT α] [DecidableLT α] [BEq α]
  {m : Map α β}
  {k : α}
  {f₁ : {x // ∃ k, (k,x) ∈ m.kvs} → γ}
  {f₂ : {x // ∃ k, (k,x) ∈ m.kvs} → γ}
  {h₁ : f₁ = f₂} :
  (m.mapOnValuesAttach f₁).find? k = (m.mapOnValuesAttach f₂).find? k
  := by
  rw [h₁]

/--
  Converse of `in_kvs_in_mapOnValues`; requires the extra preconditions that `m`
  is `WellFormed` and `f` is injective
-/
theorem in_mapOnValues_in_kvs [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} {v : β}
  (wf : m.WellFormed) :
  (k, f v) ∈ (m.mapOnValues f).kvs →
  (∀ v', f v = f v' → v = v') → -- require f to be injective
  (k, v) ∈ m.kvs
:= by
  rw [mapOnValues_eq_make_map f wf]
  unfold toList
  intro h₁ h_inj
  replace h₁ := make_mem_list_mem h₁
  replace ⟨(k', v'), h₁, h₂⟩ := List.mem_map.mp h₁
  simp only [Prod.mk.injEq] at h₂ ; replace ⟨h₂', h₂⟩ := h₂ ; subst k'
  specialize h_inj v' h₂.symm
  subst h_inj
  exact h₁

/--
  Slightly different formulation of `in_mapOnValues_in_kvs`
-/
theorem in_mapOnValues_in_kvs' [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} {v' : γ}
  (wf : m.WellFormed) :
  (k, v') ∈ (m.mapOnValues f).kvs →
  ∃ v, f v = v' ∧ (k, v) ∈ m.kvs
:= by
  rw [mapOnValues_eq_make_map f wf]
  unfold toList
  intro h₁
  replace h₁ := make_mem_list_mem h₁
  replace ⟨(k', v'), h₁, h₂⟩ := List.mem_map.mp h₁
  simp only [Prod.mk.injEq] at h₂ ; replace ⟨h₂', h₂⟩ := h₂ ; subst k' h₂
  exists v'

/-! ### mapMOnValues -/

/--
  This is not stated in terms of `Map.keys` because `Map.keys` produces a `Set`,
  and we want the even stronger property that it not only preserves the key-set,
  but also the key-order. (We'll use this to prove `mapMOnValues_some_wf`.)
-/
theorem mapMOnValues_preserves_keys [LT α] [DecidableLT α] [StrictLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  m₁.kvs.map Prod.fst = m₂.kvs.map Prod.fst
:= by
  intro h₁
  simp only [mapMOnValues, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
    Option.some.injEq] at h₁
  replace ⟨xs, h₁, h₂⟩ := h₁
  subst h₂
  cases h₂ : m₁.kvs <;> simp only [h₂, List.mapM_nil, List.mapM_cons, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h₁
  <;> unfold kvs at *
  case nil =>
    subst h₁
    simp [h₂]
  case cons kv tl =>
    have (k, v) := kv ; clear kv
    replace ⟨(k', y), ⟨y', h₁, h₃⟩, ⟨tl', h₄, h₅⟩⟩ := h₁
    subst h₅
    simp only [Prod.mk.injEq, List.map_cons, List.cons.injEq] at *
    replace ⟨h₃, h₃'⟩ := h₃
    subst k' y'
    have ih := mapMOnValues_preserves_keys (m₁ := mk tl) (m₂ := mk tl') (f := f)
    simp only [mapMOnValues, kvs, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some, Option.some.injEq, mk.injEq, exists_eq_right] at ih
    specialize ih h₄
    simp [ih, h₂]

theorem mapMOnValues_some_wf [LT α] [DecidableLT α] [StrictLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.WellFormed →
  (m₁.mapMOnValues f = some m₂) →
  m₂.WellFormed
:= by
  simp only [wf_iff_sorted, toList]
  intro wf h₁
  have h₂ := mapMOnValues_preserves_keys h₁
  exact (List.map_eq_implies_sortedBy h₂).mp wf

/--
  Alternate proof of `mapMOnValues_some_wf`, that relies on
  `List.mapM_some_eq_filterMap` instead of `mapMOnValues_preserves_keys`. Which do
  we prefer?
-/
theorem mapMOnValues_some_wf_alt_proof [LT α] [DecidableLT α] [StrictLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.WellFormed →
  (m₁.mapMOnValues f = some m₂) →
  m₂.WellFormed
:= by
  simp only [wf_iff_sorted, toList]
  intro wf h₁
  simp [mapMOnValues] at h₁
  replace ⟨xs, h₁, h₂⟩ := h₁
  subst h₂
  simp [kvs]
  replace h₁ := List.mapM_some_eq_filterMap h₁
  subst h₁
  apply List.filterMap_sortedBy _ wf
  intro (k, v) (k', v') h₁
  simp only at *
  cases h₂ : f v <;> simp [h₂, Option.bind] at h₁
  exact h₁.left

theorem mapMOnValues_ok_wf [LT α] [DecidableLT α] [StrictLT α] {f : β → Except ε γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.WellFormed →
  (m₁.mapMOnValues f = .ok m₂) →
  m₂.WellFormed
:= by
  simp only [wf_iff_sorted, toList]
  intro wf h₁
  simp [mapMOnValues, pure, Except.pure] at h₁
  cases h₂ : m₁.kvs.mapM λ kv => do let v' ← f kv.snd ; .ok (kv.fst, v')
  <;> simp [h₂] at h₁
  case ok kv =>
    subst m₂
    simp [kvs]
    replace h₂ := List.mapM_ok_eq_filterMap h₂
    subst h₂
    apply List.filterMap_sortedBy _ wf
    intro (k, v) (k', v') h₁
    simp only at *
    cases h₂ : f v <;> simp [h₂, Option.bind] at h₁
    exact h₁.left

theorem mapMOnValues_nil [LT α] [DecidableLT α] {f : β → Option γ} :
  (Map.empty : Map α β).mapMOnValues f = some Map.empty
:= by
  simp [mapMOnValues, empty, kvs, List.mapM_nil]

theorem mapMOnValues_cons {α : Type 0} [LT α] [DecidableLT α] {f : β → Option γ} {m : Map α β} {k : α} {v : β} {tl : List (α × β)}:
  m.kvs = (k, v) :: tl →
  (m.mapMOnValues f = do
    let v' ← f v
    let tl' ← (mk tl).mapMOnValues f
    return mk ((k, v') :: tl'.kvs))
:= by
  intro h₁
  cases h₂ : f v <;> simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_none_fun, Option.bind_some_fun]
  case none => unfold mapMOnValues ; simp [h₁, h₂]
  case some v' =>
    cases h₃ : (mk tl).mapMOnValues f <;> simp only [Option.none_bind, Option.some_bind]
    <;> unfold mapMOnValues at *
    case none =>
      simp only [h₁, Option.pure_def, Option.bind_eq_bind, List.mapM_cons, Option.bind_eq_none,
        Option.bind_eq_some, Option.some.injEq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro kvs' v'' h₄ tl' h₅ h₆
      simp only [h₂, Option.some.injEq] at h₄
      subst v'' kvs'
      cases (tl.mapM λ x => match x with | (k, v) => do let v' ← f v ; pure (k, v'))
      <;> simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none] at h₃
      <;> exact h₃ tl' h₅
    case some mtl' =>
      simp only [h₁, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq,
        List.mapM_cons, mk.injEq, exists_eq_right, List.cons.injEq, exists_eq_right_right,
        Prod.mk.injEq, true_and] at *
      apply And.intro h₂
      replace ⟨tl', h₃, h₄⟩ := h₃
      subst mtl'
      simp [h₃]

theorem mapMOnValues_some_implies_forall₂ [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  List.Forall₂ (λ kv₁ kv₂ => kv₁.fst = kv₂.fst ∧ f kv₁.snd = some kv₂.snd) m₁.kvs m₂.kvs
:= by
  unfold mapMOnValues kvs
  intro h₁
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h₁
  replace ⟨x, h₁, h₂⟩ := h₁
  subst h₂
  replace h₁ := List.mapM_some_iff_forall₂.mp h₁
  simp only
  apply List.Forall₂.imp _ h₁
  intro (k, v) (k', v') h₂
  simp only [Option.bind_eq_some, Option.some.injEq, Prod.mk.injEq, exists_eq_right_right] at h₂
  replace ⟨h₂, h₂'⟩ := h₂
  subst k'
  simp only [true_and]
  exact h₂

theorem mapMOnValues_some_implies_all_some {α : Type 0} [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  ∀ kv ∈ m₁.kvs, ∃ v, (kv.fst, v) ∈ m₂.kvs ∧ f kv.snd = some v
:= by
  intro h₁
  replace h₁ := List.forall₂_implies_all_left (mapMOnValues_some_implies_forall₂ h₁)
  intro (k, v) h₂
  replace ⟨(k', v'), h₁, h₃, h₄⟩ := h₁ (k, v) h₂
  simp only at *
  subst k'
  exists v'

/--
  alternate proof of `mapMOnValues_some_implies_all_some`, which instead of
  relying on `mapMOnValues_some_implies_forall₂`, relies on
  `List.mapM_some_implies_all_some`.  Which do we prefer?
-/
theorem mapMOnValues_some_implies_all_some_alt_proof [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  ∀ kv ∈ m₁.kvs, ∃ v, (kv.fst, v) ∈ m₂.kvs ∧ f kv.snd = some v
:= by
  unfold mapMOnValues
  intro h₁ kv h₂
  cases h₃ : m₁.kvs.mapM (λ x => match x with | (k, v) => do let v' ← f v ; pure (k, v'))
  <;> rw [h₃] at h₁
  <;> simp only [Option.pure_def, Option.bind_some_fun, Option.bind_none_fun, Option.some.injEq] at h₁
  case some ags =>
    subst h₁
    have (a, b) := kv ; clear kv
    simp only
    replace h₃ := List.mapM_some_implies_all_some h₃
    replace ⟨(a', g), h₃, h₄⟩ := h₃ (a, b) h₂
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq,
      Prod.mk.injEq, exists_eq_right_right] at h₄
    replace ⟨h₄, h₄'⟩ := h₄
    subst a'
    exists g

theorem mapMOnValues_some_implies_all_from_some [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  ∀ kv ∈ m₂.kvs, ∃ v, (kv.fst, v) ∈ m₁.kvs ∧ f v = kv.snd
:= by
  intro h₁
  replace h₁ := List.forall₂_implies_all_right (mapMOnValues_some_implies_forall₂ h₁)
  intro (k, v) h₂
  replace ⟨(k', v'), h₁, h₃, h₄⟩ := h₁ (k, v) h₂
  simp only at *
  subst k'
  exists v'

/--
  alternate proof of `mapMOnValues_some_implies_all_from_some`, which instead of
  relying on `mapMOnValues_some_implies_forall₂`, relies on
  `List.mapM_some_implies_all_from_some`. Which do we prefer?
-/
theorem mapMOnValues_some_implies_all_from_some_alt_proof [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = some m₂ →
  ∀ kv ∈ m₂.kvs, ∃ v, (kv.fst, v) ∈ m₁.kvs ∧ f v = kv.snd
:= by
  unfold mapMOnValues
  intro h₁ kv h₂
  cases h₃ : m₁.kvs.mapM (λ x => match x with | (k, v) => do let v' ← f v ; pure (k, v'))
  <;> rw [h₃] at h₁
  <;> simp only [Option.pure_def, Option.bind_some_fun, Option.bind_none_fun, Option.some.injEq] at h₁
  case some ags =>
    subst h₁
    have (a, g) := kv ; clear kv
    simp only
    replace h₃ := List.mapM_some_implies_all_from_some h₃
    replace ⟨(a', b), h₃, h₄⟩ := h₃ (a, g) h₂
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq,
      Prod.mk.injEq, exists_eq_right_right] at h₄
    replace ⟨h₄, h₄'⟩ := h₄
    subst a'
    exists b

theorem mapMOnValues_none_iff_exists_none {α : Type 0} [LT α] [DecidableLT α] {f : β → Option γ} {m : Map α β} :
  m.mapMOnValues f = none ↔ ∃ v ∈ m.values, f v = none
:= by
  constructor
  case mp =>
    intro h₁
    cases h₂ : m.kvs <;> simp only at h₁
    case nil =>
      rw [kvs_nil_iff_empty] at h₂ ; subst h₂
      simp [mapMOnValues_nil] at h₁
    case cons hd tl =>
      have (khd, vhd) := hd ; clear hd
      simp only [values_cons h₂, List.mem_cons, exists_eq_or_imp]
      simp only [mapMOnValues_cons h₂, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_none] at h₁
      cases h₃ : f vhd
      case none => simp only [true_or]
      case some yhd =>
        right
        specialize h₁ yhd h₃
        have := sizeOf_lt_of_tl h₂ -- required for Lean to allow the following recursive call
        apply mapMOnValues_none_iff_exists_none.mp
        by_contra h₄
        rw [← ne_eq] at h₄
        replace ⟨ytl, h₄⟩ := Option.ne_none_iff_exists'.mp h₄
        exact h₁ ytl h₄
  case mpr =>
    intro h₁
    replace ⟨v, h₁, h₂⟩ := h₁
    cases h₃ : m.kvs
    case nil =>
      rw [kvs_nil_iff_empty] at h₃ ; subst h₃
      simp [values, kvs, empty] at h₁
    case cons hd tl =>
      have (khd, vhd) := hd ; clear hd
      simp only [values_cons h₃, List.mem_cons] at h₁
      simp only [mapMOnValues_cons h₃, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none]
      intro yhd h₄ ytl h₅
      rcases h₁ with h₁ | h₁
      · subst h₁ ; simp [h₂] at h₄
      · replace h₅ := mapMOnValues_some_implies_all_some h₅
        replace ⟨k', h₁⟩ := in_values_exists_key h₁
        replace ⟨y, _, h₅⟩ := h₅ (k', v) h₁
        simp [h₂] at h₅
termination_by m

/--
  Note that the converse is not true:
  counterexample `m₁` is `[(1, false)]`, `m₂` is `[(1, false), (2, true)]`, `f` is `Except.ok`

  But for a limited converse, see `all_ok_implies_mapMOnValues_ok`
-/
theorem mapMOnValues_ok_implies_all_ok [LT α] [DecidableLT α] {f : β → Except ε γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = .ok m₂ →
  ∀ kv ∈ m₁.kvs, ∃ v, (kv.fst, v) ∈ m₂.kvs ∧ f kv.snd = .ok v
:= by
  unfold mapMOnValues
  intro h₁ kv h₂
  cases h₃ : m₁.kvs.mapM λ kv => match kv with | (k, v) => do let v' ← f v ; pure (k, v')
  <;> rw [h₃] at h₁
  <;> simp only [pure, Except.pure, Except.bind_ok, Except.bind_err, Except.ok.injEq] at h₁
  case ok ags =>
    subst h₁
    have (a, b) := kv ; clear kv
    simp only
    replace ⟨(a', g), h₃, h₄⟩ := List.mapM_ok_implies_all_ok h₃ (a, b) h₂
    simp [pure, Except.pure] at h₄
    cases h₅ : f b <;> simp [h₅] at h₄
    replace ⟨h₄, h₄'⟩ := h₄ ; subst a' g ; rename_i g
    exists g

theorem mapMOnValues_ok_implies_all_from_ok [LT α] [DecidableLT α] {f : β → Except ε γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.mapMOnValues f = .ok m₂ →
  ∀ kv ∈ m₂.kvs, ∃ v, (kv.fst, v) ∈ m₁.kvs ∧ f v = .ok kv.snd
:= by
  unfold mapMOnValues
  intro h₁ kv h₂
  cases h₃ : m₁.kvs.mapM λ kv => match kv with | (k, v) => do let v' ← f v ; pure (k, v')
  <;> rw [h₃] at h₁
  <;> simp only [pure, Except.pure, Except.bind_ok, Except.bind_err, Except.ok.injEq] at h₁
  case ok ags =>
    subst h₁
    have (a, g) := kv ; clear kv
    simp only
    replace ⟨(a', b), h₃, h₄⟩ := List.mapM_ok_implies_all_from_ok h₃ (a, g) h₂
    simp [pure, Except.pure] at h₄
    cases h₅ : f b <;> simp [h₅] at h₄
    replace ⟨h₄, h₄'⟩ := h₄ ; subst a' g ; rename_i g
    exists b

theorem all_ok_implies_mapMOnValues_ok [LT α] [DecidableLT α] {f : β → Except ε γ} {m₁ : Map α β} :
  (∀ kv ∈ m₁.kvs, ∃ v, f kv.snd = .ok v) →
  ∃ m₂, m₁.mapMOnValues f = .ok m₂
:= by
  unfold mapMOnValues
  intro h₁
  cases h₂ : m₁.kvs.mapM λ kv => match kv with | (k, v) => do let v' ← f v ; pure (k, v')
  case ok ags => simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq, exists_eq']
  case error e =>
    exfalso
    replace ⟨(k, v), hkv, h₂⟩ := List.mapM_error_implies_exists_error h₂
    split at h₂ <;> rename_i h₂' <;> simp only [pure, Except.pure] at h₂
    simp only [Prod.mk.injEq] at h₂' ; replace ⟨h₂', h₂''⟩ := h₂' ; subst k v ; rename_i k v
    replace ⟨v', h₁⟩ := h₁ (k, v) hkv
    simp only [h₁, Except.bind_ok] at h₂

theorem mapMOnValues_error_implies_exists_error [LT α] [DecidableLT α] {f : β → Except ε γ} {m : Map α β} {e : ε} :
  m.mapMOnValues f = .error e → ∃ v ∈ m.values, f v = .error e
:= by
  simp only [mapMOnValues, pure, Except.pure]
  intro h₁
  rw [do_error] at h₁
  replace ⟨(k, v), hkv, h₁⟩ := List.mapM_error_implies_exists_error h₁
  rw [do_error] at h₁
  have h_values := in_list_in_values hkv
  exists v

/-! ### `sizeOf` -/

theorem find_means_mem
  {α : Type u} {β : Type v}
  [LT α] [DecidableLT α] [BEq α] [LawfulBEq α] [DecidableEq α]
  {m : Map α β}
  {k : α}
  {v : β}
  (h : m.find? k = some v) :
  (k,v) ∈ m.kvs
  := by
  cases m
  rename_i kvs
  induction kvs
  case nil =>
    simp [find?, List.find?] at h
  case cons head tail ih =>
    simp [kvs]
    cases head
    rename_i key value
    cases heq : decide (key = k) <;> simp at heq
    case _ =>
      have beq : (key == k) = false := by
        rw [beq_eq_false_iff_ne]
        assumption
      apply Or.inr
      simp [kvs] at ih
      apply ih
      simp [find?, List.find?, beq] at h
      simp [find?, List.find?]
      apply h
    case _ =>
      apply Or.inl
      subst heq
      simp [find?, List.find?] at h
      subst h
      rfl

-- If you can find a value in a map, that value is smaller than the map
theorem find_means_smaller
  {α β : Type}
  [LT α] [DecidableLT α] [DecidableEq α]
  {m : Map α β}
  {k : α}
  {v : β}
  {h : m.find? k = some v} :
  sizeOf v < sizeOf m := by
  have h₂ : (k,v) ∈ m.kvs := by
    apply find?_mem_toList
    assumption
  have s₁ : sizeOf v < sizeOf (k,v) := by simp
  have s₂ : sizeOf m.kvs < sizeOf m := by apply sizeOf_lt_of_kvs
  have s₃ : sizeOf (k,v) < sizeOf m.kvs := by
    apply List.sizeOf_lt_of_mem
    assumption
  omega

end Cedar.Data.Map
