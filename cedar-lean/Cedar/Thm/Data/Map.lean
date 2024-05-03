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

/-! ### sizeOf -/

theorem sizeOf_lt_of_value [SizeOf α] [SizeOf β] {m : Map α β} {k : α} {v : β}
  (h : (k, v) ∈ m.1) :
  sizeOf v < sizeOf m
:= by
  simp only [Membership.mem] at h
  replace h := List.sizeOf_lt_of_mem h
  have v_lt_kv : sizeOf v < sizeOf (k, v) := by
    simp only [sizeOf, Prod._sizeOf_1]
    omega
  have m1_lt_m : sizeOf m.1 < sizeOf m := by
    simp only [sizeOf, _sizeOf_1]
    omega
  let a := sizeOf v
  let c := sizeOf m.1
  let d := sizeOf m
  have v_lt_m1 : a < c := by apply Nat.lt_trans v_lt_kv h
  have v_lt_m : a < d := by apply Nat.lt_trans v_lt_m1 m1_lt_m
  have ha : a = sizeOf v := by simp
  have hd : d = sizeOf m := by simp
  rw [ha, hd] at v_lt_m
  exact v_lt_m

theorem sizeOf_lt_of_tl [SizeOf α] [SizeOf β] {m : Map α β} {tl : List (α × β)}
  (h : m.kvs = (k, v) :: tl) :
  1 + sizeOf tl < sizeOf m
:= by
  conv => rhs ; unfold sizeOf _sizeOf_inst _sizeOf_1
  simp only
  unfold kvs at h
  simp only [h, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
  generalize sizeOf k = kn
  generalize sizeOf v = vn
  generalize sizeOf tl = tn
  omega

/-! ### Well-formed maps -/

def WellFormed {α β} [LT α] [DecidableLT α] (m : Map α β) :=
  m = Map.make m.toList

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

/-! ### contains, mem, kvs, values -/

theorem kvs_nil_iff_empty {m : Map α β} :
  m.kvs = [] ↔ m = Map.empty
:= by
  unfold kvs empty
  constructor <;> intro h
  case mp => match m with
    | mk [] => trivial
    | mk ((k, v) :: kvs) => trivial
  case mpr => simp [h]

theorem in_list_in_map {α : Type u} (k : α) (v : β) (m : Map α β) :
  (k, v) ∈ m.kvs → k ∈ m
:= by
  intro h₀
  have h₁ : k ∈ (List.map Prod.fst m.kvs) := by simp only [List.mem_map] ; exists (k, v)
  apply h₁

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
  intro kv h₁ h₂
  subst h₂
  exists kv.fst

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
  exact @h₂ (k, v) h₁

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

/-! ### find? and mapOnValues -/

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
      simp
    case some kv =>
      simp only [Option.some.injEq]
      have h₃ := List.find?_some h₂
      simp only [beq_iff_eq] at h₃
      subst h₃
      replace h₃ := List.mem_of_find?_eq_some h₂
      apply (key_maps_to_one_value kv.fst v kv.snd m wf h₁ _).symm
      trivial
  case mpr => exact find?_mem_toList

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
  cases m.1.find? (λ x => x.fst == k) <;> simp

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

theorem values_mapOnValues [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} :
  (m.mapOnValues f).values = m.values.map f
:= by
  unfold mapOnValues values kvs
  induction m.1
  case nil => simp
  case cons hd tl ih =>
    simp only [List.map_cons, List.cons.injEq, true_and]
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

theorem in_values_iff_findOrErr_ok [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {v : β} {e : Error}
  (wf : m.WellFormed) :
  v ∈ m.values ↔ ∃ k, m.findOrErr k e = .ok v
:= by
  simp only [values, List.mem_map, findOrErr_ok_iff_find?_some]
  constructor
  case mp =>
    intro h₁
    replace ⟨⟨k, v'⟩, ⟨h₁, h₂⟩⟩ := h₁
    simp only at h₂
    subst v'
    exists k
    simp [h₁, ← in_list_iff_find?_some wf]
  case mpr =>
    intro h₁
    replace ⟨k, h₁⟩ := h₁
    exists (k, v)
    simp [h₁, in_list_iff_find?_some wf, and_true]

theorem in_kvs_in_mapOnValues [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} {v : β} :
  (k, v) ∈ m.kvs → (k, f v) ∈ (m.mapOnValues f).kvs
:= by
  unfold mapOnValues
  intro h₁
  simp only [kvs, List.mem_map, Prod.mk.injEq]
  exists (k, v)

/-! ### mapMOnValues -/

/--
  This is not stated in terms of `Map.keys` because `Map.keys` produces a `Set`,
  and we want the even stronger property that it not only preserves the key-set,
  but also the key-order. (We'll use this to prove `mapMOnValues_wf`.)
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

theorem mapMOnValues_wf [LT α] [DecidableLT α] [StrictLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.WellFormed →
  (m₁.mapMOnValues f = some m₂) →
  m₂.WellFormed
:= by
  simp only [wf_iff_sorted, toList]
  intro wf h₁
  have h₂ := mapMOnValues_preserves_keys h₁
  exact (List.map_eq_implies_sortedBy h₂).mp wf

/--
  Alternate proof of `mapMOnValues_wf`, that relies on
  `List.mapM_some_eq_filterMap` instead of `mapMOnValues_preserves_keys`. Which do
  we prefer?
-/
theorem mapMOnValues_wf_alt_proof [LT α] [DecidableLT α] [StrictLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
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
      case none => simp
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


end Cedar.Data.Map
