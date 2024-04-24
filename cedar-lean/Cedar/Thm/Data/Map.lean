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

/--
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

/--
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

/--
  `make` on equivalent lists of (k,v) pairs produces equal maps

  (Organizationally belongs in the `make` section, but is needed before that)
-/
theorem make_eqv [LT α] [DecidableLT α] {xs ys : List (α × β)}:
  xs ≡ ys →
  Map.make xs = Map.make ys
:= by
  unfold make
  intro h₁
  sorry

/--
  If two well-formed maps have equivalent (k,v) sets, then the maps are actually
  equal
-/
theorem eq_iff_kvs_equiv [LT α] [DecidableLT α] {m₁ m₂ : Map α β}
  (wf₁ : m₁.WellFormed)
  (wf₂ : m₂.WellFormed) :
  m₁.kvs ≡ m₂.kvs ↔ m₁ = m₂
:= by
  constructor
  case mp =>
    intro h₁
    unfold WellFormed toList at wf₁ wf₂
    rw [wf₁]
    rw [wf₂]
    exact make_eqv h₁
  case mpr =>
    intro h₁
    subst h₁
    exact List.Equiv.refl

/-! ### contains, mem, and find? -/

theorem in_list_in_map {α : Type u} {k : α} {v : β} {m : Map α β} :
  (k, v) ∈ m.kvs → k ∈ m
:= by
  intro h₀
  have h₁ : k ∈ (List.map Prod.fst m.kvs) := by simp only [List.mem_map] ; exists (k, v)
  apply h₁

theorem in_kvs_in_values {k : α} {v : β} {m : Map α β} :
  (k, v) ∈ m.kvs → v ∈ m.values
:= by
  simp only [values, List.mem_map]
  intro h₁
  exists (k, v)

/-- kinda the converse of `in_kvs_in_values` -/
theorem in_values_exists_key {m : Map α β} {v : β} :
  v ∈ m.values → ∃ k, (k, v) ∈ m.kvs
:= by
  simp only [values, List.mem_map, forall_exists_index, and_imp]
  intro kv h₁ h₂
  subst h₂
  exists kv.fst

theorem in_list_some_find? [DecidableEq α] [LT α] [DecidableLT α] {k : α} {v : β} {m : Map α β} :
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
      simp only [Option.some.injEq]
      have h₄ := List.find?_some h₃
      simp only [beq_iff_eq] at h₄
      subst h₄
      replace h₃ := List.mem_of_find?_eq_some h₃
      apply (key_maps_to_one_value kv.fst v kv.snd m h₁ h₂ _).symm
      trivial
  case mpr =>
    intro h₂
    cases h₃ : m.kvs.find? λ x => match x with | (k', _) => k' == k
    case none => simp [h₃] at h₂
    case some kv =>
      simp only [h₃, Option.some.injEq] at h₂
      subst h₂
      have h₄ := List.mem_of_find?_eq_some h₃
      replace h₃ := List.find?_some h₃
      split at h₃ ; rename_i k' v
      simp only
      exact equal_keys_same_value k' k v m h₁ h₄ h₃

theorem contains_iff_some_find? {α β} [BEq α] {m : Map α β} {k : α} :
  m.contains k ↔ ∃ v, m.find? k = .some v
:= by simp [contains, Option.isSome_iff_exists]

theorem not_contains_of_empty {α β} [BEq α] (k : α) :
  ¬ (Map.empty : Map α β).contains k
:= by simp [contains, empty, find?, List.find?]

/-! ### make -/

theorem make_wf [LT α] [StrictLT α] [DecidableLT α] (xs : List (α × β)) :
  WellFormed (Map.make xs)
:= by
  simp [WellFormed, make, toList, kvs, List.canonicalize_idempotent]

/-
  Note that the converse of this is not true:
  counterexample `xs = [(1, false), (1, true)]`.
  Then `Map.make xs = [(1, false)]`.
-/
theorem mem_kvs_make [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  x ∈ (Map.make xs).kvs → x ∈ xs
:= by
  simp only [kvs, make]
  intro h₁
  have h₂ := List.canonicalize_subseteq Prod.fst xs
  simp only [List.subset_def] at h₂
  exact h₂ h₁

/--
  Very similar to `mem_kvs_make` above
-/
theorem mem_values_make [LT α] [StrictLT α] [DecidableLT α] {xs : List (α × β)} :
  v ∈ (Map.make xs).values → v ∈ xs.map Prod.snd
:= by
  -- despite the similarity to `mem_kvs_make`, the proof does not currently
  -- use `mem_kvs_make`
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

/-! ### find? and mapOnValues -/

theorem mapOnValues_wf [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} :
  m.WellFormed ↔ (m.mapOnValues f).WellFormed
:= by
  unfold mapOnValues WellFormed toList
  sorry

theorem mapOnValues_empty {α β γ} [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} :
  (empty : Map α β).mapOnValues f = empty
:= by
  simp [mapOnValues, empty]

theorem find?_mapOnValues {α β γ} [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α}  :
  (m.find? k).map f = (m.mapOnValues f).find? k
:= by
  simp only [find?, kvs, mapOnValues, ← List.find?_pair_map]
  cases m.1.find? (λ x => x.fst == k) <;> simp

theorem find?_mapOnValues_some {α β γ} [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} {v : β} :
  m.find? k = .some v →
  (m.mapOnValues f).find? k = .some (f v)
:= by
  intro h₁
  rw [← find?_mapOnValues]
  simp [Option.map, h₁]

theorem find?_mapOnValues_none {α β γ} [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} :
  m.find? k = .none →
  (m.mapOnValues f).find? k = .none
:= by
  intro h₁
  rw [← find?_mapOnValues]
  simp [Option.map, h₁]

theorem mapOnValues_eq_make_map {α β γ} [LT α] [StrictLT α] [DecidableLT α] {f : β → γ} {m : Map α β}
  (wf : m.WellFormed) :
  m.mapOnValues f = Map.make (m.toList.map λ kv => (kv.fst, f kv.snd))
:= by
  unfold WellFormed at wf
  simp only [make, toList, kvs, mapOnValues, mk.injEq] at *
  rw [wf] ; simp only ; rw [eq_comm]
  have h₁ : Prod.map id f = (λ (x : α × β) => (x.fst, f x.snd)) := by unfold Prod.map ; simp only [id_eq]
  simp only [← h₁, ← List.canonicalize_of_map_fst, List.canonicalize_idempotent]

theorem mapOnValues_contains {α β γ} [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} :
  Map.contains m k = Map.contains (Map.mapOnValues f m) k
:= by
  simp only [contains, Option.isSome]
  split
  case h_1 h => simp [find?_mapOnValues_some h]
  case h_2 h => simp [find?_mapOnValues_none h]

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

theorem in_values_iff_findOrErr_ok [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {v : β} {e : Error}
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
    simp [h₁, ← in_list_some_find? wf]
  case mpr =>
    intro h₁
    replace ⟨k, h₁⟩ := h₁
    exists (k, v)
    simp [h₁, in_list_some_find? wf, and_true]

theorem in_kvs_in_mapOnValues [LT α] [DecidableLT α] [DecidableEq α] {f : β → γ} {m : Map α β} {k : α} {v : β} :
  (k, v) ∈ m.kvs → (k, f v) ∈ (m.mapOnValues f).kvs
:= by
  unfold mapOnValues
  intro h₁
  simp only [kvs, List.mem_map, Prod.mk.injEq]
  exists (k, v)

/-! ### mapMOnValues -/

theorem mapMOnValues_wf [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  m₁.WellFormed →
  (m₁.mapMOnValues f = some m₂) →
  m₂.WellFormed
:= by
  unfold WellFormed toList
  intro wf h₁
  simp only [mapMOnValues, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
    Option.some.injEq] at h₁
  replace ⟨xs, h₁, h₂⟩ := h₁
  subst h₂
  sorry

/--
  Analogue of `List.mapM_eq_some` for Map.mapMOnValues
-/
theorem mapMOnValues_eq_some [LT α] [DecidableLT α] {f : β → Option γ} {m₁ : Map α β} {m₂ : Map α γ} :
  (m₁.mapMOnValues f = some m₂) → (
    (∀ kv ∈ m₁.kvs, ∃ v, (kv.fst, v) ∈ m₂.kvs ∧ f kv.snd = some v) ∧
    (∀ kv ∈ m₂.kvs, ∃ v, (kv.fst, v) ∈ m₁.kvs ∧ f v = kv.snd)
  )
:= by
  unfold mapMOnValues
  intro h₁
  constructor
  <;> intro kv h₂
  <;> cases h₃ : m₁.kvs.mapM (λ x => match x with | (k, v) => do let v' ← f v ; pure (k, v'))
  <;> rw [h₃] at h₁
  <;> simp only [Option.pure_def, Option.bind_some_fun, Option.bind_none_fun, Option.some.injEq] at h₁
  <;> subst h₁
  case left.some ags =>
    have (a, b) := kv ; clear kv
    simp only
    replace ⟨h₃, _⟩ := List.mapM_eq_some h₃
    replace ⟨(a', g), h₃, h₄⟩ := h₃ (a, b) h₂
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq,
      Prod.mk.injEq, exists_eq_right_right] at h₄
    replace ⟨h₄, h₄'⟩ := h₄
    subst a'
    exists g
  case right.some ags =>
    have (a, g) := kv ; clear kv
    simp only
    replace ⟨_, h₃⟩ := List.mapM_eq_some h₃
    replace ⟨(a', b), h₃, h₄⟩ := h₃ (a, g) h₂
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq,
      Prod.mk.injEq, exists_eq_right_right] at h₄
    replace ⟨h₄, h₄'⟩ := h₄
    subst a'
    exists b

/--
  Analogue of `List.isSome_mapM` for Map.mapMOnValues
-/
theorem isSome_mapMOnValues [LT α] [DecidableLT α] {f : β → Option γ} {m : Map α β} :
  Option.isSome (m.mapMOnValues f) ↔ ∀ v ∈ m.values, Option.isSome (f v)
:= by
  constructor
  case mp =>
    intro h₁ v h₂
    rw [Option.isSome_iff_exists]
    rw [Option.isSome_iff_exists] at h₁
    replace ⟨m', h₁⟩ := h₁
    replace ⟨h₁, _⟩ := mapMOnValues_eq_some h₁
    have ⟨k, h₃⟩ := in_values_exists_key h₂
    replace ⟨v', _, h₁⟩ := h₁ (k, v) h₃
    simp at h₁
    exists v'
  case mpr =>
    unfold Map.mapMOnValues
    intro h₁
    cases h₂ : m.kvs.mapM (λ x => match x with | (k, v) => do let v' ← f v ; pure (k, v'))
    <;> simp only [Option.pure_def, Option.bind_none_fun, Option.bind_some_fun, Option.isSome_none, Option.isSome_some]
    case none =>
      replace ⟨(k, v), h₂, h₃⟩ := List.mapM_eq_none.mp h₂
      specialize h₁ v (in_kvs_in_values h₂)
      cases h₄ : f v
      case some => simp [h₄] at h₃
      case none => simp [h₄] at h₁

/--
  Analogue of `List.mapM_eq_none` for Map.mapMOnValues

  Corollary of `isSome_mapMOnValues`
-/
theorem mapMOnValues_eq_none [LT α] [DecidableLT α] {f : β → Option γ} {m : Map α β} :
  m.mapMOnValues f = none ↔ ∃ v ∈ m.values, f v = none
:= by
  -- As of this writing, this proof is nearly syntactically identical to the
  -- proof of `List.mapM_eq_none`
  constructor
  case mp =>
    intro h₁
    by_contra h₂
    replace h₂ := forall_not_of_not_exists h₂
    simp only [not_and] at h₂
    rw [← Option.not_isSome_iff_eq_none] at h₁
    rw [isSome_mapMOnValues] at h₁
    apply h₁ ; clear h₁
    intro v h₁
    specialize h₂ v h₁
    rw [← ne_eq] at h₂
    rw [Option.ne_none_iff_isSome] at h₂
    exact h₂
  case mpr =>
    intro h₁
    replace ⟨v, h₁, h₂⟩ := h₁
    rw [← Option.not_isSome_iff_eq_none]
    intro h₃
    rw [isSome_mapMOnValues] at h₃
    specialize h₃ v h₁
    simp [h₂] at h₃

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


end Cedar.Data.Map
