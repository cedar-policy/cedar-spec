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

theorem wf_implies_tail_wf {α β} [LT α] [DecidableLT α] [StrictLT α]
  {hd : α × β} {tl : List (α × β)}
  (hwf : (mk (hd :: tl)).WellFormed) :
  (mk tl).WellFormed
:= by
  have := wf_iff_sorted.mp hwf
  cases tl with
  | nil =>
    simp [Map.WellFormed, Map.toList, Map.kvs, make, List.canonicalize]
  | cons hd2 tl =>
    apply wf_iff_sorted.mpr
    cases this
    simp only [Map.toList, Map.kvs]
    assumption

theorem wf_empty {α β} [LT α] [DecidableLT α] :
  (Map.empty : Map α β).WellFormed
:= by simp [Map.WellFormed, Map.make, Map.empty, List.canonicalize, Map.toList]

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
  exists v

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

theorem find?_some_implies_contains {α β} [BEq α] {m : Map α β} {k : α} {v : β} :
  m.find? k = .some v → m.contains k
:= by
  intros h
  apply contains_iff_some_find?.mpr
  simp [h]

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

private theorem insertCanonical_preserves_find_other_element
  [LT α] [DecidableLT α] [BEq α] [StrictLT α]
  (k : α)
  (x : (α × β)) (xs : List (α × β))  :
  (x.fst == k) = false →
  (List.insertCanonical Prod.fst x xs).find? (λ x => x.fst == k) =
  xs.find? (λ x => x.fst == k)
:= by
  intro h₁
  unfold List.insertCanonical
  split
  . simp
    assumption
  . simp
    split
    . simp [List.find?]
      rw [h₁]
    . split
      . unfold List.find?
        rename_i tl h₂ h₃
        have ih := insertCanonical_preserves_find_other_element k x tl h₁
        rw [ih]
      . unfold List.find?
        rw [h₁]
        simp
        rename_i hd₂ tl₂ h₂ h₃
        rename LT α => i₁
        rename StrictLT α => i₂
        have h₄ := @StrictLT.if_not_lt_gt_then_eq α i₁ i₂ x.fst hd₂.fst h₂ h₃
        rw [← h₄]
        rw [h₁]

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
  split at h₁ <;> simp only [Option.some.injEq, reduceCtorEq] at h₁
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
    split at h₃ <;> simp only [Option.some.injEq, reduceCtorEq] at h₃
    · subst v ; rename_i k' v h₂
      simp only [h₂, Option.some.injEq, Prod.mk.injEq, and_true]
      simpa using List.find?_some h₂
  case mpr =>
    split <;> simp ; rename_i k' v h₂
    · apply h₁ ; clear h₁
      have h₃ := List.find?_some h₂ ; simp at h₃ ; subst k'
      replace h₂ := List.mem_of_find?_eq_some h₂
      exact in_list_in_keys h₂

theorem find?_none_all_absent [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} :
  m.find? k = none → ∀ v, ¬ (k, v) ∈ m.kvs
:= by
  intro hn v
  by_contra hc
  simp only [find?] at hn
  cases hf : List.find? (fun x => x.fst == k) m.kvs <;>
  simp only [hf, reduceCtorEq] at hn
  simp only [List.find?_eq_none, beq_iff_eq] at hf
  specialize hf (k, v) hc
  simp only [not_true_eq_false] at hf

theorem in_list_implies_contains {α β}
  [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {m : Map α β} {k : α} {v : β} :
  (k, v) ∈ m.kvs → m.contains k
:= by
  intros h
  cases hfind : m.find? k with
  | none =>
    have := find?_none_all_absent hfind v h
    contradiction
  | some =>
    apply contains_iff_some_find?.mpr
    simp [hfind]

theorem all_absent_find?_none [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} :
  (∀ v, (k, v) ∉ m.kvs) → m.find? k = none
:= by
  cases h₁ : m.kvs
  case nil =>
    intros
    have hm : m = Map.mk [] := by
      rw [(by simp : m = Map.mk m.kvs), h₁]
    subst m
    simp [Map.find?, List.find?]
  case cons head tail =>
    intro hi
    have hm : m = Map.mk (head :: tail) := by
      rw [(by simp : m = Map.mk m.kvs), h₁]
    subst m
    simp only [List.mem_cons, not_or, ne_eq] at hi
    simp only [Map.find?, List.find?]
    have hh : head.fst ≠ k := by
      intro hh
      apply (hi head.snd).left
      simp [←hh]
    replace hh : (head.fst == k) = false := by
      simp [hh]
    simp only [hh]
    have hi₂ : ∀ v, (k, v) ∉ tail := by simp [hi]
    have ih := all_absent_find?_none hi₂
    simpa [Map.find?, Map.kvs] using ih

theorem find?_none_iff_all_absent [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {k : α} :
  m.find? k = none ↔ ∀ v, ¬ (k, v) ∈ m.kvs
:= Iff.intro find?_none_all_absent all_absent_find?_none


theorem list_find?_some_iff_map_find?_some {α β: Type} [BEq α] [LawfulBEq α] {l: List (α × β)} {k : α} {v : β} :
  l.find? (λ x => x.1 == k) = .some (k, v) ↔
  (Map.mk l).find? k = .some v
:= by
  constructor
  case mp =>
    intro h₁
    simp [Map.find?]
    split
    case h_1 k₂ v₂ h₂ =>
      simp [Map.kvs] at h₂
      rw [h₁] at h₂
      simp at h₂
      rcases h₂ with ⟨h₂, h₃⟩
      rw [h₃]
    case h_2 h₂ =>
      specialize h₂ k v
      simp [Map.kvs] at h₂
      rw [h₁] at h₂
      contradiction
  case mpr =>
    intro h₁
    simp [Map.find?] at h₁
    split at h₁
    case h_1 k₂ v₂ h₂ =>
      simp [Map.kvs] at h₂
      rw [h₂]
      simp
      have h₃ := List.find?_some h₂
      simp at h₃
      injection h₁ ; rename_i h₁
      rw [h₁]
      rw [h₃]
      simp
    case h_2 =>
      contradiction

theorem list_find?_mapM_implies_exists_mapped {α β γ : Type} [BEq α] [LawfulBEq α] {ls : List (α × β)} (fn : β → Option γ) {ys: List (α × γ)} {k: α} {x : β} :
  List.mapM (fun x =>
              (fn x.2).bind
                (fun v => some (x.fst, v))) ls = some ys →
  ls.find? (λ x => x.1 == k) = .some (k, x) →
  ∃y, fn x = .some y ∧  ys.find? (λ x => x.1 == k) = .some (k, y)
:= by
  intro h₁ h₂
  rw [List.mapM_some_iff_forall₂] at h₁
  cases h₁
  case nil =>
    simp at h₂
  case cons hd₁ hd₂ tl₁ tl₂ h₃ h₄ =>
    simp [List.find?] at h₂
    split at h₂
    case h_1 x₂ h₅ =>
      injection h₂ ; rename_i h₂
      rw [h₂] at h₃
      simp at h₃
      cases h₆ : (fn x) <;> rw [h₆] at h₃
      case none =>
        simp at h₃
      case some y₂ =>
        simp at h₃
        rcases h₃ with ⟨h₃, h₇⟩
        exists y₂
        simp
    case h_2 x h₅ =>
      rw [← List.mapM_some_iff_forall₂] at h₄
      unfold List.find?
      have h₆ : (hd₂.fst == k) = false := by
        cases h₆ : (fn hd₁.snd) <;> rw [h₆] at h₃
        case none =>
          simp at h₃
        case some =>
          simp at h₃
          cases hd₂
          simp at h₅
          simp
          simp at h₃
          rcases h₃ with ⟨h₃, _⟩
          rw [← h₃]
          exact h₅
      rw [h₆]
      simp
      exact list_find?_mapM_implies_exists_mapped fn h₄ h₂


theorem list_find?_mapM_implies_exists_unmapped {α β γ : Type} [BEq α] [LawfulBEq α] {ls : List (α × β)} (fn : β → Option γ) {ys: List (α × γ)} {k: α} {y: γ} :
  List.mapM (fun x =>
              (fn x.2).bind
                (fun v => some (x.fst, v))) ls = some ys →
  ys.find? (λ x => x.1 == k) = .some (k, y) →
  ∃ x, fn x = some y ∧ (ls.find? (λ x => x.1 == k) = .some (k, x))
:= by
  intro h₁ h₂
  rw [List.mapM_some_iff_forall₂] at h₁
  cases h₁
  case nil =>
    simp at h₂
  case cons hd₁ hd₂ tl₁ tl₂ h₃ h₄=>
    simp [List.find?] at h₂
    split at h₂
    case h_1 x h₅ =>
      injection h₂ ; rename_i h₂
      rw [h₂] at h₃
      cases h₆ : (fn hd₁.snd) <;> rw [h₆] at h₃
      case none =>
        simp at h₃
      case some y₂ =>
        simp at h₃
        rcases h₃ with ⟨h₃, h₇⟩
        exists hd₁.snd
        rw [h₆, h₇]
        simp
        rw [h₃]
        simp
        cases hd₁
        simp at h₃
        rw [h₃]
    case h_2 x h₅ =>
      rw [← List.mapM_some_iff_forall₂] at h₄
      unfold List.find?
      have h₆ : (hd₁.fst == k) = false := by
        cases h₆ : (fn hd₁.snd) <;> rw [h₆] at h₃
        case none =>
          simp at h₃
        case some =>
          simp at h₃
          cases hd₂
          simp at h₅
          simp
          simp at h₃
          rcases h₃ with ⟨h₃, _⟩
          rw [h₃]
          exact h₅
      rw [h₆]
      simp
      exact list_find?_mapM_implies_exists_unmapped fn h₄ h₂


theorem find?_mapM_key_id {α β : Type} [BEq α] [LawfulBEq α] {ks : List α} {kvs : List (α × β)} {fn : α → Option β} {k: α}
  (h₁ : ks.mapM (λ k => do (k, ←fn k)) = some kvs)
  (h₂ : k ∈ ks) :
  (Map.mk kvs).find? k = fn k
:= by
  simp only [Map.find?, Map.kvs]
  cases h₂
  case head l =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h₁
    cases hf : fn k <;> simp only [hf, Option.bind_none, Option.bind_some, reduceCtorEq] at h₁
    cases ht₁ : (l.mapM (λ k => (fn k).bind λ v => some (k, v))) <;> simp [ht₁ , Option.bind_none, Option.bind_some, reduceCtorEq, Option.some.injEq] at h₁
    subst h₁
    simp
  case tail h t h₂  =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h₁
    cases hf : fn h <;> simp only [hf, Option.bind_none, Option.bind_some, reduceCtorEq] at h₁
    cases ht₁ : (t.mapM (λ k => (fn k).bind λ v => some (k, v))) <;> simp only [ht₁, Option.bind_none, Option.bind_some, reduceCtorEq, Option.some.injEq] at h₁
    subst h₁
    simp only [List.find?]
    cases h₃ : (h == k)
    · simp only
      exact find?_mapM_key_id ht₁ h₂
    · simp only [beq_iff_eq] at h₃
      simp [h₃, ←hf]

theorem mapM_key_id_key_none_implies_find?_none {α β : Type} [DecidableEq α] [LT α] [StrictLT α] [DecidableLT α] {ks : List α} {kvs : List (α × β)} {fn : α → Option β} {k: α}
  (h₂ : ks.mapM (λ k => do (k, ←fn k)) = some kvs)
  (h₁ : fn k = none) :
  (Map.make kvs).find? k = none
:= by
  by_cases h₃ : k ∈ ks
  case pos =>
    have ⟨ _, _, h₄ ⟩ := List.mapM_some_implies_all_some h₂ k h₃
    simp [h₁] at h₄
  case neg =>
    simp only [Map.find?_none_iff_all_absent, Map.kvs, Map.make]
    intro v hl'
    have h₄ := List.in_canonicalize_in_list hl'
    exact List.not_mem_implies_not_mem_mapM_key_id h₂ h₃ v h₄

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
  cases m.1.find? (λ x => x.fst == k) <;> simp only [Option.map_none, Option.map_some]

theorem find?_mapOnValues_some {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} {v : β} :
  m.find? k = .some v →
  (m.mapOnValues f).find? k = .some (f v)
:= by
  intro h₁
  rw [← find?_mapOnValues]
  simp [Option.map, h₁]

theorem find?_mapOnValues_some' {α β γ} [LT α] [DecidableLT α] [DecidableEq α] (f : β → γ) {m : Map α β} {k : α} {v : γ} :
  (m.mapOnValues f).find? k = .some v →
  (∃ v', m.find? k = .some v' ∧ v = f v')
:= by
  intro h
  simp only [find?, kvs, mapOnValues, List.find?_map] at h
  split at h <;> simp at h
  case _ heq =>
    subst h
    simp only [Option.map] at heq
    split at heq <;> simp at heq
    case _ y heq₁ =>
      exists y.snd
      have : ∀ x, ((fun x => x.fst == k) ∘ fun (x : α × β) => (x.fst, f x.snd)) x = (fun x => x.fst == k) x := by
        simp only [Function.comp_apply, implies_true]
      simp only [List.find?_compose (fun (x : α × β) => (x.fst, f x.snd)) (fun x => x.fst == k)
          (fun x => x.fst == k) this] at heq₁
      simp only [find?, kvs, heq₁, true_and]
      rcases heq with ⟨_, heq⟩
      subst heq
      rfl

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
  cases m.find? k <;> simp only [Except.ok.injEq, Option.some.injEq, reduceCtorEq]

theorem findOrErr_err_iff_find?_none [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {e : Error} :
  m.findOrErr k e = .error e ↔ m.find? k = none
:= by
  unfold findOrErr
  cases m.find? k <;> simp only [reduceCtorEq]

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
  `find?_some_iff_in_values` below
-/
theorem find?_some_implies_in_values [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} :
  m.find? k = .some v → v ∈ m.values
:= by
  intro h₁
  simp [values]
  exists k
  have h₂ := find?_mem_toList h₁ ; simp [toList] at h₂
  simp only [h₂]

/--
  The converse requires the `wf` precondition, and is available in
  `findOrErr_ok_iff_in_values` below
-/
theorem findOrErr_ok_implies_in_values [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} {v : β} {e : Error} :
  m.findOrErr k e = .ok v → v ∈ m.values
:= by
  simp only [findOrErr_ok_iff_find?_some]
  exact find?_some_implies_in_values

/--
  The `mp` direction of this does not need the `wf` precondition and, in fact,
  is available separately as `find?_some_implies_in_values` above
-/
theorem find?_some_iff_in_values [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {v : β}
  (wf : m.WellFormed) :
  (∃ k, m.find? k = .some v) ↔ v ∈ m.values
:= by
  constructor
  case mp =>
    intro ⟨k, h₁⟩
    exact find?_some_implies_in_values h₁
  case mpr =>
    simp only [values, List.mem_map]
    intro h₁
    replace ⟨⟨k, v'⟩, ⟨h₁, h₂⟩⟩ := h₁
    simp only at h₂
    subst v'
    exists k
    simp [h₁, ← in_list_iff_find?_some wf]

/--
  The `mp` direction of this does not need the `wf` precondition and, in fact,
  is available separately as `findOrErr_ok_implies_in_values` above
-/
theorem findOrErr_ok_iff_in_values [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {m : Map α β} {v : β} {e : Error}
  (wf : m.WellFormed) :
  (∃ k, m.findOrErr k e = .ok v) ↔ v ∈ m.values
:= by
  simp only [findOrErr_ok_iff_find?_some]
  exact find?_some_iff_in_values wf

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
  Given a hypothesis like:
    h: Data.Map.find? es uid = none
  Proves something like:
    Data.Map.findOrErr es uid Error.entityDoesNotExist = .error .entityDoesNotExist
-/
theorem find?_none_iff_findorErr_errors [LT α] [DecidableLT α] [DecidableEq α] {m : Map α β} {k : α} (e : Error) :
  m.find? k = none ↔ m.findOrErr k e = .error e
:= by
  constructor
  case mp =>
    intro h
    simp only [findOrErr, h]
  case mpr =>
    intro h₁
    simp only [findOrErr] at h₁
    cases h₂: m.find? k
    case none => simp
    case some =>
      rw [h₂] at h₁
      simp at h₁

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
  simp only [mapMOnValues, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h₁
  replace ⟨xs, h₁, h₂⟩ := h₁
  subst h₂
  cases h₂ : m₁.kvs <;> simp only [h₂, List.mapM_nil, List.mapM_cons, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
  <;> unfold kvs at *
  case nil =>
    subst h₁
    simp only [List.map_nil]
  case cons kv tl =>
    have (k, v) := kv ; clear kv
    replace ⟨(k', y), ⟨y', h₁, h₃⟩, ⟨tl', h₄, h₅⟩⟩ := h₁
    subst h₅
    simp only [Prod.mk.injEq, List.map_cons, List.cons.injEq] at *
    replace ⟨h₃, h₃'⟩ := h₃
    subst k' y'
    have ih := mapMOnValues_preserves_keys (m₁ := mk tl) (m₂ := mk tl') (f := f)
    simp only [mapMOnValues, kvs, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq, mk.injEq, exists_eq_right] at ih
    specialize ih h₄
    simp only [ih, and_self]

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
  simp only [mapMOnValues, Option.pure_def, do_some] at h₁
  replace ⟨xs, h₁, h₂⟩ := h₁
  subst h₂
  simp [kvs]
  replace h₁ := List.mapM_some_eq_filterMap h₁
  subst h₁
  apply List.filterMap_sortedBy _ wf
  intro (k, v) (k', v') h₁
  simp only at *
  cases h₂ : f v <;> simp [h₂] at h₁
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
    cases h₂ : f v <;> simp [h₂] at h₁
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
  case none => simp [h₁, h₂, mapMOnValues]
  case some v' =>
    cases h₃ : (mk tl).mapMOnValues f
    <;> simp only [Option.bind_none, Option.bind_some]
    <;> unfold mapMOnValues at *
    <;> simp only [h₁, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff,
          Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, List.mapM_cons]
    case none =>
      simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro kvs' v'' h₄ tl' h₅ h₆
      simp only [h₂, Option.some.injEq] at h₄
      subst v'' kvs'
      cases (tl.mapM λ x => match x with | (k, v) => do let v' ← f v ; pure (k, v'))
      <;> simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff, reduceCtorEq] at h₃
      <;> exact h₃ tl' h₅
    case some mtl' =>
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Map.mk.injEq, exists_eq_right, List.cons.injEq, exists_eq_right_right,
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
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
  replace ⟨x, h₁, h₂⟩ := h₁
  subst h₂
  replace h₁ := List.mapM_some_iff_forall₂.mp h₁
  simp only
  apply List.Forall₂.imp _ h₁
  intro (k, v) (k', v') h₂
  simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq, exists_eq_right_right] at h₂
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
  <;> simp only [Option.pure_def, Option.bind_some_fun, Option.bind_none_fun, Option.some.injEq, reduceCtorEq] at h₁
  case some ags =>
    subst h₁
    have (a, b) := kv ; clear kv
    simp only
    replace h₃ := List.mapM_some_implies_all_some h₃
    replace ⟨(a', g), h₃, h₄⟩ := h₃ (a, b) h₂
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
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
  <;> simp only [Option.pure_def, Option.bind_some_fun, Option.bind_none_fun, Option.some.injEq, reduceCtorEq] at h₁
  case some ags =>
    subst h₁
    have (a, g) := kv ; clear kv
    simp only
    replace h₃ := List.mapM_some_implies_all_from_some h₃
    replace ⟨(a', b), h₃, h₄⟩ := h₃ (a, g) h₂
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
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
        Option.bind_eq_none_iff, reduceCtorEq] at h₁
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
      simp only [mapMOnValues_cons h₃, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff]
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
  <;> simp only [pure, Except.pure, Except.bind_ok, Except.bind_err, Except.ok.injEq, reduceCtorEq] at h₁
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
  <;> simp only [pure, Except.pure, Except.bind_ok, Except.bind_err, Except.ok.injEq, reduceCtorEq] at h₁
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
    split at h₂ ; rename_i h₂' ; simp only [pure, Except.pure] at h₂
    simp only [Prod.mk.injEq] at h₂' ; replace ⟨h₂', h₂''⟩ := h₂' ; subst k v ; rename_i k v
    replace ⟨v', h₁⟩ := h₁ (k, v) hkv
    simp only [h₁, Except.bind_ok, reduceCtorEq] at h₂

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

theorem wellFormed_correct {α β} [LT α] [StrictLT α] [DecidableLT α] {m : Map α β} :
  m.wellFormed = true ↔ m.WellFormed
:= by
  constructor
  · intros h
    apply wf_iff_sorted.mpr
    apply List.isSortedBy_correct.mpr
    exact h
  · intros h
    apply List.isSortedBy_correct.mp
    apply wf_iff_sorted.mp
    exact h


/--
Helper for make_find?_eq_list_find?
-/
private theorem map_make_find?_in_tail
  [LT α] [StrictLT α] [BEq α] [LawfulBEq α]
  [DecidableLT α]
  [SizeOf α] [SizeOf β]
  {hd : (α × β)} {tl : List (α × β)} {k : α} :
  ¬(hd.1 = k) →
  (Map.make (hd :: tl)).find? k = (Map.make tl).find? k
:= by
  simp [Map.make]
  intro h₁
  simp [List.canonicalize]
  unfold List.insertCanonical
  split
  . simp [Map.find?, List.find?]
    split
    . rename_i h₂
      split at h₂ <;> rename_i h₃
      . simp at h₃
        contradiction
      . contradiction
    . rename_i h₃ _ _
      rw [h₃]
      simp [Map.kvs]
  . simp
    split
    case h_2.isTrue hd₂ tl₂ h₃ h₄ =>
      unfold Map.find?
      simp [List.find?]
      split <;> rename_i h₅
      . split at h₅ <;> rename_i h₆
        . simp at h₆
          contradiction
        . rw [h₅]
      . simp at h₅
        have h₆ : (hd.fst == k) = false := by
          simp
          assumption
        rw [h₆] at h₅
        simp at h₅
        split
        case h_1 h₇ =>
          rename α => k
          rename β => v
          rw [h₇] at h₅
          specialize h₅ k v
          contradiction
        case h_2 => simp
    case h_2.isFalse xs hd₂ tl₂ h₃ h₄ =>
      rw [h₃]
      rename LT α => i₁
      rename StrictLT α => i₂
      split
      case isTrue h₅ =>
        simp [Map.find?, List.find?]
        cases h₆: hd₂.fst == k
        case false =>
          simp
          have h₇ : (hd.fst == k) = false := by
            simp
            assumption
          have h₈ := insertCanonical_preserves_find_other_element k hd tl₂ h₇
          rw [h₈]
        case true =>
          simp
      case isFalse h₅ =>
        have h₆ := @StrictLT.if_not_lt_gt_then_eq α i₁ i₂ hd.fst hd₂.fst h₄ h₅
        simp [Map.find?, List.find?]
        rw [← h₆]
        have h₈ : (hd.fst == k) = false := by simp; assumption
        rw [h₈]

theorem make_find?_eq_list_find?
  [DecidableEq α] [LT α] [DecidableLT α]
  [Cedar.Data.StrictLT α]
  {l : List (α × β)}
  {k : α} :
  (make l).find? k = (List.find? (λ x => x.fst == k) l).map Prod.snd
   := by
  cases l
  case nil =>
    simp [make, List.canonicalize, Map.find?, List.find?]
  case cons hd tl =>
    simp [List.find?]
    split
    case h_1 x h₁ =>
      simp [make, List.canonicalize, Map.find?, Map.kvs]
      simp at h₁
      rw [← h₁]
      rw [List.insertCanonical_find? (f := Prod.fst) hd]
    case h_2 x h₃ =>
      simp at h₃
      rw [map_make_find?_in_tail h₃]
      rw [make_find?_eq_list_find?]


theorem list_find?_iff_make_find?
  [DecidableEq α] [LT α] [DecidableLT α]
  [Cedar.Data.StrictLT α]
  {l : List (α × β)}
  {k : α} {v : β} :
  List.find? (λ x => x.fst == k) l = some (k, v) ↔
  (make l).find? k = some v := by
  rw [make_find?_eq_list_find?]
  simp
  constructor
  case mp =>
    intro h
    exists k
  case mpr =>
    intro h
    replace ⟨k₂, h⟩ := h
    have h₂ := List.find?_some h
    simp at h₂
    rw [h₂] at h
    exact h

theorem list_find?_iff_mk_find?
  [DecidableEq α] [LT α] [DecidableLT α]
  [Cedar.Data.StrictLT α]
  {l : List (α × β)}
  {k : α} {v : β} :
  List.find? (λ x => x.fst == k) l = some (k, v) ↔
  (mk l).find? k = some v := by
  constructor
  case mp =>
    intro h₁
    simp [Map.find?, Map.kvs]
    rw [h₁]
  case mpr =>
    intro h₁
    simp [Map.find?, Map.kvs] at h₁
    split at h₁
    case h_1 k₂ v₂ h₂ =>
      injection h₁ ; rename_i h₁
      have h₃ := List.find?_some h₂
      simp at h₃
      rw [h₁, h₃] at h₂
      exact h₂
    case h_2 =>
      contradiction

/--
If a key exists in `l₂` but not in `l₁`,
then `Map.make (l₁ ++ l₂)` contains that key.
-/
theorem map_make_append_find_disjoint
  [LT α] [StrictLT α] [DecidableEq α] [DecidableLT α]
  [SizeOf α] [SizeOf β]
  {l₁ : List (α × β)} {l₂ : List (α × β)} {k : α}
  (hfind₁ : l₁.find? (λ ⟨k', _⟩ => k' == k) = none)
  (hfind₂ : (l₂.find? (λ ⟨k', _⟩ => k' == k)).isSome) :
  ∃ v,
    (Map.make (l₁ ++ l₂)).find? k = some v ∧
    (k, v) ∈ l₂
:= by
  have hwf : (Map.make (l₁ ++ l₂)).WellFormed := by
    exact Map.make_wf _
  have hsub :
    (Map.make (l₁ ++ l₂)).kvs ⊆ l₁ ++ l₂
  := by
    apply List.canonicalize_subseteq
  simp [Subset, List.Subset] at hsub
  have ⟨v, hv⟩ :
    ∃ v, (Map.make (l₁ ++ l₂)).find? k = some v
  := by
    simp only [Option.isSome] at hfind₂
    split at hfind₂
    rotate_left
    contradiction
    rename_i kv hkv
    exists kv.snd
    rw [make_find?_eq_list_find?]
    rw [List.find?_append]
    rw [hkv, hfind₁]
    simp
  simp only [hv, Option.some.injEq, exists_eq_left']
  have := Map.find?_mem_toList hv
  have := hsub k v this
  cases this with
  | inl hmem₁ =>
    have := List.find?_eq_none.mp hfind₁
    specialize this (k, v) hmem₁
    simp at this
  | inr h => exact h

theorem make_map_values_find
  [DecidableEq α] [LT α] [DecidableLT α]
  [Cedar.Data.StrictLT α]
  {l : List α}
  {f : α → β}
  {k : α}
  (hfind : k ∈ l) :
  (Map.make (l.map (λ x => (x, f x)))).find? k =
  .some (f k)
:= by
  rw [make_find?_eq_list_find?]
  simp only [List.find?_map, Option.map_eq_some_iff]
  unfold Function.comp
  simp
  exists k
  exists k
  simp
  rw [List.find?_exact_iff_mem.mpr hfind]

theorem map_toList_findSome?
  [BEq α] [LawfulBEq α]
  {m : Map α β} {k : α} {v : β} {v' : γ}
  {f : α × β → Option γ}
  (hfind : Map.find? m k = .some v)
  (hf : ∀ kv, (∃ v', f kv = .some v') → kv.1 = k)
  (hkv : f (k, v) = .some v') :
  m.toList.findSome? f = .some v'
:= by
  cases m with | mk m =>
  simp only [Map.toList, Map.kvs, Map.find?] at hfind ⊢
  split at hfind
  · rename_i heq
    simp only [Option.some.injEq] at hfind
    simp [hfind] at heq
    induction m with
    | nil => contradiction
    | cons hd tl ih =>
      simp only [List.findSome?]
      simp only [List.find?] at heq
      split
      · rename_i fhd heq'
        split at heq
        · rename_i heq''
          simp only [Option.some.injEq] at heq
          simp only [beq_iff_eq, heq] at heq''
          simp only [heq''] at heq
          simp only [heq] at heq'
          simp only [heq'] at hkv
          simp [hkv]
        · rename_i heq''
          simp only [beq_eq_false_iff_ne, ne_eq] at heq''
          apply False.elim
          apply heq''
          apply hf
          exists fhd
      · split at heq
        · rename_i h₁ _ h₂
          simp only [beq_iff_eq] at h₂
          simp only [Option.some.injEq] at heq
          simp only [heq] at h₂
          simp only [h₂] at heq
          simp only [heq] at h₁
          simp only [hkv] at h₁
          contradiction
        · exact ih heq
  · contradiction

theorem map_find?_to_list_find?
  [BEq α] [LawfulBEq α]
  {m : Map α β} {k : α} {v : β}
  (hfind : Map.find? m k = .some v) :
  List.find? (λ x => x.fst == k) (Map.toList m) = .some (k, v)
:= by
  simp only [Map.find?] at hfind
  split at hfind
  · rename_i heq
    simp only [Option.some.injEq] at hfind
    simp only [Map.toList, heq, hfind]
    have := List.find?_some heq
    simp only [beq_iff_eq] at this
    simp [this]
  · contradiction

/-- A variant of `map_make_append_find_disjoint`. -/
theorem map_make_append_find_disjoint'
  [LT α] [StrictLT α] [DecidableEq α] [DecidableLT α]
  [SizeOf α] [SizeOf β]
  {l₁ : List (α × β)} {l₂ : List (α × β)} {k : α} {v : β}
  (hfind₁ : l₁.find? (λ ⟨k', _⟩ => k' == k) = none)
  (hfind₂ : l₂.find? (λ ⟨k', _⟩ => k' == k) = .some (k, v))
  (heq : ∀ x₁ x₂, x₁ ∈ l₂ → x₂ ∈ l₂ → x₁.fst = x₂.fst → x₁ = x₂) :
  (Map.make (l₁ ++ l₂)).find? k = some v
:= by
  have : (l₂.find? (λ ⟨k', _⟩ => k' == k)).isSome
  := by simp only [hfind₂, Option.isSome]
  have ⟨v', hfind_k, hmem⟩ := map_make_append_find_disjoint hfind₁ this
  have := List.mem_of_find?_eq_some hfind₂
  have := heq _ _ this hmem
  simp only [Prod.mk.injEq, true_and, forall_const] at this
  simp only [this, hfind_k]

theorem map_find?_implies_find?_weaker_pred
  [BEq α] [LawfulBEq α]
  {m : Map α β} {k : α} {v : β} {f : α × β → Bool}
  (hfind : Map.find? m k = .some v)
  (hf : ∀ kv, f kv → kv.1 = k)
  (hkv : f (k, v)) :
  List.find? f (Map.toList m) = .some (k, v)
:= by
  replace hfind := map_find?_to_list_find? hfind
  cases m with | mk m =>
  simp only [Map.toList, Map.kvs] at hfind ⊢
  induction m with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.find?]
    split
    · rename_i heq
      have := hf hd heq
      simp only [List.find?, this, BEq.rfl, Option.some.injEq] at hfind
      simp [hfind]
    · rename_i heq
      apply ih
      simp only [List.find?] at hfind
      split at hfind
      · simp only [Option.some.injEq] at hfind
        simp only [←hfind] at hkv
        simp [hkv] at heq
      · exact hfind

theorem map_keys_empty_implies_map_empty
  {m : Map α β}
  (h : m.keys.toList = []) :
  m = (Map.mk [])
:= by
  cases m with | mk m =>
  cases m with
  | nil => rfl
  | cons hd tl =>
    simp only [Map.keys, List.map, Set.toList, Set.elts] at h
    contradiction

theorem toList_congr
  {m₁ m₂ : Map α β}
  (h : m₁.toList = m₂.toList) :
  m₁ = m₂
:= by
  cases m₁ with | mk m₁
  cases m₂ with | mk m₂
  simp only [Map.toList, Map.kvs] at h
  simp [h]

theorem find?_append
  [LT α] [StrictLT α] [DecidableEq α] [DecidableLT α]
  {m₁ m₂ : Map α β} {k : α}:
  (m₁ ++ m₂).find? k = (m₁.find? k).or (m₂.find? k)
:= by
  have h_append_eq : (m₁ ++ m₂).find? k = (Map.make (m₁.kvs ++ m₂.kvs)).find? k := by
    rfl
  rw [h_append_eq]
  rw [make_find?_eq_list_find?]
  rw [List.find?_append]
  simp [Map.find?, Option.map, Option.or]
  cases List.find? (fun x => x.fst == k) m₁.kvs
  . simp
    cases List.find? (fun x => x.fst == k) m₂.kvs <;> simp
  . simp

end Cedar.Data.Map
