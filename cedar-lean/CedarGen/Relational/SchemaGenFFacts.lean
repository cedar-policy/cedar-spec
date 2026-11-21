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

import CedarGen.Relational.SchemaGenFMono
import Cedar.Thm.Validation.Relational.EnvironmentValidation

/-! # Facts about the functions `GenTypeEnvF` computes

Deduplication and sorting (what they keep, when they are the identity), the transitive closure
(it keeps the keys and everything but the ancestors, draws its ancestors from the given ones,
keeps sets sorted, and is the identity on a closed hierarchy), and the rank filter. -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.Validation.Relational.Schema

/-! ## Membership relations -/

theorem definedEntityType_iff_mem {ets : List EntityType} {x : EntityType} :
    DefinedEntityType ets x ↔ x ∈ ets := by
  constructor
  · intro h
    induction h with
    | here => exact List.mem_cons_self
    | there _ _ _ _ _ ih => exact List.mem_cons_of_mem _ ih
  · intro h
    induction ets with
    | nil => cases h
    | cons y ys ih =>
      by_cases hxy : x = y
      · subst hxy; exact .here _ _
      · exact .there _ _ _ hxy (ih ((List.mem_cons.mp h).resolve_left hxy))

theorem definedUID_iff_mem {us : List EntityUID} {x : EntityUID} : DefinedUID us x ↔ x ∈ us := by
  constructor
  · intro h
    induction h with
    | here => exact List.mem_cons_self
    | there _ _ _ _ _ ih => exact List.mem_cons_of_mem _ ih
  · intro h
    induction us with
    | nil => cases h
    | cons y ys ih =>
      by_cases hxy : x = y
      · subst hxy; exact .here _ _
      · exact .there _ _ _ hxy (ih ((List.mem_cons.mp h).resolve_left hxy))

theorem notInET_iff {x : EntityType} {ks : List EntityType} : NotInET x ks ↔ x ∉ ks := by
  constructor
  · intro h
    induction h
    case nil => simp
    case cons hne _ ih =>
      simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩
  · intro h
    induction ks with
    | nil => exact .nil _
    | cons k ks ih =>
      simp only [List.mem_cons, not_or] at h
      exact .cons _ _ _ h.1 (ih h.2)

theorem notInUID_iff {x : EntityUID} {us : List EntityUID} : NotInUID x us ↔ x ∉ us := by
  constructor
  · intro h
    induction h
    case nil => simp
    case cons hne _ ih =>
      simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩
  · intro h
    induction us with
    | nil => exact .nil _
    | cons k ks ih =>
      simp only [List.mem_cons, not_or] at h
      exact .cons _ _ _ h.1 (ih h.2)

theorem subET_sub {xs ys : List EntityType} (h : SubET xs ys) : ∀ y ∈ ys, y ∈ xs := by
  induction h with
  | nil => simp
  | skip _ _ _ _ ih => exact fun y hy => List.mem_cons_of_mem _ (ih y hy)
  | pick _ _ _ _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih y hy)

theorem subUID_sub {xs ys : List EntityUID} (h : SubUID xs ys) : ∀ y ∈ ys, y ∈ xs := by
  induction h with
  | nil => simp
  | skip _ _ _ _ ih => exact fun y hy => List.mem_cons_of_mem _ (ih y hy)
  | pick _ _ _ _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih y hy)

theorem subET_self : ∀ xs : List EntityType, SubET xs xs
  | [] => .nil
  | x :: xs => .pick _ _ _ (subET_self xs)

/-! ## Deduplication -/

theorem mem_dedupKeep {α} [DecidableEq α] {x : α} : ∀ {xs : List α}, x ∈ dedupKeep xs ↔ x ∈ xs
  | [] => by simp [dedupKeep]
  | y :: ys => by
    unfold dedupKeep
    split
    · rw [mem_dedupKeep]
      constructor
      · exact List.mem_cons_of_mem _
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · assumption
        · exact h
    · simp only [List.mem_cons, mem_dedupKeep]

theorem nodup_dedupKeep {α} [DecidableEq α] : ∀ (xs : List α), (dedupKeep xs).Nodup
  | [] => by simp [dedupKeep]
  | y :: ys => by
    unfold dedupKeep
    split
    · exact nodup_dedupKeep ys
    next h =>
      exact List.nodup_cons.mpr ⟨fun hm => h (mem_dedupKeep.mp hm), nodup_dedupKeep ys⟩

theorem dedupKeep_of_nodup {α} [DecidableEq α] : ∀ {xs : List α}, xs.Nodup → dedupKeep xs = xs
  | [], _ => rfl
  | y :: ys, h => by
    have ⟨h₁, h₂⟩ := List.nodup_cons.mp h
    unfold dedupKeep
    rw [if_neg h₁, dedupKeep_of_nodup h₂]

theorem dedupKeys_sub {α β} [DecidableEq α] : ∀ {xs : List (α × β)} {p}, p ∈ dedupKeys xs → p ∈ xs
  | [], _, h => by simp [dedupKeys] at h
  | q :: qs, p, h => by
    unfold dedupKeys at h
    split at h
    · exact List.mem_cons_of_mem _ (dedupKeys_sub h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (dedupKeys_sub h)

theorem dedupKeys_keys_sub {α β} [DecidableEq α] : ∀ {xs : List (α × β)} {k},
    k ∈ (dedupKeys xs).map Prod.fst → k ∈ xs.map Prod.fst := by
  intro xs k h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨p, dedupKeys_sub hp, rfl⟩

theorem dedupKeys_nodup {α β} [DecidableEq α] : ∀ (xs : List (α × β)),
    ((dedupKeys xs).map Prod.fst).Nodup
  | [] => by simp [dedupKeys]
  | q :: qs => by
    unfold dedupKeys
    split
    · exact dedupKeys_nodup qs
    next h =>
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => h ?_, dedupKeys_nodup qs⟩
      obtain ⟨p, hp, hpq⟩ := List.mem_map.mp (dedupKeys_keys_sub hm)
      exact List.any_eq_true.mpr ⟨p, hp, by simp [hpq]⟩

theorem dedupKeys_of_nodup {α β} [DecidableEq α] : ∀ {xs : List (α × β)},
    (xs.map Prod.fst).Nodup → dedupKeys xs = xs
  | [], _ => rfl
  | q :: qs, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    unfold dedupKeys
    have : (qs.any fun p => decide (p.1 = q.1)) = false := by
      rw [List.any_eq_false]
      intro p hp hpq
      exact h.1 (List.mem_map.mpr ⟨p, hp, of_decide_eq_true hpq⟩)
    rw [if_neg (by simp [this]), dedupKeys_of_nodup h.2]

/-! ## Sorting -/

section Sorting
variable {α : Type} [LT α] [StrictLT α] [DecidableLT α]

theorem eltsSorted_canonicalize (xs : List α) : EltsSorted (List.canonicalize id xs) :=
  eltsSorted_iff_sorted.mpr (List.canonicalize_sortedBy id xs)

theorem mem_canonicalize {xs : List α} {x : α} : x ∈ List.canonicalize id xs ↔ x ∈ xs :=
  ⟨fun h => List.canonicalize_subseteq id xs h, fun h => (List.canonicalize_equiv xs).1 h⟩

theorem canonicalize_of_eltsSorted {xs : List α} (h : EltsSorted xs) :
    List.canonicalize id xs = xs :=
  List.sortedBy_implies_canonicalize_eq (eltsSorted_iff_sorted.mp h)

theorem nodup_of_eltsSorted {xs : List α} (h : EltsSorted xs) : xs.Nodup := by
  have := sortedBy_map_nodup (f := id) (eltsSorted_iff_sorted.mp h)
  simpa using this

theorem canonicalize_ne_nil [DecidableEq α] {x : α} {xs : List α} :
    List.canonicalize id (x :: xs) ≠ [] :=
  (List.canonicalize_not_nil id (x :: xs)).mp (by simp)

end Sorting

section SortingKeys
variable {α β : Type} [LT α] [StrictLT α] [DecidableLT α]

theorem keysSorted_canonicalize (xs : List (α × β)) : KeysSorted (List.canonicalize Prod.fst xs) :=
  keysSorted_iff_sortedBy.mpr (List.canonicalize_sortedBy Prod.fst xs)

theorem canonicalize_fst_sub {xs : List (α × β)} {p : α × β} (h : p ∈ List.canonicalize Prod.fst xs) :
    p ∈ xs :=
  List.canonicalize_subseteq Prod.fst xs h

theorem canonicalize_fst_of_keysSorted {xs : List (α × β)} (h : KeysSorted xs) :
    List.canonicalize Prod.fst xs = xs :=
  List.sortedBy_implies_canonicalize_eq (keysSorted_iff_sortedBy.mp h)

theorem keys_nodup_of_keysSorted {xs : List (α × β)} (h : KeysSorted xs) :
    (xs.map Prod.fst).Nodup :=
  sortedBy_map_nodup (keysSorted_iff_sortedBy.mp h)

end SortingKeys

/-! ## The arrangements -/

theorem KeyArrET.nodup {m xs ys} (h : KeyArrET m xs ys) : ys.Nodup := by
  cases h with
  | sortT => exact nodup_of_eltsSorted (eltsSorted_canonicalize _)
  | sortF => exact nodup_of_eltsSorted (eltsSorted_canonicalize _)
  | dedupF => exact nodup_dedupKeep _

theorem KeyArrET.sorted {xs ys} (h : KeyArrET true xs ys) : EltsSorted ys := by
  cases h; exact eltsSorted_canonicalize _

theorem KeyArrET.sub {m xs ys} (h : KeyArrET m xs ys) : ∀ y ∈ ys, y ∈ xs := by
  cases h with
  | sortT => exact fun _ hy => mem_canonicalize.mp hy
  | sortF => exact fun _ hy => mem_canonicalize.mp hy
  | dedupF => exact fun _ hy => mem_dedupKeep.mp hy

theorem KeyArrUID.nodup {m xs ys} (h : KeyArrUID m xs ys) : ys.Nodup := by
  cases h with
  | sortT => exact nodup_of_eltsSorted (eltsSorted_canonicalize _)
  | sortF => exact nodup_of_eltsSorted (eltsSorted_canonicalize _)
  | dedupF => exact nodup_dedupKeep _

theorem KeyArrUID.sorted {xs ys} (h : KeyArrUID true xs ys) : EltsSorted ys := by
  cases h; exact eltsSorted_canonicalize _

theorem KeyArrUID.sub {m xs ys} (h : KeyArrUID m xs ys) : ∀ y ∈ ys, y ∈ xs := by
  cases h with
  | sortT => exact fun _ hy => mem_canonicalize.mp hy
  | sortF => exact fun _ hy => mem_canonicalize.mp hy
  | dedupF => exact fun _ hy => mem_dedupKeep.mp hy

theorem SetArrET.sub {m xs ys} (h : SetArrET m xs ys) : ∀ y ∈ ys, y ∈ xs := by
  cases h with
  | sortT => exact fun _ hy => mem_canonicalize.mp hy
  | sortF => exact fun _ hy => mem_canonicalize.mp hy
  | keepF => exact fun _ hy => hy

theorem SetArrET.sorted {xs ys} (h : SetArrET true xs ys) : EltsSorted ys := by
  cases h; exact eltsSorted_canonicalize _

theorem SetArrUID.sub {m xs ys} (h : SetArrUID m xs ys) : ∀ y ∈ ys, y ∈ xs := by
  cases h with
  | sortT => exact fun _ hy => mem_canonicalize.mp hy
  | sortF => exact fun _ hy => mem_canonicalize.mp hy
  | keepF => exact fun _ hy => hy

theorem SetArrUID.sorted {xs ys} (h : SetArrUID true xs ys) : EltsSorted ys := by
  cases h; exact eltsSorted_canonicalize _

theorem SetArrStr.sorted {xs ys} (h : SetArrStr true xs ys) : EltsSorted ys := by
  cases h; exact eltsSorted_canonicalize _

theorem SetArrET.ne_nil {m x xs ys} (h : SetArrET m (x :: xs) ys) : ys ≠ [] := by
  cases h with
  | sortT => exact canonicalize_ne_nil
  | sortF => exact canonicalize_ne_nil
  | keepF => simp

theorem SetArrStr.ne_nil {m x xs ys} (h : SetArrStr m (x :: xs) ys) : ys ≠ [] := by
  cases h with
  | sortT => exact canonicalize_ne_nil
  | sortF => exact canonicalize_ne_nil
  | keepF => simp

theorem insertCanonical_length_le {α β} [LT β] [DecidableLT β] (f : α → β) (x : α) :
    ∀ xs : List α, (List.insertCanonical f x xs).length ≤ xs.length + 1
  | [] => by simp [List.insertCanonical]
  | y :: ys => by
    unfold List.insertCanonical
    dsimp only
    split
    · simp
    · split
      · have := insertCanonical_length_le f x ys
        simp only [List.length_cons]; omega
      · simp

theorem canonicalize_length_le {α β} [LT β] [DecidableLT β] (f : α → β) :
    ∀ xs : List α, (List.canonicalize f xs).length ≤ xs.length
  | [] => by simp [List.canonicalize]
  | y :: ys => by
    simp only [List.canonicalize, List.length_cons]
    have := insertCanonical_length_le f y (List.canonicalize f ys)
    have := canonicalize_length_le f ys
    omega

theorem SetArrET.length_le {m xs ys} (h : SetArrET m xs ys) : ys.length ≤ xs.length := by
  cases h with
  | sortT => exact canonicalize_length_le _ _
  | sortF => exact canonicalize_length_le _ _
  | keepF => exact Nat.le_refl _

/-- Sorted lists are arranged as themselves, at either flag. -/
theorem setArrET_self {m} {xs : List EntityType} (h : EltsSorted xs) : SetArrET m xs xs := by
  cases m
  · have := SetArrET.sortF xs; rwa [canonicalize_of_eltsSorted h] at this
  · have := SetArrET.sortT xs; rwa [canonicalize_of_eltsSorted h] at this

theorem setArrUID_self {m} {xs : List EntityUID} (h : EltsSorted xs) : SetArrUID m xs xs := by
  cases m
  · have := SetArrUID.sortF xs; rwa [canonicalize_of_eltsSorted h] at this
  · have := SetArrUID.sortT xs; rwa [canonicalize_of_eltsSorted h] at this

theorem setArrStr_self {m} {xs : List String} (h : EltsSorted xs) : SetArrStr m xs xs := by
  cases m
  · have := SetArrStr.sortF xs; rwa [canonicalize_of_eltsSorted h] at this
  · have := SetArrStr.sortT xs; rwa [canonicalize_of_eltsSorted h] at this

theorem keyArrET_self {m} {xs : List EntityType} (h : EltsSorted xs) : KeyArrET m xs xs := by
  cases m
  · have := KeyArrET.sortF xs; rwa [canonicalize_of_eltsSorted h] at this
  · have := KeyArrET.sortT xs; rwa [canonicalize_of_eltsSorted h] at this

theorem keyArrUID_self {m} {xs : List EntityUID} (h : EltsSorted xs) : KeyArrUID m xs xs := by
  cases m
  · have := KeyArrUID.sortF xs; rwa [canonicalize_of_eltsSorted h] at this
  · have := KeyArrUID.sortT xs; rwa [canonicalize_of_eltsSorted h] at this

theorem AttrArr.sub {c m raw attrs} (h : AttrArr c m raw attrs) : ∀ p ∈ attrs, p ∈ raw := by
  cases h with
  | sortTT => exact fun _ hp => canonicalize_fst_sub hp
  | sortTF => exact fun _ hp => canonicalize_fst_sub hp
  | dedupTF => exact fun _ hp => dedupKeys_sub hp
  | sortFT => exact fun _ hp => canonicalize_fst_sub hp
  | rawFT => exact fun _ hp => hp
  | sortFF => exact fun _ hp => canonicalize_fst_sub hp
  | dedupFF => exact fun _ hp => dedupKeys_sub hp
  | rawFF => exact fun _ hp => hp

theorem AttrArr.nodup {m raw attrs} (h : AttrArr true m raw attrs) : (attrs.map Prod.fst).Nodup := by
  cases h with
  | sortTT => exact keys_nodup_of_keysSorted (keysSorted_canonicalize _)
  | sortTF => exact keys_nodup_of_keysSorted (keysSorted_canonicalize _)
  | dedupTF => exact dedupKeys_nodup _

theorem AttrArr.sorted {c raw attrs} (h : AttrArr c true raw attrs) (hc : c = true) :
    KeysSorted attrs := by
  subst hc
  cases h; exact keysSorted_canonicalize _

/-! ## Transitive closure -/

section Closure
variable {α β : Type} [DecidableEq α] [LT α] [DecidableLT α]
variable (get : β → List α) (set : β → List α → β)

theorem mem_addAnc {s : Bool} {acc : List α} {x y : α} :
    y ∈ addAnc s acc x → y ∈ acc ∨ y = x := by
  unfold addAnc
  split
  · exact .inl
  · split
    · intro h
      rcases List.mem_cons.mp (List.insertCanonical_subset id x acc h) with rfl | h
      · exact .inr rfl
      · exact .inl h
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact .inl h
      · exact .inr (List.mem_singleton.mp h)

theorem mem_foldl_addAnc {s : Bool} : ∀ {xs acc : List α} {y : α},
    y ∈ xs.foldl (addAnc s) acc → y ∈ acc ∨ y ∈ xs
  | [], _, _, h => .inl h
  | x :: xs, acc, y, h => by
    rcases mem_foldl_addAnc (xs := xs) h with h | h
    · rcases mem_addAnc h with h | rfl
      · exact .inl h
      · exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ h)

theorem foldl_addAnc_of_sub {s : Bool} : ∀ {xs acc : List α}, (∀ x ∈ xs, x ∈ acc) →
    xs.foldl (addAnc s) acc = acc
  | [], _, _ => rfl
  | x :: xs, acc, h => by
    simp only [List.foldl_cons]
    have : addAnc s acc x = acc := by unfold addAnc; rw [if_pos (h x List.mem_cons_self)]
    rw [this]
    exact foldl_addAnc_of_sub (fun y hy => h y (List.mem_cons_of_mem _ hy))

variable [StrictLT α] in
theorem sorted_foldl_addAnc : ∀ {xs acc : List α}, EltsSorted acc →
    EltsSorted (xs.foldl (addAnc true) acc)
  | [], _, h => h
  | x :: xs, acc, h => by
    simp only [List.foldl_cons]
    refine sorted_foldl_addAnc ?_
    unfold addAnc
    split
    · exact h
    · simp only [↓reduceIte]
      exact eltsSorted_iff_sorted.mpr (List.insertCanonical_sortedBy x (eltsSorted_iff_sorted.mp h))

theorem lookupAncs_mem {g : List (α × β)} {b x : α} (h : x ∈ lookupAncs get g b) :
    ∃ q ∈ g, q.1 = b ∧ x ∈ get q.2 := by
  unfold lookupAncs at h
  split at h
  next q hq =>
    have hb := List.find?_some hq
    simp only [decide_eq_true_eq] at hb
    exact ⟨q, List.mem_of_find?_eq_some hq, hb, h⟩
  · simp at h

theorem closeStep_map_fst (s : Bool) (g : List (α × β)) :
    (closeStep get set s g).map Prod.fst = g.map Prod.fst := by
  simp [closeStep]

theorem closeAll_map_fst (s : Bool) (g : List (α × β)) :
    (closeAll get set s g).map Prod.fst = g.map Prod.fst := by
  unfold closeAll
  generalize g.length = n
  induction n generalizing g with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, closeStep_map_fst]

/-- What the closure leaves alone: any projection blind to the ancestors. -/
theorem closeAll_map_proj {γ : Type} (f : β → γ) (hf : ∀ e l, f (set e l) = f e) (s : Bool)
    (g : List (α × β)) :
    (closeAll get set s g).map (fun p => (p.1, f p.2)) = g.map (fun p => (p.1, f p.2)) := by
  unfold closeAll
  generalize g.length = n
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [closeStep, hf]

/-- Every ancestor in the closure is an ancestor in the given hierarchy, if `set` stores no
more than it is given. -/
theorem closeAll_ancs_sub (hget : ∀ e l x, x ∈ get (set e l) → x ∈ l) (s : Bool) :
    ∀ (n : Nat) (g : List (α × β)), ∀ p ∈ Nat.iterate (closeStep get set s) n g,
      ∀ x ∈ get p.2, ∃ q ∈ g, x ∈ get q.2 := by
  intro n
  induction n with
  | zero => intro g p hp x hx; exact ⟨p, hp, hx⟩
  | succ n ih =>
    intro g p hp x hx
    rw [Function.iterate_succ_apply] at hp
    obtain ⟨q, hq, hxq⟩ := ih _ p hp x hx
    simp only [closeStep, List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have hx' := hget _ _ _ hxq
    rcases mem_foldl_addAnc hx' with h | h
    · exact ⟨r, hr, h⟩
    · obtain ⟨b, -, hb⟩ := List.mem_flatMap.mp h
      obtain ⟨q', hq', -, hx''⟩ := lookupAncs_mem get hb
      exact ⟨q', hq', hx''⟩

theorem closeAll_sub (hget : ∀ e l x, x ∈ get (set e l) → x ∈ l) (s : Bool) (g : List (α × β))
    {p : α × β} (hp : p ∈ closeAll get set s g) {x : α} (hx : x ∈ get p.2) :
    ∃ q ∈ g, x ∈ get q.2 :=
  closeAll_ancs_sub get set hget s g.length g p hp x hx

variable [StrictLT α] in
/-- Closing in order keeps every ancestor list sorted. -/
theorem closeAll_sorted (hget : ∀ e l, get (set e l) = l ∨ get (set e l) = [])
    (g : List (α × β)) (hg : ∀ q ∈ g, EltsSorted (get q.2)) :
    ∀ p ∈ closeAll get set true g, EltsSorted (get p.2) := by
  unfold closeAll
  generalize g.length = n
  induction n generalizing g with
  | zero => exact hg
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    refine ih _ ?_
    intro p hp
    simp only [closeStep, List.mem_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rcases hget r.2 (((get r.2).flatMap (lookupAncs get g)).foldl (addAnc true) (get r.2)) with
      h | h
    · rw [h]; exact sorted_foldl_addAnc (hg r hr)
    · rw [h]; exact .nil

/-- A closed hierarchy is its own closure. -/
theorem closeStep_of_closed (hset : ∀ e, set e (get e) = e) (s : Bool) (g : List (α × β))
    (h : closedB get g = true) : closeStep get set s g = g := by
  unfold closeStep
  conv => rhs; rw [← List.map_id g]
  refine List.map_congr_left fun p hp => ?_
  have hsub : ∀ x ∈ (get p.2).flatMap (lookupAncs get g), x ∈ get p.2 := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hx
    obtain ⟨q, hq, rfl, hxq⟩ := lookupAncs_mem get hxb
    simp only [closedB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, decide_eq_true_eq] at h
    rcases h p hp q hq with h | h
    · exact absurd hb h
    · exact h x hxq
  rw [foldl_addAnc_of_sub hsub, hset]
  rfl

theorem closeAll_of_closed (hset : ∀ e, set e (get e) = e) (s : Bool) (g : List (α × β))
    (h : closedB get g = true) : closeAll get set s g = g := by
  unfold closeAll
  generalize g.length = n
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, closeStep_of_closed get set hset s g h, ih]

theorem closedB_iff (g : List (α × β)) :
    closedB get g = true ↔ ∀ p ∈ g, ∀ q ∈ g, q.1 ∈ get p.2 → ∀ x ∈ get q.2, x ∈ get p.2 := by
  simp only [closedB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · intro h p hp q hq hqp x hx
    rcases h p hp q hq with h | h
    · exact absurd hqp h
    · exact h x hx
  · intro h p hp q hq
    by_cases hqp : q.1 ∈ get p.2
    · exact .inr (h p hp q hq hqp)
    · exact .inl hqp

theorem irreflB_iff (g : List (α × β)) : irreflB get g = true ↔ ∀ p ∈ g, p.1 ∉ get p.2 := by
  simp [irreflB]

end Closure

/-! ### The entity and action instances -/

theorem entWith_entAncs (e : EntitySchemaEntry) : entWith e (entAncs e) = e := by
  cases e with
  | standard se => obtain ⟨⟨l⟩, attrs, tags⟩ := se; rfl
  | enum eids => rfl

theorem entAncs_entWith (e : EntitySchemaEntry) (l : List EntityType) :
    entAncs (entWith e l) = l ∨ entAncs (entWith e l) = [] := by
  cases e with
  | standard se => exact .inl rfl
  | enum eids => exact .inr rfl

theorem entAncs_entWith_sub (e : EntitySchemaEntry) (l : List EntityType) (x : EntityType)
    (h : x ∈ entAncs (entWith e l)) : x ∈ l := by
  rcases entAncs_entWith e l with h' | h' <;> rw [h'] at h
  · exact h
  · cases h

/-- What an entity entry is apart from its ancestors. -/
def entShape : EntitySchemaEntry → EntitySchemaEntry
  | .standard e => .standard { e with ancestors := Set.mk [] }
  | .enum eids => .enum eids

theorem entShape_entWith (e : EntitySchemaEntry) (l : List EntityType) :
    entShape (entWith e l) = entShape e := by
  cases e <;> rfl

theorem actWith_actAncs (e : ActionSchemaEntry) : actWith e (actAncs e) = e := by
  obtain ⟨ps, rs, ⟨l⟩, ctx⟩ := e; rfl

theorem actAncs_actWith (e : ActionSchemaEntry) (l : List EntityUID) :
    actAncs (actWith e l) = l ∨ actAncs (actWith e l) = [] := .inl rfl

theorem actAncs_actWith_sub (e : ActionSchemaEntry) (l : List EntityUID) (x : EntityUID)
    (h : x ∈ actAncs (actWith e l)) : x ∈ l := h

/-- What an action entry is apart from its ancestors. -/
def actShape (e : ActionSchemaEntry) : ActionSchemaEntry := { e with ancestors := Set.mk [] }

theorem actShape_actWith (e : ActionSchemaEntry) (l : List EntityUID) :
    actShape (actWith e l) = actShape e := rfl

/-! ## Ranks -/

theorem mem_lowerOf {ranked : List (EntityUID × Nat)} {k : Nat} {u : EntityUID} :
    u ∈ lowerOf ranked k ↔ ∃ j, (u, j) ∈ ranked ∧ j < k := by
  simp only [lowerOf, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq]
  constructor
  · rintro ⟨⟨u', j⟩, hm, hj, rfl⟩
    exact ⟨j, hm, hj⟩
  · rintro ⟨j, hm, hj⟩
    exact ⟨(u, j), hm, hj, rfl⟩

end Cedar.Validation.Relational.SchemaGen
