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

import Cedar.Thm.PartialSchema
import Cedar.Thm.Validation.EnvironmentValidation
import Cedar.Validation.Linker

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

---- Helpers ---

-- Facts about `Map`, `Set` and `List` that `Cedar/Thm/Data` does not provide yet.

/-- `Map.find?` returns the value of the first entry with the key. -/
private theorem find?_eq_toList_find? {α β} [BEq α] (m : Map α β) (k : α) :
    m.find? k = (m.toList.find? (·.fst == k)).map Prod.snd := by
  cases hf : m.toList.find? (·.fst == k) <;> simp [Map.find?, hf]

/-- Rebuilding a map from its entries with key-dependent values. -/
private theorem make_toList_map_find? {α β γ} [DecidableEq α] [LT α] [DecidableLT α] [StrictLT α]
    (m : Map α β) (g : α → β → γ) (k : α) :
    (Map.make (m.toList.map fun kv => (kv.fst, g kv.fst kv.snd))).find? k =
      (m.find? k).map (g k) := by
  rw [Map.make_find?_eq_list_find?, List.find?_map, find?_eq_toList_find?]
  cases hf : m.toList.find? (·.fst == k) with
  | none => simp [hf, Function.comp_def]
  | some kv =>
    have hk : kv.fst = k := by simpa using List.find?_some hf
    simp [hf, hk, Function.comp_def]

/-- In key-preserving related lists, an entry found for a key has a related entry found for it. -/
private theorem forall₂_find?_some {α β} [DecidableEq α]
    {r : α × β → α × β → Prop} {xs ys : List (α × β)} {k : α} {x : α × β}
    (hkeys : ∀ x y, r x y → y.fst = x.fst)
    (hrel : List.Forall₂ r xs ys)
    (hfind : xs.find? (·.fst == k) = some x) :
    ∃ y, ys.find? (·.fst == k) = some y ∧ r x y := by
  induction hrel with
  | nil => simp at hfind
  | @cons x₀ y₀ _ _ hr _ ih =>
    simp only [List.find?] at hfind ⊢
    rw [hkeys _ _ hr]
    split at hfind
    · simp only [Option.some.injEq] at hfind
      subst x
      exact ⟨y₀, rfl, hr⟩
    · exact ih hfind

/-- In key-preserving related lists, a key absent from one list is absent from the other. -/
private theorem forall₂_find?_none {α β} [DecidableEq α]
    {r : α × β → α × β → Prop} {xs ys : List (α × β)} {k : α}
    (hkeys : ∀ x y, r x y → y.fst = x.fst)
    (hrel : List.Forall₂ r xs ys)
    (hfind : xs.find? (·.fst == k) = none) :
    ys.find? (·.fst == k) = none := by
  induction hrel with
  | nil => rfl
  | @cons x₀ y₀ _ _ hr _ ih =>
    simp only [List.find?] at hfind ⊢
    rw [hkeys _ _ hr]
    split at hfind
    · contradiction
    · exact ih hfind

/-- No element is in the empty set `∅`. -/
private theorem not_mem_emptyc {α} (y : α) : ¬y ∈ (∅ : Set α) :=
  Set.not_mem_empty y

/-- A fold of unions is well-formed if it starts from a well-formed set or adds a set. -/
private theorem foldl_union_wf {α β} [LT α] [DecidableLT α] [StrictLT α]
    (g : β → Set α) (l : List β) (init : Set α) (h : init.WellFormed ∨ l ≠ []) :
    (l.foldl (fun acc a => acc ∪ g a) init).WellFormed := by
  induction l generalizing init with
  | nil => simpa using h
  | cons a l ih => exact ih _ (.inl (Set.union_wf _ _))

-- Facts about paths along a relation. Walks bound the rounds of `closeAncestors`.

/-- A path starts with an edge. -/
private theorem transGen_head {α} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) : ∃ c, r a c := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

/-- A path ends with an edge. -/
private theorem transGen_tail {α} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) : ∃ c, r c b := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

/-- A path stays a path along a larger relation. -/
private theorem transGen_mono {α} {r s : α → α → Prop} (hrs : ∀ a b, r a b → s a b)
    {a b : α} (h : Relation.TransGen r a b) : Relation.TransGen s a b := by
  induction h with
  | single h => exact .single (hrs _ _ h)
  | tail _ h ih => exact .tail ih (hrs _ _ h)

/-- A path along `edge` from `x` to `y` whose edges leave from `srcs`, in order. -/
private inductive Walk {α} (edge : α → α → Prop) : α → α → List α → Prop
  | single {x y} : edge x y → Walk edge x y [x]
  | cons {x z y srcs} : edge x z → Walk edge z y srcs → Walk edge x y (x :: srcs)

private theorem Walk.append {α} {edge : α → α → Prop} {x y z : α} {s₁ s₂ : List α}
    (h₁ : Walk edge x y s₁) (h₂ : Walk edge y z s₂) : Walk edge x z (s₁ ++ s₂) := by
  induction h₁ with
  | single h => exact .cons h h₂
  | cons h _ ih => exact .cons h (ih h₂)

private theorem Walk.of_transGen {α} {edge : α → α → Prop} {x y : α}
    (h : Relation.TransGen edge x y) : ∃ srcs, Walk edge x y srcs := by
  induction h with
  | single h => exact ⟨_, .single h⟩
  | tail _ h ih =>
    obtain ⟨_, w⟩ := ih
    exact ⟨_, w.append (.single h)⟩

/-- Every vertex a walk leaves from has an edge. -/
private theorem Walk.source_edge {α} {edge : α → α → Prop} {x y : α} {srcs : List α}
    (h : Walk edge x y srcs) : ∀ v ∈ srcs, ∃ w, edge v w := by
  induction h with
  | single h => simpa using ⟨_, h⟩
  | cons h _ ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨_, h⟩
    · exact ih v hv

/-- A walk through `v` continues from `v` along a suffix of its sources. -/
private theorem Walk.suffix {α} {edge : α → α → Prop} {x y v : α} {srcs : List α}
    (h : Walk edge x y srcs) (hv : v ∈ srcs) :
    ∃ srcs', srcs' <:+ srcs ∧ Walk edge v y srcs' := by
  induction h with
  | single h =>
    obtain rfl := List.mem_singleton.mp hv
    exact ⟨_, List.suffix_refl _, .single h⟩
  | cons h w ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨_, List.suffix_refl _, .cons h w⟩
    · obtain ⟨srcs', hsfx, w'⟩ := ih hv
      exact ⟨srcs', hsfx.trans (List.suffix_cons _ _), w'⟩

/-- Every walk can be shortened to one that leaves from each vertex at most once. -/
private theorem Walk.nodup {α} {edge : α → α → Prop} {x y : α} {srcs : List α}
    (h : Walk edge x y srcs) :
    ∃ srcs', srcs'.Nodup ∧ srcs' ⊆ srcs ∧ Walk edge x y srcs' := by
  induction h with
  | @single x _ h => exact ⟨[x], by simp, List.Subset.refl _, .single h⟩
  | @cons x _ _ _ h _ ih =>
    obtain ⟨srcs', hnodup, hsub, w⟩ := ih
    by_cases hx : x ∈ srcs'
    · obtain ⟨srcs'', hsfx, w'⟩ := w.suffix hx
      exact ⟨srcs'', hnodup.sublist hsfx.sublist,
        fun _ hv => List.mem_cons_of_mem _ (hsub (hsfx.subset hv)), w'⟩
    · exact ⟨x :: srcs', List.nodup_cons.mpr ⟨hx, hnodup⟩, List.cons_subset_cons _ hsub,
        .cons h w⟩

-- Facts about well-formed types that `Cedar/Thm/Validation` does not provide yet.

/-- The empty record type is well-formed. -/
private theorem emptyRecord_wf {env : TypeEnv} :
    (CedarType.record Map.empty).WellFormed env :=
  .record_wf Map.wf_empty fun _ _ h => by simp at h

/-- The empty record type is lifted. -/
private theorem emptyRecord_lifted : (CedarType.record Map.empty).IsLifted :=
  .record_lifted fun _ _ h => by simp [Map.empty, Map.toList] at h

-- Facts about linking two entries.

/-- Linking two entity entries does not depend on their order. -/
private theorem entity_link_comm
    (ety : EntityType) (x y z : PartialEntitySchemaEntry)
    (h : x.link ety y = .ok z) :
    y.link ety x = .ok z := by
  cases x <;> cases y <;> simp only [PartialEntitySchemaEntry.link] at h ⊢
  case defined.defined => contradiction
  case external.external parents₁ parents₂ =>
    simp only [Except.ok.injEq] at h ⊢
    rw [← h, Set.union_comm]
  all_goals
    split at h <;> simp_all only [reduceCtorEq]

/-- Linking two action entries does not depend on their order. -/
private theorem action_link_comm
    (uid : EntityUID) (x y z : PartialActionSchemaEntry)
    (h : x.link uid y = .ok z) :
    y.link uid x = .ok z := by
  cases x <;> cases y <;> simp only [PartialActionSchemaEntry.link] at h ⊢
  case defined.defined => contradiction
  all_goals
    split at h <;> simp_all [beq_iff_eq]

/-- Linking an entity definition with another entry keeps the definition. -/
private theorem entity_link_defined
    {ety : EntityType} {entry : EntitySchemaEntry}
    {other result : PartialEntitySchemaEntry}
    (h : PartialEntitySchemaEntry.link ety (.defined entry) other = .ok result) :
    result = .defined entry := by
  cases other with
  | defined => simp [PartialEntitySchemaEntry.link] at h
  | external =>
    cases entry with
    | enum => simp [PartialEntitySchemaEntry.link] at h
    | standard =>
      simp only [PartialEntitySchemaEntry.link] at h
      split at h
      · exact (Except.ok.inj h).symm
      · contradiction

/-- Linking a standard or external entity entry gives a standard or external entry. -/
private theorem entity_link_isStandard
    {ety : EntityType} {x y z : PartialEntitySchemaEntry}
    (h : x.link ety y = .ok z)
    (hx : x.isStandard = true) :
    z.isStandard = true := by
  cases x with
  | defined entry => rw [entity_link_defined h]; exact hx
  | external =>
    cases y with
    | external =>
      simp only [PartialEntitySchemaEntry.link, Except.ok.injEq] at h
      subst z
      rfl
    | defined entry =>
      cases entry with
      | enum => simp [PartialEntitySchemaEntry.link] at h
      | standard =>
        simp only [PartialEntitySchemaEntry.link] at h
        split at h
        · cases Except.ok.inj h
          rfl
        · contradiction

/-- Linking an action definition with another entry keeps the definition. -/
private theorem action_link_defined
    {uid : EntityUID} {entry : ActionSchemaEntry}
    {other result : PartialActionSchemaEntry}
    (h : PartialActionSchemaEntry.link uid (.defined entry) other = .ok result) :
    result = .defined entry := by
  cases other with
  | defined => simp [PartialActionSchemaEntry.link] at h
  | external =>
    simp only [PartialActionSchemaEntry.link] at h
    split at h
    · exact (Except.ok.inj h).symm
    · contradiction

/-- Linking an action entry keeps its ancestors. -/
private theorem action_link_ancestors
    {uid : EntityUID} {x y z : PartialActionSchemaEntry}
    (h : x.link uid y = .ok z) :
    z.ancestors = x.ancestors := by
  cases x <;> cases y <;> simp only [PartialActionSchemaEntry.link] at h
  case defined.defined => contradiction
  all_goals
    split at h
    · cases Except.ok.inj h
      simp_all [PartialActionSchemaEntry.ancestors]
    · contradiction

/-- A definition obtained by linking is one of the linked entries. -/
private theorem entity_link_eq_defined
    {ety : EntityType} {x y : PartialEntitySchemaEntry} {entry : EntitySchemaEntry}
    (h : x.link ety y = .ok (.defined entry)) :
    x = .defined entry ∨ y = .defined entry := by
  cases x with
  | defined => exact .inl (entity_link_defined h).symm
  | external =>
    cases y with
    | external => simp [PartialEntitySchemaEntry.link] at h
    | defined => exact .inr (entity_link_defined (entity_link_comm _ _ _ _ h)).symm

/-- Linking two entity entries unions their ancestors. -/
private theorem entity_link_ancestors
    {ety a : EntityType} {x y z : PartialEntitySchemaEntry}
    (h : x.link ety y = .ok z) :
    a ∈ z.ancestors ↔ a ∈ x.ancestors ∨ a ∈ y.ancestors := by
  have hstd : ∀ {ancestors : Set EntityType} {std : StandardSchemaEntry},
      ancestors.subset std.ancestors = true → (a ∈ std.ancestors ↔ a ∈ ancestors ∨ a ∈ std.ancestors) :=
    fun hsub => ⟨.inr, fun h => h.elim (Set.subset_def.mp hsub a) id⟩
  cases x <;> cases y <;> simp only [PartialEntitySchemaEntry.link] at h
  case defined.defined => contradiction
  case external.external =>
    cases Except.ok.inj h
    simp [PartialEntitySchemaEntry.ancestors, Set.mem_union]
  case defined.external entry ancestors =>
    cases entry with
    | enum => simp at h
    | standard =>
      simp only at h
      split at h
      · cases Except.ok.inj h
        exact (hstd ‹_›).trans or_comm
      · contradiction
  case external.defined ancestors entry =>
    cases entry with
    | enum => simp at h
    | standard =>
      simp only at h
      split at h
      · cases Except.ok.inj h
        exact hstd ‹_›
      · contradiction

/-- Linking two action entries gives one of them. -/
private theorem action_link_eq
    {uid : EntityUID} {x y z : PartialActionSchemaEntry}
    (h : x.link uid y = .ok z) :
    z = x ∨ z = y := by
  cases x <;> cases y <;> simp only [PartialActionSchemaEntry.link] at h
  case defined.defined => contradiction
  all_goals
    split at h
    · cases Except.ok.inj h
      simp
    · contradiction

/-- `z` keeps the definition, the standard kind, and the ancestors of the entity entry `x`. -/
private structure EntryKept (x z : PartialEntitySchemaEntry) : Prop where
  definition : ∀ entry, x = .defined entry → z = .defined entry
  standard : x.isStandard = true → z.isStandard = true
  ancestors : x.ancestors ⊆ z.ancestors

/-- Two entity entries that are not both definitions link when one entry keeps both. -/
private theorem entity_link_exists {ety : EntityType} {x y z : PartialEntitySchemaEntry}
    (hdup : ∀ e₁ e₂, x = .defined e₁ → y = .defined e₂ → False)
    (hx : EntryKept x z) (hy : EntryKept y z) :
    ∃ v, x.link ety y = .ok v := by
  -- A definition linked with an external is the common entry, so it is standard.
  have hstd : ∀ {entry a}, EntryKept (.defined entry) z → EntryKept (.external a) z →
      ∃ std, entry = .standard std ∧ a.subset std.ancestors = true := by
    intro entry a hd he
    have hz := hd.definition entry rfl
    subst hz
    cases entry with
    | enum =>
      exact absurd (he.standard rfl)
        (by simp [PartialEntitySchemaEntry.isStandard, EntitySchemaEntry.isStandard])
    | standard std => exact ⟨std, rfl, he.ancestors⟩
  cases x with
  | defined e₁ =>
    cases y with
    | defined e₂ => exact (hdup e₁ e₂ rfl rfl).elim
    | external a₂ =>
      obtain ⟨std, rfl, hsub⟩ := hstd hx hy
      simp [PartialEntitySchemaEntry.link, hsub]
  | external a₁ =>
    cases y with
    | defined e₂ =>
      obtain ⟨std, rfl, hsub⟩ := hstd hy hx
      simp [PartialEntitySchemaEntry.link, hsub]
    | external a₂ => exact ⟨_, rfl⟩

/-- Two action entries with the same ancestors link when they are not both definitions. -/
private theorem action_link_exists {uid : EntityUID} {x y : PartialActionSchemaEntry}
    (hdup : ∀ e₁ e₂, x = .defined e₁ → y = .defined e₂ → False)
    (hancestors : x.ancestors = y.ancestors) :
    ∃ v, x.link uid y = .ok v := by
  cases x <;> cases y
  case defined.defined e₁ e₂ => exact (hdup e₁ e₂ rfl rfl).elim
  all_goals
    simp only [PartialActionSchemaEntry.ancestors] at hancestors
    simp [PartialActionSchemaEntry.link, hancestors]

-- Facts about `linkMaps`.

/-- The step `linkMaps` applies to each entry of its first map. -/
private def linkEntry {α β} [BEq α]
    (f : α → β → β → Except LinkError β) (m₂ : Map α β)
    (kv : α × β) : Except LinkError (α × β) :=
  match m₂.find? kv.fst with
  | some v₂ => do pure (kv.fst, ← f kv.fst kv.snd v₂)
  | none => pure kv

/-- `linkEntry` keeps the key of its entry. -/
private theorem linkEntry_key {α β} [BEq α]
    {f : α → β → β → Except LinkError β} {m₂ : Map α β}
    {kv kv' : α × β}
    (h : linkEntry f m₂ kv = .ok kv') :
    kv'.fst = kv.fst := by
  unfold linkEntry at h
  split at h
  · rename_i v₂ _
    cases hf : f kv.fst kv.snd v₂ <;> simp [hf] at h
    subst kv'
    rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst kv'
    rfl

/-- A successful `linkMaps` links the first map's entries, then appends the second map's other entries. -/
private theorem linkMaps_ok_eq {α β} [LT α] [DecidableLT α] [DecidableEq α]
    {f : α → β → β → Except LinkError β} {m₁ m₂ out : Map α β}
    (h : linkMaps f m₁ m₂ = .ok out) :
    ∃ linked,
      List.Forall₂ (fun x y => linkEntry f m₂ x = .ok y) m₁.toList linked ∧
      out = Map.make (linked ++ m₂.toList.filter fun kv => !m₁.contains kv.fst) := by
  unfold linkMaps at h
  change (do
    let linked ← m₁.toList.mapM (linkEntry f m₂)
    let rest := m₂.toList.filter fun (kv : α × β) => !m₁.contains kv.fst
    pure (Map.make (linked ++ rest))) = .ok out at h
  obtain ⟨linked, hmap, hout⟩ := do_eq_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at hout
  exact ⟨linked, List.mapM_ok_iff_forall₂.mp hmap, hout.symm⟩

/-- The entry `linkMaps` computes for a key from that key's entries in its two inputs. -/
private def linkAt {α β}
    (f : α → β → β → Except LinkError β) (k : α) :
    Option β → Option β → Except LinkError (Option β)
  | some v₁, some v₂ => some <$> f k v₁ v₂
  | some v₁, none => .ok (some v₁)
  | none, some v₂ => .ok (some v₂)
  | none, none => .ok none

/-- `linkMaps` computes each key's entry from that key's entries in its two inputs. -/
private theorem linkMaps_find? {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
    {f : α → β → β → Except LinkError β} {m₁ m₂ out : Map α β}
    (hlink : linkMaps f m₁ m₂ = .ok out) (k : α) :
    linkAt f k (m₁.find? k) (m₂.find? k) = .ok (out.find? k) := by
  obtain ⟨linked, hrel, rfl⟩ := linkMaps_ok_eq hlink
  rw [Map.make_find?_eq_list_find?, List.find?_append]
  cases h₁ : m₁.find? k with
  | some v₁ =>
    obtain ⟨⟨k', v⟩, hlinked, hstep⟩ :=
      forall₂_find?_some (fun _ _ => linkEntry_key) hrel (Map.map_find?_to_list_find? h₁)
    have hk : k' = k := by simpa using List.find?_some hlinked
    subst hk
    rw [hlinked]
    unfold linkEntry at hstep
    cases h₂ : m₂.find? k' with
    | none => simp_all [linkAt, pure, Except.pure]
    | some v₂ => cases hf : f k' v₁ v₂ <;> simp_all [linkAt]
  | none =>
    have hl₁ : m₁.toList.find? (·.fst == k) = none := by
      rwa [find?_eq_toList_find?, Option.map_eq_none_iff] at h₁
    rw [forall₂_find?_none (fun _ _ => linkEntry_key) hrel hl₁, Option.none_or]
    cases h₂ : m₂.find? k with
    | none =>
      have hl₂ : m₂.toList.find? (·.fst == k) = none := by
        rwa [find?_eq_toList_find?, Option.map_eq_none_iff] at h₂
      have hrest :
          (m₂.toList.filter fun kv => !m₁.contains kv.fst).find? (·.fst == k) = none := by
        rw [List.find?_eq_none] at hl₂ ⊢
        exact fun x hx => hl₂ x (List.mem_filter.mp hx).1
      rw [hrest]
      rfl
    | some v₂ =>
      rw [List.find?_filter_if_find? (fun k _ => !m₁.contains k)
        (Map.map_find?_to_list_find? h₂) (by simp [Map.contains, h₁])]
      rfl

/-- An entry of the first map keeps every property that linking it with the second map's entry keeps. -/
private theorem linkMaps_find?_left {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
    {f : α → β → β → Except LinkError β} {m₁ m₂ out : Map α β} {k : α} {v₁ : β}
    {P : β → Prop}
    (hlink : linkMaps f m₁ m₂ = .ok out)
    (hfind : m₁.find? k = some v₁)
    (hf : ∀ v₂ v, f k v₁ v₂ = .ok v → P v)
    (hP : P v₁) :
    ∃ v, out.find? k = some v ∧ P v := by
  have hspec := linkMaps_find? hlink k
  rw [hfind] at hspec
  cases h₂ : m₂.find? k with
  | none =>
    simp only [h₂, linkAt, Except.ok.injEq] at hspec
    exact ⟨v₁, hspec.symm, hP⟩
  | some v₂ =>
    simp only [h₂, linkAt] at hspec
    cases hv : f k v₁ v₂ <;> simp only [hv] at hspec
    · simp at hspec
    · simp only [Functor.map, Except.map, Except.ok.injEq] at hspec
      exact ⟨_, hspec.symm, hf v₂ _ hv⟩

/-- An entry of the second map keeps every property that linking the first map's entry with it keeps. -/
private theorem linkMaps_find?_right {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
    {f : α → β → β → Except LinkError β} {m₁ m₂ out : Map α β} {k : α} {v₂ : β}
    {P : β → Prop}
    (hlink : linkMaps f m₁ m₂ = .ok out)
    (hfind : m₂.find? k = some v₂)
    (hf : ∀ v₁ v, f k v₁ v₂ = .ok v → P v)
    (hP : P v₂) :
    ∃ v, out.find? k = some v ∧ P v := by
  have hspec := linkMaps_find? hlink k
  rw [hfind] at hspec
  cases h₁ : m₁.find? k with
  | none =>
    simp only [h₁, linkAt, Except.ok.injEq] at hspec
    exact ⟨v₂, hspec.symm, hP⟩
  | some v₁ =>
    simp only [h₁, linkAt] at hspec
    cases hv : f k v₁ v₂ <;> simp only [hv] at hspec
    · simp at hspec
    · simp only [Functor.map, Except.map, Except.ok.injEq] at hspec
      exact ⟨_, hspec.symm, hf v₁ _ hv⟩

/-- `linkMaps` declares exactly the keys of its inputs. -/
private theorem linkMaps_contains {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
    {f : α → β → β → Except LinkError β} {m₁ m₂ out : Map α β}
    (hlink : linkMaps f m₁ m₂ = .ok out) (k : α) :
    out.contains k ↔ m₁.contains k ∨ m₂.contains k := by
  have hspec := linkMaps_find? hlink k
  simp only [Map.contains]
  cases h₁ : m₁.find? k <;> cases h₂ : m₂.find? k <;>
    simp only [h₁, h₂, linkAt, Except.ok.injEq] at hspec
  case some.some v₁ v₂ =>
    cases hv : f k v₁ v₂ <;> simp [hv, Functor.map, Except.map] at hspec
    simp [← hspec]
  all_goals simp [← hspec]

/-- A successful `linkMaps` produces a well-formed map. -/
private theorem linkMaps_wf {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
    {f : α → β → β → Except LinkError β} {m₁ m₂ out : Map α β}
    (hlink : linkMaps f m₁ m₂ = .ok out) :
    out.WellFormed := by
  obtain ⟨_, _, rfl⟩ := linkMaps_ok_eq hlink
  exact Map.make_wf _

/-- `linkMaps` succeeds when linking succeeds at every key of a well-formed first map. -/
private theorem linkMaps_exists {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
    {f : α → β → β → Except LinkError β} {m₁ m₂ : Map α β}
    (hw₁ : m₁.WellFormed)
    (h : ∀ k v₁ v₂, m₁.find? k = some v₁ → m₂.find? k = some v₂ →
      ∃ v, f k v₁ v₂ = .ok v) :
    ∃ out, linkMaps f m₁ m₂ = .ok out := by
  have hall : ∀ kv ∈ m₁.toList, ∃ out, linkEntry f m₂ kv = .ok out := by
    intro ⟨k, v₁⟩ hmem
    cases h₂ : m₂.find? k with
    | none => exact ⟨(k, v₁), by simp only [linkEntry, h₂]; rfl⟩
    | some v₂ =>
      obtain ⟨v, hv⟩ := h k v₁ v₂ ((Map.in_list_iff_find?_some hw₁).mp hmem) h₂
      exact ⟨(k, v), by simp [linkEntry, h₂, hv]⟩
  obtain ⟨linked, hlinked⟩ := List.all_ok_implies_mapM_ok hall
  refine ⟨Map.make (linked ++ m₂.toList.filter fun kv => !m₁.contains kv.fst), ?_⟩
  unfold linkMaps
  change (do
    let linked ← m₁.toList.mapM (linkEntry f m₂)
    let rest := m₂.toList.filter fun (kv : α × β) => !m₁.contains kv.fst
    pure (Map.make (linked ++ rest))) = _
  simp [hlinked]

/-- `linkMaps` is commutative when linking entries is, given a well-formed second map. -/
private theorem linkMaps_comm {α β} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
    {f : α → β → β → Except LinkError β} {m₁ m₂ out : Map α β}
    (hw₂ : m₂.WellFormed)
    (hcomm : ∀ k v₁ v₂ v, f k v₁ v₂ = .ok v → f k v₂ v₁ = .ok v)
    (hlink : linkMaps f m₁ m₂ = .ok out) :
    linkMaps f m₂ m₁ = .ok out := by
  have hspec := linkMaps_find? hlink
  obtain ⟨out', hlink'⟩ := linkMaps_exists hw₂ fun k v₂ v₁ h₂ h₁ => by
    have hs := hspec k
    rw [h₁, h₂] at hs
    cases hv : f k v₁ v₂ with
    | error => simp [linkAt, hv] at hs
    | ok v => exact ⟨v, hcomm k v₁ v₂ v hv⟩
  suffices hout : out' = out by rw [← hout]; exact hlink'
  apply Map.find?_ext (linkMaps_wf hlink') (linkMaps_wf hlink)
  intro k
  have hs := hspec k
  have hs' := linkMaps_find? hlink' k
  cases h₁ : m₁.find? k <;> cases h₂ : m₂.find? k <;>
    simp only [h₁, h₂, linkAt] at hs hs'
  case some.some v₁ v₂ =>
    cases hv : f k v₁ v₂ with
    | error => simp [hv] at hs
    | ok v =>
      simp [hv, hcomm k v₁ v₂ v hv] at hs hs'
      rw [← hs, ← hs']
  all_goals
    simp only [Except.ok.injEq] at hs hs'
    rw [← hs, ← hs']

/-- A key that `linkMaps` keeps comes from the first map, the second map, or linking both entries. -/
private theorem linkAt_some {α β} {f : α → β → β → Except LinkError β} {k : α}
    {v₁ v₂ : Option β} {v : β}
    (h : linkAt f k v₁ v₂ = .ok (some v)) :
    (v₁ = some v ∧ v₂ = none) ∨ (v₁ = none ∧ v₂ = some v) ∨
      ∃ a b, v₁ = some a ∧ v₂ = some b ∧ f k a b = .ok v := by
  cases v₁ <;> cases v₂ <;> simp only [linkAt, Except.ok.injEq, Option.some.injEq] at h
  case none.none => contradiction
  case some.none => exact .inl ⟨by rw [h], rfl⟩
  case none.some => exact .inr (.inl ⟨rfl, by rw [h]⟩)
  case some.some a b =>
    cases hv : f k a b <;> simp [hv, Functor.map, Except.map] at h
    exact .inr (.inr ⟨a, b, rfl, rfl, by rw [hv, h]⟩)

/-- A key that `linkMaps` drops is in neither map. -/
private theorem linkAt_none {α β} {f : α → β → β → Except LinkError β} {k : α}
    {v₁ v₂ : Option β}
    (h : linkAt f k v₁ v₂ = .ok none) :
    v₁ = none ∧ v₂ = none := by
  cases v₁ <;> cases v₂ <;> simp only [linkAt, Except.ok.injEq, reduceCtorEq] at h
  case none.none => exact ⟨rfl, rfl⟩
  case some.some a b => cases hv : f k a b <;> simp [hv, Functor.map, Except.map] at h

/-- In linked entity maps, each entity type's ancestors are its ancestors in either input. -/
private theorem linkMaps_entity_ancestors {ets₁ ets₂ out : PartialEntitySchema}
    (hlink : linkMaps PartialEntitySchemaEntry.link ets₁ ets₂ = .ok out) (x y : EntityType) :
    (∃ e, out.find? x = some e ∧ y ∈ e.ancestors) ↔
      (∃ e, ets₁.find? x = some e ∧ y ∈ e.ancestors) ∨
      (∃ e, ets₂.find? x = some e ∧ y ∈ e.ancestors) := by
  have hspec := linkMaps_find? hlink x
  cases hout : out.find? x with
  | none =>
    obtain ⟨h₁, h₂⟩ := linkAt_none (hout ▸ hspec)
    simp [h₁, h₂]
  | some e =>
    rcases linkAt_some (hout ▸ hspec) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, hv⟩
    · simp [h₁, h₂]
    · simp [h₁, h₂]
    · simp [h₁, h₂, entity_link_ancestors hv]

/-- A definition in linked entity maps is a definition in either input. -/
private theorem linkMaps_entity_defined {ets₁ ets₂ out : PartialEntitySchema}
    {ety : EntityType} {entry : EntitySchemaEntry}
    (hlink : linkMaps PartialEntitySchemaEntry.link ets₁ ets₂ = .ok out)
    (hfind : out.find? ety = some (.defined entry)) :
    ets₁.find? ety = some (.defined entry) ∨ ets₂.find? ety = some (.defined entry) := by
  rcases linkAt_some (hfind ▸ linkMaps_find? hlink ety) with
    ⟨h₁, -⟩ | ⟨-, h₂⟩ | ⟨x, y, h₁, h₂, hlinked⟩
  · exact .inl h₁
  · exact .inr h₂
  · rcases entity_link_eq_defined hlinked with rfl | rfl
    · exact .inl h₁
    · exact .inr h₂

-- Facts about `closeAncestors`.

/-- `y` is listed as an ancestor of `x` in `m`. -/
private def AncestorEdge (m : Map EntityType (Set EntityType)) (x y : EntityType) : Prop :=
  y ∈ (m.find? x).getD ∅

/-- One round of `closeAncestors`, which adds the ancestors of every listed ancestor. -/
private def closeRound (m : Map EntityType (Set EntityType)) : Map EntityType (Set EntityType) :=
  m.mapOnValues λ s => Set.foldl (λ acc a => acc ∪ (m.find? a).getD ∅) s s

/-- The loop of `closeAncestors`, whose own name is not accessible here. -/
private def closeIter : Nat → Map EntityType (Set EntityType) → Map EntityType (Set EntityType)
  | 0, m => m
  | n + 1, m => closeIter n (closeRound m)

private theorem closeAncestors_eq_closeIter (m : Map EntityType (Set EntityType)) :
    closeAncestors m = closeIter m.size m := by
  unfold closeAncestors
  generalize m.size = n
  induction n generalizing m with
  | zero => rfl
  | succ n ih => exact ih _

private theorem ancestorEdge_closeRound {m : Map EntityType (Set EntityType)} {x y : EntityType} :
    AncestorEdge (closeRound m) x y ↔
      AncestorEdge m x y ∨ ∃ a, AncestorEdge m x a ∧ AncestorEdge m a y := by
  simp only [AncestorEdge, closeRound, Map.find?_mapOnValues]
  cases m.find? x with
  | none => simp [not_mem_emptyc]
  | some s =>
    simp only [Option.map_some, Option.getD_some, Set.foldl,
      List.mem_foldl_union_iff_mem_or_exists, Set.mem_elts_iff_mem_set]

/-- One round halves the length of every walk. -/
private theorem Walk.closeRound {m : Map EntityType (Set EntityType)} {x y : EntityType}
    {srcs : List EntityType}
    (h : Walk (AncestorEdge m) x y srcs) :
    (∃ srcs', Walk (AncestorEdge (closeRound m)) x y srcs' ∧
      2 * srcs'.length ≤ srcs.length + 1) ∧
    (∀ w, AncestorEdge m w x → ∃ srcs', Walk (AncestorEdge (closeRound m)) w y srcs' ∧
      2 * srcs'.length ≤ srcs.length + 2) := by
  induction h with
  | @single x y hxy =>
    exact ⟨⟨[x], .single (ancestorEdge_closeRound.mpr (.inl hxy)), by simp⟩,
      fun w hwx => ⟨[w], .single (ancestorEdge_closeRound.mpr (.inr ⟨x, hwx, hxy⟩)), by simp⟩⟩
  | @cons x z y srcs hxz _ ih =>
    refine ⟨?_, fun w hwx => ?_⟩
    · obtain ⟨srcs', w', hlen⟩ := ih.2 x hxz
      exact ⟨srcs', w', by simp only [List.length_cons]; omega⟩
    · obtain ⟨srcs', w', hlen⟩ := ih.1
      exact ⟨w :: srcs', .cons (ancestorEdge_closeRound.mpr (.inr ⟨x, hwx, hxz⟩)) w',
        by simp only [List.length_cons]; omega⟩

/-- `n` rounds turn every walk of length at most `2 ^ n` into an edge. -/
private theorem Walk.closeIter {n : Nat} {m : Map EntityType (Set EntityType)}
    {x y : EntityType} {srcs : List EntityType}
    (h : Walk (AncestorEdge m) x y srcs) (hlen : srcs.length ≤ 2 ^ n) :
    AncestorEdge (closeIter n m) x y := by
  induction n generalizing m srcs with
  | zero =>
    cases h with
    | single h => exact h
    | cons _ w => cases w <;> simp at hlen
  | succ n ih =>
    obtain ⟨srcs', w', hlen'⟩ := h.closeRound.1
    exact ih w' (by rw [Nat.pow_succ] at hlen; omega)

/-- Every edge added by a round is a path in the original map. -/
private theorem closeRound_sound {m : Map EntityType (Set EntityType)} {x y : EntityType}
    (h : Relation.TransGen (AncestorEdge (closeRound m)) x y) :
    Relation.TransGen (AncestorEdge m) x y := by
  have hedge : ∀ {a b}, AncestorEdge (closeRound m) a b →
      Relation.TransGen (AncestorEdge m) a b :=
    fun h => (ancestorEdge_closeRound.mp h).elim .single fun ⟨_, h₁, h₂⟩ => .tail (.single h₁) h₂
  induction h with
  | single h => exact hedge h
  | tail _ h ih => exact ih.trans (hedge h)

private theorem closeIter_sound {n : Nat} {m : Map EntityType (Set EntityType)}
    {x y : EntityType} (h : AncestorEdge (closeIter n m) x y) :
    Relation.TransGen (AncestorEdge m) x y := by
  induction n generalizing m with
  | zero => exact .single h
  | succ n ih => exact closeRound_sound (ih h)

/-- A vertex with an edge is a key. -/
private theorem AncestorEdge.key {m : Map EntityType (Set EntityType)} {x y : EntityType}
    (h : AncestorEdge m x y) : x ∈ m.toList.map Prod.fst := by
  unfold AncestorEdge at h
  cases hx : m.find? x with
  | none => simp [hx, not_mem_emptyc] at h
  | some s => exact List.mem_map.mpr ⟨(x, s), Map.find?_mem_toList hx, rfl⟩

/-- `closeAncestors` lists exactly the ancestors reachable in its input. -/
private theorem ancestorEdge_closeAncestors {m : Map EntityType (Set EntityType)}
    {x y : EntityType} :
    AncestorEdge (closeAncestors m) x y ↔ Relation.TransGen (AncestorEdge m) x y := by
  rw [closeAncestors_eq_closeIter]
  refine ⟨closeIter_sound, fun h => ?_⟩
  obtain ⟨_, w⟩ := Walk.of_transGen h
  obtain ⟨srcs, hnodup, -, w⟩ := w.nodup
  apply w.closeIter
  have hkeys : srcs ⊆ m.toList.map Prod.fst := fun v hv =>
    let ⟨_, hv⟩ := w.source_edge v hv
    hv.key
  have hlen := (List.subperm_of_subset hnodup hkeys).length_le
  simp only [List.length_map] at hlen
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hlen Nat.lt_two_pow_self)

/-- Every set computed by a round is well-formed. -/
private theorem closeRound_wf (m : Map EntityType (Set EntityType)) (x : EntityType) :
    (((closeRound m).find? x).getD ∅).WellFormed := by
  simp only [closeRound, Map.find?_mapOnValues]
  cases m.find? x with
  | none => exact Set.empty_wf
  | some s =>
    cases s with
    | mk elts =>
      cases elts with
      | nil => exact Set.empty_wf
      | cons a l => exact foldl_union_wf _ _ _ (.inr (List.cons_ne_nil _ _))

private theorem closeIter_succ_wf (n : Nat) (m : Map EntityType (Set EntityType))
    (x : EntityType) :
    (((closeIter (n + 1) m).find? x).getD ∅).WellFormed := by
  induction n generalizing m with
  | zero => exact closeRound_wf m x
  | succ n ih => exact ih (closeRound m)

/-- Every set computed by `closeAncestors` is well-formed. -/
private theorem closeAncestors_wf (m : Map EntityType (Set EntityType)) (x : EntityType) :
    (((closeAncestors m).find? x).getD ∅).WellFormed := by
  rw [closeAncestors_eq_closeIter]
  cases hsize : m.size with
  | zero =>
    have hnil : m.toList = [] := List.eq_nil_of_length_eq_zero hsize
    simp only [closeIter, Map.find?, hnil, List.find?_nil, Option.getD_none]
    exact Set.empty_wf
  | succ n => exact closeIter_succ_wf n m x

-- Facts about `closeForLink`.

/-- The closed ancestors that `closeForLink` assigns to an entity type. -/
private def closedAncestors (ets : PartialEntitySchema) (ety : EntityType) : Set EntityType :=
  ((closeAncestors (ets.mapOnValues (·.ancestors))).find? ety).getD Set.empty

/-- A successful closure keeps every definition's ancestors and replaces every entry's ancestors with the closed ones. -/
private theorem closeForLink_ok {ets out : PartialEntitySchema}
    (h : ets.closeForLink = .ok out) :
    (∀ ety std, (ety, .defined (.standard std)) ∈ ets.toList →
      closedAncestors ets ety = std.ancestors) ∧
    out = Map.make (ets.toList.map fun kv =>
      (kv.fst, kv.snd.withAncestors (closedAncestors ets kv.fst))) := by
  unfold PartialEntitySchema.closeForLink at h
  obtain ⟨_, hcheck, hout⟩ := do_eq_ok.mp h
  constructor
  · intro ety std hmem
    have hstep := List.forM_ok_implies_all_ok' hcheck _ hmem
    simp only at hstep
    split at hstep
    · exact beq_iff_eq.mp ‹_›
    · contradiction
  · simp only [pure, Except.pure, Except.ok.injEq] at hout
    exact hout.symm

/-- `closeForLink` replaces each entry's ancestors with its closed ancestors. -/
private theorem closeForLink_find? {ets out : PartialEntitySchema}
    (h : ets.closeForLink = .ok out) (ety : EntityType) :
    out.find? ety = (ets.find? ety).map (·.withAncestors (closedAncestors ets ety)) := by
  rw [(closeForLink_ok h).2,
    make_toList_map_find? ets fun ety entry => entry.withAncestors (closedAncestors ets ety)]

/-- A successful closure keeps every definition unchanged. -/
private theorem closeForLink_find?_defined
    {ets out : PartialEntitySchema} {ety : EntityType} {entry : EntitySchemaEntry}
    (hclose : ets.closeForLink = .ok out)
    (hfind : ets.find? ety = some (.defined entry)) :
    out.find? ety = some (.defined entry) := by
  rw [closeForLink_find? hclose, hfind, Option.map_some]
  cases entry with
  | enum => rfl
  | standard std =>
    rw [(closeForLink_ok hclose).1 ety std (Map.find?_mem_toList hfind)]
    rfl

/-- Replacing ancestors keeps an entry standard or external. -/
private theorem withAncestors_isStandard
    (entry : PartialEntitySchemaEntry) (ancestors : Set EntityType) :
    (entry.withAncestors ancestors).isStandard = entry.isStandard := by
  cases entry with
  | defined entry => cases entry <;> rfl
  | external => rfl

/-- An entity type's closed ancestors are the entity types reachable through listed ancestors. -/
private theorem mem_closedAncestors {ets : PartialEntitySchema} {x y : EntityType} :
    y ∈ closedAncestors ets x ↔
      Relation.TransGen (fun a b => ∃ e, ets.find? a = some e ∧ b ∈ e.ancestors) x y := by
  have hedge : AncestorEdge (ets.mapOnValues (·.ancestors)) =
      fun a b => ∃ e, ets.find? a = some e ∧ b ∈ e.ancestors := by
    funext a b
    simp only [AncestorEdge, Map.find?_mapOnValues, eq_iff_iff]
    cases ets.find? a <;> simp [not_mem_emptyc]
  rw [← hedge]
  exact ancestorEdge_closeAncestors

/-- Closed ancestors are well-formed. -/
private theorem closedAncestors_wf (ets : PartialEntitySchema) (x : EntityType) :
    (closedAncestors ets x).WellFormed :=
  closeAncestors_wf _ x

/-- Closed ancestors of linked entity maps are reachable through either input's ancestors. -/
private theorem mem_closedAncestors_linkMaps {ets₁ ets₂ out : PartialEntitySchema}
    {x y : EntityType}
    (hlink : linkMaps PartialEntitySchemaEntry.link ets₁ ets₂ = .ok out) :
    y ∈ closedAncestors out x ↔
      Relation.TransGen (fun a b =>
        (∃ e, ets₁.find? a = some e ∧ b ∈ e.ancestors) ∨
        (∃ e, ets₂.find? a = some e ∧ b ∈ e.ancestors)) x y := by
  have hedges : (fun a b => ∃ e, out.find? a = some e ∧ b ∈ e.ancestors) =
      (fun a b => (∃ e, ets₁.find? a = some e ∧ b ∈ e.ancestors) ∨
        (∃ e, ets₂.find? a = some e ∧ b ∈ e.ancestors)) := by
    funext a b
    exact propext (linkMaps_entity_ancestors hlink a b)
  rw [mem_closedAncestors, hedges]

/-- `closeForLink` succeeds when closing keeps every definition's ancestors. -/
private theorem closeForLink_exists {ets : PartialEntitySchema}
    (h : ∀ ety std, (ety, .defined (.standard std)) ∈ ets.toList →
      closedAncestors ets ety = std.ancestors) :
    ∃ out, ets.closeForLink = .ok out := by
  unfold PartialEntitySchema.closeForLink
  refine ⟨_, do_eq_ok.mpr ⟨(), List.all_ok_implies_forM_ok _ _
    fun ⟨ety, entry⟩ hmem => ?_, rfl⟩⟩
  cases entry with
  | external => rfl
  | defined entry =>
    cases entry with
    | enum => rfl
    | standard std =>
      have hclosed := h ety std hmem
      unfold closedAncestors at hclosed
      simp [hclosed]

-- Facts about `link`.

/-- The first check of `link`: no action's entity type is an entity type of either input. -/
private def collisionCheck (p c : PartialSchema) : Except LinkError Unit :=
  (p.acts.toList ++ c.acts.toList).forM λ (uid, _) =>
    if p.ets.contains uid.ty || c.ets.contains uid.ty then
      .error (.actionEntityTypeDeclared uid.ty)
    else
      .ok ()

/-- `link` checks collisions, links both maps, then closes the linked entity map. -/
private theorem link_eq (p c : PartialSchema) :
    link p c = (do
      collisionCheck p c
      let ets ← linkMaps PartialEntitySchemaEntry.link p.ets c.ets
      let acts ← linkMaps PartialActionSchemaEntry.link p.acts c.acts
      let ets ← PartialEntitySchema.closeForLink ets
      pure { ets, acts }) := rfl

/-- The results of the steps of a successful link. -/
private theorem link_ok {p c t : PartialSchema} (h : link p c = .ok t) :
    collisionCheck p c = .ok () ∧
    ∃ ets,
      linkMaps PartialEntitySchemaEntry.link p.ets c.ets = .ok ets ∧
      linkMaps PartialActionSchemaEntry.link p.acts c.acts = .ok t.acts ∧
      PartialEntitySchema.closeForLink ets = .ok t.ets := by
  rw [link_eq] at h
  obtain ⟨_, hcollision, h⟩ := do_eq_ok.mp h
  obtain ⟨ets, hets, h⟩ := do_eq_ok.mp h
  obtain ⟨acts, hacts, h⟩ := do_eq_ok.mp h
  obtain ⟨_, hclose, rfl⟩ := do_ok_eq_ok.mp h
  exact ⟨hcollision, ets, hets, hacts, hclose⟩

/-- After a successful collision check, no action of either input has an entity type of either input. -/
private theorem collisionCheck_ok {p c : PartialSchema} {uid : EntityUID}
    (h : collisionCheck p c = .ok ())
    (haction : p.acts.contains uid ∨ c.acts.contains uid) :
    ¬p.ets.contains uid.ty ∧ ¬c.ets.contains uid.ty := by
  obtain ⟨entry, hmem⟩ : ∃ entry, (uid, entry) ∈ p.acts.toList ++ c.acts.toList := by
    rcases haction with haction | haction <;>
      obtain ⟨entry, hfind⟩ := Map.contains_iff_some_find?.mp haction <;>
      exact ⟨entry, by simp [Map.find?_mem_toList hfind]⟩
  have hstep := List.forM_ok_implies_all_ok' h _ hmem
  simp only at hstep
  split at hstep
  · contradiction
  · rename_i hnot
    simpa using hnot

/-- The collision check does not depend on the input order. -/
private theorem collisionCheck_comm {p c : PartialSchema}
    (h : collisionCheck p c = .ok ()) :
    collisionCheck c p = .ok () := by
  apply List.all_ok_implies_forM_ok
  intro x hx
  have hstep := List.forM_ok_implies_all_ok' h x
    (by simpa only [List.mem_append, or_comm] using hx)
  simpa only [Bool.or_comm] using hstep

/-- The collision check passes when no action of either input has an entity type of either input. -/
private theorem collisionCheck_of_disjoint {p c : PartialSchema}
    (h : ∀ uid, p.acts.contains uid ∨ c.acts.contains uid →
      ¬p.ets.contains uid.ty ∧ ¬c.ets.contains uid.ty) :
    collisionCheck p c = .ok () := by
  apply List.all_ok_implies_forM_ok
  intro ⟨uid, _⟩ hmem
  have ⟨hp, hc⟩ := h uid ((List.mem_append.mp hmem).imp
    Map.in_list_implies_contains Map.in_list_implies_contains)
  simp [hp, hc]

/-- `link` succeeds when each of its steps does. -/
private theorem link_of_steps {p c : PartialSchema} {ets ets' : PartialEntitySchema}
    {acts : PartialActionSchema}
    (hcollision : collisionCheck p c = .ok ())
    (hets : linkMaps PartialEntitySchemaEntry.link p.ets c.ets = .ok ets)
    (hacts : linkMaps PartialActionSchemaEntry.link p.acts c.acts = .ok acts)
    (hclose : ets.closeForLink = .ok ets') :
    link p c = .ok { ets := ets', acts } := by
  simp [link_eq, hcollision, hets, hacts, hclose, pure, Except.pure]

/-- A link has a well-formed entity map. -/
private theorem link_ets_wf {p c t : PartialSchema} (hlink : link p c = .ok t) :
    t.ets.WellFormed := by
  obtain ⟨-, _, -, -, hclose⟩ := link_ok hlink
  rw [(closeForLink_ok hclose).2]
  exact Map.make_wf _

/-- A link has a well-formed action map. -/
private theorem link_acts_wf {p c t : PartialSchema} (hlink : link p c = .ok t) :
    t.acts.WellFormed := by
  obtain ⟨-, -, -, hacts, -⟩ := link_ok hlink
  exact linkMaps_wf hacts

/-- The ancestors of an unresolved external entity type in a link are well-formed. -/
private theorem link_external_ancestors_wf {p c t : PartialSchema} {ety : EntityType}
    {ancestors : Set EntityType} (hlink : link p c = .ok t)
    (hfind : t.ets.find? ety = some (.external ancestors)) :
    ancestors.WellFormed := by
  obtain ⟨-, ets, -, -, hclose⟩ := link_ok hlink
  rw [closeForLink_find? hclose, Option.map_eq_some_iff] at hfind
  obtain ⟨entry, -, hentry⟩ := hfind
  cases entry with
  | defined entry => cases entry <;> simp [PartialEntitySchemaEntry.withAncestors] at hentry
  | external =>
    simp only [PartialEntitySchemaEntry.withAncestors,
      PartialEntitySchemaEntry.external.injEq] at hentry
    rw [← hentry]
    exact closedAncestors_wf ets ety

-- Facts about well-formed partial schemas.

/-- A well-formed partial schema has a well-formed entity map. -/
private theorem PartialSchema.WellFormed.etsMap
    {schema : PartialSchema} (h : schema.WellFormed) :
    schema.ets.WellFormed := by
  simp only [PartialSchema.WellFormed, PartialSchema.validationView] at h
  exact Map.mapOnValues_wf.mpr h.2.1.1

/-- A well-formed partial schema has a well-formed action map. -/
private theorem PartialSchema.WellFormed.actsMap
    {schema : PartialSchema} (h : schema.WellFormed) :
    schema.acts.WellFormed := by
  simp only [PartialSchema.WellFormed, PartialSchema.validationView] at h
  exact Map.mapOnValues_wf.mpr h.2.2.1

/-- The environment in which `PartialSchema.WellFormed` checks a partial schema. -/
private def PartialSchema.wfEnv (schema : PartialSchema) : TypeEnv :=
  { ets := schema.validationView.ets, acts := schema.validationView.acts, reqty := default }

private theorem PartialSchema.wellFormed_iff {schema : PartialSchema} :
    schema.WellFormed ↔ schema.ets.AncestorsClosed ∧
      schema.wfEnv.ets.WellFormed schema.wfEnv ∧ schema.wfEnv.acts.WellFormed schema.wfEnv :=
  Iff.rfl

private theorem PartialSchema.wfEnv_ets_find? {schema : PartialSchema} {ety : EntityType}
    {entry : EntitySchemaEntry} (h : schema.wfEnv.ets.find? ety = some entry) :
    ∃ entry', schema.ets.find? ety = some entry' ∧ entry'.validationView = entry :=
  Option.map_eq_some_iff.mp ((validationView_find?_ets schema ety).symm.trans h)

private theorem PartialSchema.wfEnv_acts_find? {schema : PartialSchema} {uid : EntityUID}
    {entry : ActionSchemaEntry} (h : schema.wfEnv.acts.find? uid = some entry) :
    ∃ entry', schema.acts.find? uid = some entry' ∧ entry'.validationView = entry :=
  Option.map_eq_some_iff.mp ((validationView_find?_acts schema uid).symm.trans h)

private theorem PartialSchema.wfEnv_ets_contains (schema : PartialSchema) (ety : EntityType) :
    schema.wfEnv.ets.contains ety = schema.ets.contains ety := by
  simp [PartialSchema.wfEnv, EntitySchema.contains, Map.contains, validationView_find?_ets]

private theorem PartialSchema.wfEnv_acts_contains (schema : PartialSchema) (uid : EntityUID) :
    schema.wfEnv.acts.contains uid = schema.acts.contains uid := by
  simp [PartialSchema.wfEnv, ActionSchema.contains, Map.contains, validationView_find?_acts]

/-- The validation view keeps whether an entity type is standard or external. -/
private theorem PartialEntitySchemaEntry.validationView_isStandard
    (entry : PartialEntitySchemaEntry) :
    entry.validationView.isStandard = entry.isStandard := by
  cases entry <;> rfl

private theorem PartialSchema.WellFormed.entry {schema : PartialSchema} {ety : EntityType}
    {entry : PartialEntitySchemaEntry} (h : schema.WellFormed)
    (hfind : schema.ets.find? ety = some entry) :
    entry.validationView.WellFormed schema.wfEnv :=
  h.2.1.2 ety _ (by simp [validationView_find?_ets, hfind])

private theorem PartialSchema.WellFormed.action {schema : PartialSchema} {uid : EntityUID}
    {entry : PartialActionSchemaEntry} (h : schema.WellFormed)
    (hfind : schema.acts.find? uid = some entry) :
    entry.validationView.WellFormed schema.wfEnv :=
  h.2.2.2.1 uid _ (by simp [validationView_find?_acts, hfind])

/-- In a well-formed partial schema, every ancestor of an entity type is standard or external. -/
private theorem PartialSchema.WellFormed.ancestor_isStandard {schema : PartialSchema}
    {ety ancestor : EntityType} {entry : PartialEntitySchemaEntry} (h : schema.WellFormed)
    (hfind : schema.ets.find? ety = some entry) (hmem : ancestor ∈ entry.ancestors) :
    ∃ entry', schema.ets.find? ancestor = some entry' ∧ entry'.isStandard = true := by
  have hwf := h.entry hfind
  have hstd : ∃ ventry, schema.wfEnv.ets.find? ancestor = some ventry ∧ ventry.isStandard := by
    cases entry with
    | defined entry =>
      cases entry with
      | enum => exact absurd hmem (Set.not_mem_empty _)
      | standard => exact hwf.2.1 ancestor hmem
    | external => exact hwf.2.1 ancestor hmem
  obtain ⟨_, hventry, hstd⟩ := hstd
  obtain ⟨entry', hentry', rfl⟩ := PartialSchema.wfEnv_ets_find? hventry
  exact ⟨entry', hentry', by rwa [PartialEntitySchemaEntry.validationView_isStandard] at hstd⟩

/-- In a well-formed partial schema, every ancestor of an action is an action. -/
private theorem PartialSchema.WellFormed.action_ancestor {schema : PartialSchema}
    {uid ancestor : EntityUID} {entry : PartialActionSchemaEntry} (h : schema.WellFormed)
    (hfind : schema.acts.find? uid = some entry) (hmem : ancestor ∈ entry.ancestors) :
    schema.acts.contains ancestor := by
  obtain ⟨-, -, -, -, -, hancestors, -⟩ := h.action hfind
  rw [← PartialSchema.wfEnv_acts_contains]
  exact hancestors ancestor (by rwa [PartialActionSchemaEntry.validationView_ancestors])

/-- A well-formed partial schema has no action among its own ancestors. -/
private theorem PartialSchema.WellFormed.acyclic {schema : PartialSchema} {uid : EntityUID}
    {entry : PartialActionSchemaEntry} (h : schema.WellFormed)
    (hfind : schema.acts.find? uid = some entry) :
    uid ∉ entry.ancestors := by
  rw [← PartialActionSchemaEntry.validationView_ancestors]
  exact h.2.2.2.2.2.1 uid _ (by simp [validationView_find?_acts, hfind])

/-- A well-formed partial schema has transitively closed action ancestors. -/
private theorem PartialSchema.WellFormed.transitive {schema : PartialSchema}
    {uid₁ uid₂ : EntityUID} {entry₁ entry₂ : PartialActionSchemaEntry} (h : schema.WellFormed)
    (hfind₁ : schema.acts.find? uid₁ = some entry₁)
    (hfind₂ : schema.acts.find? uid₂ = some entry₂)
    (hmem : uid₂ ∈ entry₁.ancestors) :
    entry₂.ancestors ⊆ entry₁.ancestors := by
  rw [← PartialActionSchemaEntry.validationView_ancestors,
    ← PartialActionSchemaEntry.validationView_ancestors]
  exact h.2.2.2.2.2.2 uid₁ _ uid₂ _
    (by simp [validationView_find?_acts, hfind₁])
    (by simp [validationView_find?_acts, hfind₂])
    (by rwa [PartialActionSchemaEntry.validationView_ancestors])

/-- A well-formed partial schema declares no action type as an entity type. -/
private theorem PartialSchema.WellFormed.disjoint {schema : PartialSchema} {uid : EntityUID}
    (h : schema.WellFormed) (haction : schema.acts.contains uid) :
    ¬schema.ets.contains uid.ty := by
  rw [← PartialSchema.wfEnv_ets_contains]
  exact (PartialSchema.wellFormed_iff.mp h).2.2.2.2.1 uid
    (by rw [PartialSchema.wfEnv_acts_contains]; exact haction)

/-- In a well-formed partial schema, every entity entry has well-formed ancestors. -/
private theorem PartialSchema.WellFormed.ancestors_wf {schema : PartialSchema}
    {ety : EntityType} {entry : PartialEntitySchemaEntry} (h : schema.WellFormed)
    (hfind : schema.ets.find? ety = some entry) :
    entry.ancestors.WellFormed := by
  have hwf := h.entry hfind
  cases entry with
  | defined entry =>
    cases entry with
    | standard => exact hwf.1
    | enum => exact Set.empty_wf
  | external => exact hwf.1

/-- With closed ancestors, every entity type reachable through listed ancestors is listed. -/
private theorem PartialEntitySchema.AncestorsClosed.reach {ets : PartialEntitySchema}
    (h : ets.AncestorsClosed) {ety ancestor : EntityType} {entry : PartialEntitySchemaEntry}
    (hfind : ets.find? ety = some entry)
    (hreach : Relation.TransGen (fun x y => ∃ e, ets.find? x = some e ∧ y ∈ e.ancestors)
      ety ancestor) :
    ancestor ∈ entry.ancestors := by
  induction hreach with
  | single hedge =>
    obtain ⟨e, he, hmem⟩ := hedge
    rw [hfind, Option.some.injEq] at he
    exact he ▸ hmem
  | tail _ hedge ih =>
    obtain ⟨e, he, hmem⟩ := hedge
    exact Set.mem_subset_mem hmem (h _ _ _ _ hfind ih he)

/-- The validation view keeps an entity type's ancestors. -/
private theorem PartialEntitySchemaEntry.validationView_ancestors
    (entry : PartialEntitySchemaEntry) :
    entry.validationView.ancestors = entry.ancestors := by
  cases entry <;> rfl

/-- An external entity type's view is well-formed when its ancestors are well-formed and standard. -/
private theorem PartialEntitySchemaEntry.external_validationView_wf {env : TypeEnv}
    {ancestors : Set EntityType} (hwf : ancestors.WellFormed)
    (hstandard : ∀ a ∈ ancestors,
      ∃ entry, env.ets.find? a = some entry ∧ entry.isStandard) :
    (PartialEntitySchemaEntry.external ancestors).validationView.WellFormed env :=
  ⟨hwf, hstandard, emptyRecord_wf, emptyRecord_lifted, by simp⟩

/-- An external action's view is well-formed when its ancestors are a well-formed set of actions. -/
private theorem PartialActionSchemaEntry.external_validationView_wf {env : TypeEnv}
    {ancestors : Set EntityUID} (hwf : ancestors.WellFormed)
    (hactions : ∀ a ∈ ancestors, env.acts.contains a) :
    (PartialActionSchemaEntry.external ancestors).validationView.WellFormed env :=
  ⟨Set.empty_wf, Set.empty_wf, hwf,
    fun _ h => by simp [PartialActionSchemaEntry.validationView, Set.contains] at h,
    fun _ h => by simp [PartialActionSchemaEntry.validationView, Set.contains] at h,
    hactions, emptyRecord_wf, emptyRecord_lifted⟩

-- Facts about `DeclarationsKept`.

private theorem DeclarationsKept.acts_contains {s t : PartialSchema} (h : DeclarationsKept s t)
    {uid : EntityUID} (hs : s.acts.contains uid) :
    t.acts.contains uid := by
  obtain ⟨entry, hentry⟩ := Map.contains_iff_some_find?.mp hs
  obtain ⟨entry', hentry', -⟩ := h.actions uid entry hentry
  exact Map.contains_iff_some_find?.mpr ⟨entry', hentry'⟩

private theorem DeclarationsKept.entityType_wf {s t : PartialSchema} (h : DeclarationsKept s t)
    {ety : EntityType} (hwf : EntityType.WellFormed s.wfEnv ety) :
    EntityType.WellFormed t.wfEnv ety := by
  rcases hwf with hets | ⟨uid, hacts, hty⟩
  · left
    rw [PartialSchema.wfEnv_ets_contains] at hets ⊢
    exact h.entities ety hets
  · right
    rw [PartialSchema.wfEnv_acts_contains] at hacts
    exact ⟨uid, by rw [PartialSchema.wfEnv_acts_contains]; exact h.acts_contains hacts, hty⟩

private theorem DeclarationsKept.cedarType_wf {s t : PartialSchema} (h : DeclarationsKept s t)
    {ty : CedarType} (hwf : CedarType.WellFormed s.wfEnv ty) :
    CedarType.WellFormed t.wfEnv ty :=
  CedarType.WellFormed.mono (fun _ => h.entityType_wf) hwf

/-- An ancestor listed in a well-formed `s` is standard or external in `t`. -/
private theorem DeclarationsKept.ancestor_isStandard {s t : PartialSchema}
    (h : DeclarationsKept s t) (hs : s.WellFormed) {ety ancestor : EntityType}
    {entry : PartialEntitySchemaEntry}
    (hfind : s.ets.find? ety = some entry) (hmem : ancestor ∈ entry.ancestors) :
    ∃ ventry, t.wfEnv.ets.find? ancestor = some ventry ∧ ventry.isStandard = true := by
  obtain ⟨entry', hentry', hstd⟩ := hs.ancestor_isStandard hfind hmem
  obtain ⟨entry'', hentry'', hstd'⟩ := h.standard _ _ hentry' hstd
  exact ⟨entry''.validationView,
    by rw [PartialSchema.wfEnv, validationView_find?_ets, hentry'']; rfl,
    by rw [PartialEntitySchemaEntry.validationView_isStandard]; exact hstd'⟩

/-- A definition of a well-formed `s` is well-formed in `t`. -/
private theorem DeclarationsKept.definition_wf {s t : PartialSchema}
    (h : DeclarationsKept s t) (hs : s.WellFormed) {ety : EntityType}
    {entry : EntitySchemaEntry} (hfind : s.ets.find? ety = some (.defined entry)) :
    entry.WellFormed t.wfEnv := by
  have hwf := hs.entry hfind
  cases entry with
  | enum => exact hwf
  | standard std =>
    obtain ⟨hancestors, -, hattrs, hlifted, htags⟩ := hwf
    exact ⟨hancestors, fun _ hmem => h.ancestor_isStandard hs hfind hmem,
      h.cedarType_wf hattrs, hlifted,
      fun ty hty => ⟨h.cedarType_wf (htags ty hty).1, (htags ty hty).2⟩⟩

/-- An action of a well-formed `s` is well-formed in `t`. -/
private theorem DeclarationsKept.action_wf {s t : PartialSchema}
    (h : DeclarationsKept s t) (hs : s.WellFormed) {uid : EntityUID}
    {entry : PartialActionSchemaEntry} (hfind : s.acts.find? uid = some entry) :
    entry.validationView.WellFormed t.wfEnv := by
  obtain ⟨h₁, h₂, h₃, hprincipals, hresources, hancestors, hcontext, hlifted⟩ := hs.action hfind
  refine ⟨h₁, h₂, h₃, fun ety hety => h.entityType_wf (hprincipals ety hety),
    fun ety hety => h.entityType_wf (hresources ety hety), fun uid hmem => ?_,
    h.cedarType_wf hcontext, hlifted⟩
  have := hancestors uid hmem
  rw [PartialSchema.wfEnv_acts_contains] at this ⊢
  exact h.acts_contains this

/-- In `t`, the ancestors of an ancestor of an action of a well-formed `s` are ancestors of that action. -/
private theorem DeclarationsKept.transitive {s t : PartialSchema}
    (h : DeclarationsKept s t) (hs : s.WellFormed) {uid₁ uid₂ : EntityUID}
    {entry₁ entry₂ : PartialActionSchemaEntry}
    (hfind₁ : s.acts.find? uid₁ = some entry₁) (hfind₂ : t.acts.find? uid₂ = some entry₂)
    (hmem : uid₂ ∈ entry₁.ancestors) :
    entry₂.ancestors ⊆ entry₁.ancestors := by
  obtain ⟨entry₂', hentry₂'⟩ := Map.contains_iff_some_find?.mp (hs.action_ancestor hfind₁ hmem)
  obtain ⟨entry₂'', hentry₂'', hancestors⟩ := h.actions _ _ hentry₂'
  rw [hfind₂, Option.some.injEq] at hentry₂''
  rw [hentry₂'', hancestors]
  exact hs.transitive hfind₁ hentry₂' hmem

/-- Keeping declarations is transitive. -/
private theorem DeclarationsKept.trans {s t u : PartialSchema}
    (hst : DeclarationsKept s t) (htu : DeclarationsKept t u) :
    DeclarationsKept s u where
  entities ety h := htu.entities ety (hst.entities ety h)
  definitions ety entry h := htu.definitions ety entry (hst.definitions ety entry h)
  standard ety entry h hstd :=
    let ⟨_, h', hstd'⟩ := hst.standard ety entry h hstd
    htu.standard ety _ h' hstd'
  ancestors ety entry a h ha :=
    let ⟨_, h', ha'⟩ := hst.ancestors ety entry a h ha
    htu.ancestors ety _ a h' ha'
  actions uid entry h :=
    let ⟨_, h', hancestors'⟩ := hst.actions uid entry h
    let ⟨entry'', h'', hancestors''⟩ := htu.actions uid _ h'
    ⟨entry'', h'', hancestors''.trans hancestors'⟩
  actionDefinitions uid entry h :=
    htu.actionDefinitions uid entry (hst.actionDefinitions uid entry h)

/-- The entry of `t` for an entity type of `s` keeps the entry of `s`. -/
private theorem DeclarationsKept.entry {s t : PartialSchema} (h : DeclarationsKept s t)
    {ety : EntityType} {x z : PartialEntitySchemaEntry}
    (hx : s.ets.find? ety = some x) (hz : t.ets.find? ety = some z) :
    EntryKept x z where
  definition entry hentry := by
    have := h.definitions ety entry (hentry ▸ hx)
    rwa [hz, Option.some.injEq] at this
  standard hstd := by
    obtain ⟨z', hz', hstd'⟩ := h.standard ety x hx hstd
    rw [hz, Option.some.injEq] at hz'
    exact hz' ▸ hstd'
  ancestors := Set.subset_def.mpr fun a ha => by
    obtain ⟨z', hz', ha'⟩ := h.ancestors ety x a hx ha
    rw [hz, Option.some.injEq] at hz'
    exact hz' ▸ ha'

/-- Well-formed partial schemas that keep each other's declarations are equal. -/
private theorem DeclarationsKept.antisymm {s t : PartialSchema}
    (hs : s.WellFormed) (ht : t.WellFormed)
    (hst : DeclarationsKept s t) (hts : DeclarationsKept t s) :
    s = t := by
  have hets : s.ets = t.ets := by
    refine Map.find?_ext hs.etsMap ht.etsMap fun ety => ?_
    cases hx : s.ets.find? ety with
    | none =>
      cases hz : t.ets.find? ety with
      | none => rfl
      | some z =>
        have := hts.entities ety (Map.find?_some_implies_contains hz)
        simp [Map.contains, hx] at this
    | some x =>
      obtain ⟨z, hz⟩ := Map.contains_iff_some_find?.mp
        (hst.entities ety (Map.find?_some_implies_contains hx))
      rw [hz]
      have hxz := hst.entry hx hz
      have hzx := hts.entry hz hx
      cases x with
      | defined entry => rw [hxz.definition entry rfl]
      | external =>
        cases z with
        | defined entry => rw [hzx.definition entry rfl]
        | external =>
          have heq := (Set.subset_iff_eq (hs.ancestors_wf hx) (ht.ancestors_wf hz)).mp
            ⟨hxz.ancestors, hzx.ancestors⟩
          simp only [PartialEntitySchemaEntry.ancestors] at heq
          rw [heq]
  have hacts : s.acts = t.acts := by
    refine Map.find?_ext hs.actsMap ht.actsMap fun uid => ?_
    cases hx : s.acts.find? uid with
    | none =>
      cases hz : t.acts.find? uid with
      | none => rfl
      | some z =>
        obtain ⟨_, hx', -⟩ := hts.actions uid z hz
        simp [hx] at hx'
    | some x =>
      obtain ⟨z, hz, hancestors⟩ := hst.actions uid x hx
      rw [hz]
      cases x with
      | defined entry => rw [← hz, hst.actionDefinitions uid entry hx]
      | external =>
        cases z with
        | defined entry => simp [hts.actionDefinitions uid entry hz] at hx
        | external =>
          simp only [PartialActionSchemaEntry.ancestors] at hancestors
          rw [hancestors]
  cases s
  cases t
  dsimp only at hets hacts
  rw [hets, hacts]

-- Linking partial schemas that one partial schema keeps.

/--
Well-formed partial schemas without a common definition link when a
well-formed partial schema keeps the declarations of both.
-/
private theorem link_exists_of_kept {s₁ s₂ t : PartialSchema}
    (hs₁ : s₁.WellFormed) (hs₂ : s₂.WellFormed) (ht : t.WellFormed)
    (h₁ : DeclarationsKept s₁ t) (h₂ : DeclarationsKept s₂ t)
    (hdisjoint :
      (∀ ety e₁ e₂, s₁.ets.find? ety = some (.defined e₁) →
        s₂.ets.find? ety ≠ some (.defined e₂)) ∧
      (∀ uid e₁ e₂, s₁.acts.find? uid = some (.defined e₁) →
        s₂.acts.find? uid ≠ some (.defined e₂))) :
    ∃ t', link s₁ s₂ = .ok t' := by
  -- No action type is an entity type, since `t` declares the actions and entity types of both.
  have hcollision : collisionCheck s₁ s₂ = .ok () := by
    refine collisionCheck_of_disjoint fun uid haction => ?_
    have hty := ht.disjoint (haction.elim h₁.acts_contains h₂.acts_contains)
    exact ⟨fun h => hty (h₁.entities _ h), fun h => hty (h₂.entities _ h)⟩
  -- Entries of both inputs link, since `t` keeps both.
  obtain ⟨ets, hets⟩ :
      ∃ ets, linkMaps PartialEntitySchemaEntry.link s₁.ets s₂.ets = .ok ets := by
    refine linkMaps_exists hs₁.etsMap fun ety x y hx hy => ?_
    obtain ⟨z, hz⟩ := Map.contains_iff_some_find?.mp
      (h₁.entities ety (Map.find?_some_implies_contains hx))
    exact entity_link_exists
      (fun e₁ e₂ hx' hy' => hdisjoint.1 ety e₁ e₂ (hx' ▸ hx) (hy' ▸ hy))
      (h₁.entry hx hz) (h₂.entry hy hz)
  obtain ⟨acts, hacts⟩ :
      ∃ acts, linkMaps PartialActionSchemaEntry.link s₁.acts s₂.acts = .ok acts := by
    refine linkMaps_exists hs₁.actsMap fun uid x y hx hy => ?_
    obtain ⟨z, hz, hxz⟩ := h₁.actions uid x hx
    obtain ⟨z', hz', hyz⟩ := h₂.actions uid y hy
    rw [hz, Option.some.injEq] at hz'
    subst hz'
    exact action_link_exists
      (fun e₁ e₂ hx' hy' => hdisjoint.2 uid e₁ e₂ (hx' ▸ hx) (hy' ▸ hy))
      (hxz.symm.trans hyz)
  -- Closing keeps each definition's ancestors, which hold everything `t` reaches from it.
  obtain ⟨_, hclose⟩ := closeForLink_exists (ets := ets) fun ety std hmem => by
    have hfind := (Map.in_list_iff_find?_some (linkMaps_wf hets)).mp hmem
    obtain ⟨hwf, hz⟩ : std.ancestors.WellFormed ∧
        t.ets.find? ety = some (.defined (.standard std)) := by
      rcases linkMaps_entity_defined hets hfind with h | h
      · exact ⟨hs₁.ancestors_wf h, h₁.definitions _ _ h⟩
      · exact ⟨hs₂.ancestors_wf h, h₂.definitions _ _ h⟩
    refine (Set.subset_iff_eq (closedAncestors_wf _ _) hwf).mp
      ⟨Set.subset_def.mpr fun a ha => ?_,
        Set.subset_def.mpr fun a ha => mem_closedAncestors.mpr (.single ⟨_, hfind, ha⟩)⟩
    rw [mem_closedAncestors_linkMaps hets] at ha
    refine ht.1.reach hz (transGen_mono ?_ ha)
    rintro x y (⟨e, he, hy⟩ | ⟨e, he, hy⟩)
    · exact h₁.ancestors x e y he hy
    · exact h₂.ancestors x e y he hy
  exact ⟨_, link_of_steps hcollision hets hacts hclose⟩

-- Facts about the partial schema that completes another.

/-- The entity entry that completes an entry: an external for a definition, the view of an external. -/
private def PartialEntitySchemaEntry.complement :
    PartialEntitySchemaEntry → PartialEntitySchemaEntry
  | .defined entry => .external entry.ancestors
  | .external ancestors => .defined (PartialEntitySchemaEntry.external ancestors).validationView

/-- The action entry that completes an entry: an external for a definition, the view of an external. -/
private def PartialActionSchemaEntry.complement :
    PartialActionSchemaEntry → PartialActionSchemaEntry
  | .defined entry => .external entry.ancestors
  | .external ancestors => .defined (PartialActionSchemaEntry.external ancestors).validationView

/--
The partial schema that completes `p`: it defines the externals of `p` and
declares the other standard entity types and actions of `p` external.
-/
private def PartialSchema.complement (p : PartialSchema) : PartialSchema where
  ets := (p.ets.filter fun _ entry => entry.isStandard).mapOnValues
    PartialEntitySchemaEntry.complement
  acts := p.acts.mapOnValues PartialActionSchemaEntry.complement

private theorem PartialEntitySchemaEntry.complement_ancestors (entry : PartialEntitySchemaEntry) :
    entry.complement.ancestors = entry.ancestors := by
  cases entry <;> rfl

/-- A completing entry is viewed as an external with the same ancestors. -/
private theorem PartialEntitySchemaEntry.complement_validationView
    (entry : PartialEntitySchemaEntry) :
    entry.complement.validationView =
      (PartialEntitySchemaEntry.external entry.ancestors).validationView := by
  cases entry <;> rfl

private theorem PartialActionSchemaEntry.complement_ancestors (entry : PartialActionSchemaEntry) :
    entry.complement.ancestors = entry.ancestors := by
  cases entry <;> rfl

/-- A completing action is viewed as an external with the same ancestors. -/
private theorem PartialActionSchemaEntry.complement_validationView
    (entry : PartialActionSchemaEntry) :
    entry.complement.validationView =
      (PartialActionSchemaEntry.external entry.ancestors).validationView := by
  cases entry <;> rfl

/-- The complement completes exactly the standard and external entity types. -/
private theorem PartialSchema.complement_ets_find? {p : PartialSchema} (hp : p.ets.WellFormed)
    {ety : EntityType} {entry : PartialEntitySchemaEntry} :
    p.complement.ets.find? ety = some entry ↔
      ∃ pe, p.ets.find? ety = some pe ∧ pe.isStandard = true ∧ pe.complement = entry := by
  simp only [PartialSchema.complement, Map.find?_mapOnValues, Option.map_eq_some_iff]
  constructor
  · rintro ⟨pe, hpe, rfl⟩
    have := (Map.find?_filter_iff_find hp).mpr hpe
    exact ⟨pe, this.1, this.2, rfl⟩
  · rintro ⟨pe, hpe, hstd, rfl⟩
    exact ⟨pe, Map.find?_filter_if_find? hpe hstd, rfl⟩

private theorem PartialSchema.complement_acts_find? (p : PartialSchema) (uid : EntityUID) :
    p.complement.acts.find? uid = (p.acts.find? uid).map PartialActionSchemaEntry.complement :=
  Map.find?_mapOnValues _ _ _

/-- A partial schema and its complement define no entity type or action in common. -/
private theorem PartialSchema.complement_definitions_disjoint {p : PartialSchema}
    (hp : p.ets.WellFormed) :
    (∀ ety e₁ e₂, p.ets.find? ety = some (.defined e₁) →
      p.complement.ets.find? ety ≠ some (.defined e₂)) ∧
    (∀ uid e₁ e₂, p.acts.find? uid = some (.defined e₁) →
      p.complement.acts.find? uid ≠ some (.defined e₂)) := by
  constructor
  · intro ety e₁ e₂ h₁ h₂
    obtain ⟨_, hpe, -, hcomplement⟩ := (PartialSchema.complement_ets_find? hp).mp h₂
    rw [h₁, Option.some.injEq] at hpe
    simp [← hpe, PartialEntitySchemaEntry.complement] at hcomplement
  · intro uid e₁ e₂ h₁ h₂
    simp [PartialSchema.complement_acts_find?, h₁, PartialActionSchemaEntry.complement] at h₂

/-- The complete partial schema that defines every entry of `p` by its validation view. -/
private def PartialSchema.completion (p : PartialSchema) : PartialSchema :=
  Schema.toPartialSchema p.validationView

private theorem PartialSchema.completion_ets_find? (p : PartialSchema) (ety : EntityType) :
    p.completion.ets.find? ety =
      (p.ets.find? ety).map fun entry => .defined entry.validationView := by
  simp only [PartialSchema.completion, Schema.toPartialSchema, PartialSchema.validationView,
    Map.find?_mapOnValues, Option.map_map]
  rfl

private theorem PartialSchema.completion_acts_find? (p : PartialSchema) (uid : EntityUID) :
    p.completion.acts.find? uid =
      (p.acts.find? uid).map fun entry => .defined entry.validationView := by
  simp only [PartialSchema.completion, Schema.toPartialSchema, PartialSchema.validationView,
    Map.find?_mapOnValues, Option.map_map]
  rfl

/-- The completion of a well-formed partial schema is well-formed. -/
private theorem PartialSchema.WellFormed.completion {p : PartialSchema} (hp : p.WellFormed) :
    p.completion.WellFormed := by
  have henv : p.completion.wfEnv = p.wfEnv := by
    unfold PartialSchema.wfEnv PartialSchema.completion
    rw [toPartialSchema_validationView]
  rw [PartialSchema.wellFormed_iff, henv]
  refine ⟨?_, (PartialSchema.wellFormed_iff.mp hp).2⟩
  intro ety entry ancestor ancestorEntry hfind hmem hfind'
  rw [PartialSchema.completion_ets_find?, Option.map_eq_some_iff] at hfind hfind'
  obtain ⟨pe, hpe, rfl⟩ := hfind
  obtain ⟨pa, hpa, rfl⟩ := hfind'
  change ancestor ∈ pe.validationView.ancestors at hmem
  change pa.validationView.ancestors ⊆ pe.validationView.ancestors
  rw [PartialEntitySchemaEntry.validationView_ancestors] at hmem ⊢
  rw [PartialEntitySchemaEntry.validationView_ancestors]
  exact hp.1 _ _ _ _ hpe hmem hpa

/-- The complement of a well-formed partial schema is well-formed. -/
private theorem PartialSchema.WellFormed.complement {p : PartialSchema} (hp : p.WellFormed) :
    p.complement.WellFormed := by
  have hets : ∀ {ety entry}, p.complement.ets.find? ety = some entry ↔
      ∃ pe, p.ets.find? ety = some pe ∧ pe.isStandard = true ∧ pe.complement = entry :=
    PartialSchema.complement_ets_find? hp.etsMap
  -- Every standard entity type of `p` is standard in the complement.
  have hstandard : ∀ ety pe, p.ets.find? ety = some pe → pe.isStandard = true →
      ∃ ventry, p.complement.wfEnv.ets.find? ety = some ventry ∧ ventry.isStandard := by
    intro ety pe hpe hstd
    refine ⟨pe.complement.validationView, ?_,
      by rw [PartialEntitySchemaEntry.complement_validationView]; rfl⟩
    rw [PartialSchema.wfEnv, validationView_find?_ets, hets.mpr ⟨pe, hpe, hstd, rfl⟩]
    rfl
  rw [PartialSchema.wellFormed_iff]
  refine ⟨?closed, ⟨?etsMap, ?ets⟩, ⟨?actsMap, ?acts, ?disjoint, ?acyclic, ?transitive⟩⟩
  case closed =>
    intro ety entry ancestor ancestorEntry hfind hmem hfind'
    obtain ⟨pe, hpe, -, rfl⟩ := hets.mp hfind
    obtain ⟨pa, hpa, -, rfl⟩ := hets.mp hfind'
    rw [PartialEntitySchemaEntry.complement_ancestors] at hmem ⊢
    rw [PartialEntitySchemaEntry.complement_ancestors]
    exact hp.1 _ _ _ _ hpe hmem hpa
  case etsMap =>
    exact Map.mapOnValues_wf.mp (Map.mapOnValues_wf.mp (Map.filter_wf _ _ hp.etsMap))
  case ets =>
    intro ety ventry hventry
    obtain ⟨entry, hfind, rfl⟩ := PartialSchema.wfEnv_ets_find? hventry
    obtain ⟨pe, hpe, -, rfl⟩ := hets.mp hfind
    rw [PartialEntitySchemaEntry.complement_validationView]
    refine PartialEntitySchemaEntry.external_validationView_wf (hp.ancestors_wf hpe)
      fun a ha => ?_
    obtain ⟨pa, hpa, hstd⟩ := hp.ancestor_isStandard hpe ha
    exact hstandard a pa hpa hstd
  case actsMap => exact Map.mapOnValues_wf.mp (Map.mapOnValues_wf.mp hp.actsMap)
  case acts =>
    intro uid ventry hventry
    obtain ⟨entry, hfind, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry
    rw [PartialSchema.complement_acts_find?, Option.map_eq_some_iff] at hfind
    obtain ⟨pa, hpa, rfl⟩ := hfind
    rw [PartialActionSchemaEntry.complement_validationView]
    obtain ⟨-, -, hwf, -⟩ := hp.action hpa
    refine PartialActionSchemaEntry.external_validationView_wf
      (by rwa [PartialActionSchemaEntry.validationView_ancestors] at hwf) fun a ha => ?_
    rw [PartialSchema.wfEnv_acts_contains]
    simp only [PartialSchema.complement, Map.contains_mapOnValues]
    exact hp.action_ancestor hpa ha
  case disjoint =>
    intro uid haction
    rw [PartialSchema.wfEnv_acts_contains] at haction
    simp only [PartialSchema.complement, Map.contains_mapOnValues] at haction
    rw [PartialSchema.wfEnv_ets_contains]
    intro hety
    obtain ⟨entry, hentry⟩ := Map.contains_iff_some_find?.mp hety
    obtain ⟨pe, hpe, -⟩ := hets.mp hentry
    exact hp.disjoint haction (Map.find?_some_implies_contains hpe)
  case acyclic =>
    intro uid ventry hventry
    obtain ⟨entry, hfind, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry
    rw [PartialSchema.complement_acts_find?, Option.map_eq_some_iff] at hfind
    obtain ⟨pa, hpa, rfl⟩ := hfind
    rw [PartialActionSchemaEntry.validationView_ancestors,
      PartialActionSchemaEntry.complement_ancestors]
    exact hp.acyclic hpa
  case transitive =>
    intro uid₁ ventry₁ uid₂ ventry₂ hventry₁ hventry₂ hmem
    obtain ⟨entry₁, hfind₁, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry₁
    obtain ⟨entry₂, hfind₂, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry₂
    rw [PartialSchema.complement_acts_find?, Option.map_eq_some_iff] at hfind₁ hfind₂
    obtain ⟨pa₁, hpa₁, rfl⟩ := hfind₁
    obtain ⟨pa₂, hpa₂, rfl⟩ := hfind₂
    simp only [PartialActionSchemaEntry.validationView_ancestors,
      PartialActionSchemaEntry.complement_ancestors] at hmem ⊢
    exact hp.transitive hpa₁ hpa₂ hmem

/-- The completion of `p` keeps the declarations of `p`. -/
private theorem DeclarationsKept.completion (p : PartialSchema) :
    DeclarationsKept p p.completion where
  entities ety h := by
    simpa [Map.contains, PartialSchema.completion_ets_find?] using h
  definitions ety entry h := by
    rw [PartialSchema.completion_ets_find?, h]
    rfl
  standard ety entry h hstd :=
    ⟨.defined entry.validationView, by rw [PartialSchema.completion_ets_find?, h]; rfl,
      by rw [← hstd]; exact PartialEntitySchemaEntry.validationView_isStandard entry⟩
  ancestors ety entry a h ha :=
    ⟨.defined entry.validationView, by rw [PartialSchema.completion_ets_find?, h]; rfl,
      by
        show a ∈ entry.validationView.ancestors
        rwa [PartialEntitySchemaEntry.validationView_ancestors]⟩
  actions uid entry h :=
    ⟨.defined entry.validationView, by rw [PartialSchema.completion_acts_find?, h]; rfl,
      PartialActionSchemaEntry.validationView_ancestors entry⟩
  actionDefinitions uid entry h := by
    rw [PartialSchema.completion_acts_find?, h]
    rfl

/-- The completion of `p` keeps the declarations of the complement of `p`. -/
private theorem DeclarationsKept.complement_completion {p : PartialSchema}
    (hp : p.ets.WellFormed) :
    DeclarationsKept p.complement p.completion where
  entities ety h := by
    obtain ⟨entry, hentry⟩ := Map.contains_iff_some_find?.mp h
    obtain ⟨pe, hpe, -⟩ := (PartialSchema.complement_ets_find? hp).mp hentry
    simp [Map.contains, PartialSchema.completion_ets_find?, hpe]
  definitions ety entry h := by
    obtain ⟨pe, hpe, -, hcomplement⟩ := (PartialSchema.complement_ets_find? hp).mp h
    cases pe with
    | defined => simp [PartialEntitySchemaEntry.complement] at hcomplement
    | external =>
      simp only [PartialEntitySchemaEntry.complement, PartialEntitySchemaEntry.defined.injEq]
        at hcomplement
      rw [PartialSchema.completion_ets_find?, hpe, ← hcomplement]
      rfl
  standard ety entry h _ := by
    obtain ⟨pe, hpe, hstd, -⟩ := (PartialSchema.complement_ets_find? hp).mp h
    exact ⟨.defined pe.validationView, by rw [PartialSchema.completion_ets_find?, hpe]; rfl,
      by rw [← hstd]; exact PartialEntitySchemaEntry.validationView_isStandard pe⟩
  ancestors ety entry a h ha := by
    obtain ⟨pe, hpe, -, rfl⟩ := (PartialSchema.complement_ets_find? hp).mp h
    refine ⟨.defined pe.validationView,
      by rw [PartialSchema.completion_ets_find?, hpe]; rfl, ?_⟩
    show a ∈ pe.validationView.ancestors
    rwa [PartialEntitySchemaEntry.validationView_ancestors,
      ← PartialEntitySchemaEntry.complement_ancestors]
  actions uid entry h := by
    rw [PartialSchema.complement_acts_find?, Option.map_eq_some_iff] at h
    obtain ⟨pa, hpa, rfl⟩ := h
    exact ⟨.defined pa.validationView, by rw [PartialSchema.completion_acts_find?, hpa]; rfl,
      by rw [PartialActionSchemaEntry.complement_ancestors,
        ← PartialActionSchemaEntry.validationView_ancestors pa]; rfl⟩
  actionDefinitions uid entry h := by
    rw [PartialSchema.complement_acts_find?, Option.map_eq_some_iff] at h
    obtain ⟨pa, hpa, hcomplement⟩ := h
    cases pa with
    | defined => simp [PartialActionSchemaEntry.complement] at hcomplement
    | external =>
      simp only [PartialActionSchemaEntry.complement, PartialActionSchemaEntry.defined.injEq]
        at hcomplement
      rw [PartialSchema.completion_acts_find?, hpa, ← hcomplement]
      rfl

/-- A partial schema keeping the declarations of `p` and its complement keeps the completion's. -/
private theorem DeclarationsKept.completion_of_complement {p t : PartialSchema}
    (hp : p.ets.WellFormed) (hpt : DeclarationsKept p t)
    (hct : DeclarationsKept p.complement t) :
    DeclarationsKept p.completion t where
  entities ety h := by
    simp only [Map.contains, PartialSchema.completion_ets_find?, Option.isSome_map] at h
    exact hpt.entities ety h
  definitions ety entry h := by
    rw [PartialSchema.completion_ets_find?, Option.map_eq_some_iff] at h
    obtain ⟨pe, hpe, hview⟩ := h
    simp only [PartialEntitySchemaEntry.defined.injEq] at hview
    cases pe with
    | defined => exact hview ▸ hpt.definitions ety _ hpe
    | external =>
      exact hct.definitions ety entry ((PartialSchema.complement_ets_find? hp).mpr
        ⟨_, hpe, rfl, by rw [← hview]; rfl⟩)
  standard ety entry h hstd := by
    rw [PartialSchema.completion_ets_find?, Option.map_eq_some_iff] at h
    obtain ⟨pe, hpe, rfl⟩ := h
    exact hpt.standard ety pe hpe
      (by rw [← PartialEntitySchemaEntry.validationView_isStandard]; exact hstd)
  ancestors ety entry a h ha := by
    rw [PartialSchema.completion_ets_find?, Option.map_eq_some_iff] at h
    obtain ⟨pe, hpe, rfl⟩ := h
    change a ∈ pe.validationView.ancestors at ha
    rw [PartialEntitySchemaEntry.validationView_ancestors] at ha
    exact hpt.ancestors ety pe a hpe ha
  actions uid entry h := by
    rw [PartialSchema.completion_acts_find?, Option.map_eq_some_iff] at h
    obtain ⟨pa, hpa, rfl⟩ := h
    obtain ⟨entry', hentry', hancestors⟩ := hpt.actions uid pa hpa
    exact ⟨entry', hentry',
      hancestors.trans (PartialActionSchemaEntry.validationView_ancestors pa).symm⟩
  actionDefinitions uid entry h := by
    rw [PartialSchema.completion_acts_find?, Option.map_eq_some_iff] at h
    obtain ⟨pa, hpa, hview⟩ := h
    simp only [PartialActionSchemaEntry.defined.injEq] at hview
    cases pa with
    | defined => exact hview ▸ hpt.actionDefinitions uid _ hpa
    | external =>
      apply hct.actionDefinitions uid entry
      rw [PartialSchema.complement_acts_find?, hpa, ← hview]
      rfl

---- Minor Linker Results ---

/--
Every entity or action definition from either input appears unchanged in the
result.
-/
theorem linker_preserves_definitions
    {p c t : PartialSchema}
    (hlink : link p c = .ok t) :
    (∀ ety entry, p.ets.find? ety = some (.defined entry) →
      t.ets.find? ety = some (.defined entry)) ∧
    (∀ ety entry, c.ets.find? ety = some (.defined entry) →
      t.ets.find? ety = some (.defined entry)) ∧
    (∀ uid entry, p.acts.find? uid = some (.defined entry) →
      t.acts.find? uid = some (.defined entry)) ∧
    (∀ uid entry, c.acts.find? uid = some (.defined entry) →
      t.acts.find? uid = some (.defined entry)) := by
  obtain ⟨-, ets, hets, hacts, hclose⟩ := link_ok hlink
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ety entry hfind
    obtain ⟨_, hlinked, rfl⟩ :=
      linkMaps_find?_left hets hfind (fun _ _ => entity_link_defined) rfl
    exact closeForLink_find?_defined hclose hlinked
  · intro ety entry hfind
    obtain ⟨_, hlinked, rfl⟩ := linkMaps_find?_right hets hfind
      (fun _ _ h => entity_link_defined (entity_link_comm _ _ _ _ h)) rfl
    exact closeForLink_find?_defined hclose hlinked
  · intro uid entry hfind
    obtain ⟨_, hlinked, rfl⟩ :=
      linkMaps_find?_left hacts hfind (fun _ _ => action_link_defined) rfl
    exact hlinked
  · intro uid entry hfind
    obtain ⟨_, hlinked, rfl⟩ := linkMaps_find?_right hacts hfind
      (fun _ _ h => action_link_defined (action_link_comm _ _ _ _ h)) rfl
    exact hlinked

/--
The result declares exactly the entity types declared by either input.
-/
theorem linker_preserves_entity_declarations
    {p c t : PartialSchema}
    (hlink : link p c = .ok t)
    (ety : EntityType) :
    t.ets.contains ety ↔ p.ets.contains ety ∨ c.ets.contains ety := by
  obtain ⟨-, ets, hets, -, hclose⟩ := link_ok hlink
  simp only [Map.contains, closeForLink_find? hclose, Option.isSome_map]
  exact linkMaps_contains hets ety

/--
The result declares exactly the action UIDs declared by either input.
-/
theorem linker_preserves_action_declarations
    {p c t : PartialSchema}
    (hlink : link p c = .ok t)
    (uid : EntityUID) :
    t.acts.contains uid ↔ p.acts.contains uid ∨ c.acts.contains uid := by
  obtain ⟨-, -, -, hacts, -⟩ := link_ok hlink
  exact linkMaps_contains hacts uid

/--
Every action from either input keeps its ancestors in the result.
-/
theorem linker_preserves_action_ancestors
    {p c t : PartialSchema}
    (hlink : link p c = .ok t) :
    (∀ uid entry, p.acts.find? uid = some entry →
      ∃ entry', t.acts.find? uid = some entry' ∧ entry'.ancestors = entry.ancestors) ∧
    (∀ uid entry, c.acts.find? uid = some entry →
      ∃ entry', t.acts.find? uid = some entry' ∧ entry'.ancestors = entry.ancestors) := by
  obtain ⟨-, -, -, hacts, -⟩ := link_ok hlink
  exact ⟨fun _ _ hfind => linkMaps_find?_left hacts hfind (fun _ _ => action_link_ancestors) rfl,
    fun _ _ hfind => linkMaps_find?_right hacts hfind
      (fun _ _ h => action_link_ancestors (action_link_comm _ _ _ _ h)) rfl⟩

/--
Every standard or external entity type from either input is standard or
external in the result. In particular, an external entity type never links to
an enumerated entity type.
-/
theorem linker_preserves_standard_entities
    {p c t : PartialSchema}
    (hlink : link p c = .ok t) :
    (∀ ety entry, p.ets.find? ety = some entry → entry.isStandard = true →
      ∃ entry', t.ets.find? ety = some entry' ∧ entry'.isStandard = true) ∧
    (∀ ety entry, c.ets.find? ety = some entry → entry.isStandard = true →
      ∃ entry', t.ets.find? ety = some entry' ∧ entry'.isStandard = true) := by
  obtain ⟨-, ets, hets, -, hclose⟩ := link_ok hlink
  have hclosed : ∀ ety entry, ets.find? ety = some entry → entry.isStandard = true →
      ∃ entry', t.ets.find? ety = some entry' ∧ entry'.isStandard = true :=
    fun ety entry hfind hstd =>
      ⟨_, by rw [closeForLink_find? hclose, hfind]; rfl, by rw [withAncestors_isStandard]; exact hstd⟩
  constructor
  · intro ety entry hfind hstd
    obtain ⟨_, hlinked, hstd'⟩ :=
      linkMaps_find?_left hets hfind (fun _ _ h => entity_link_isStandard h hstd) hstd
    exact hclosed _ _ hlinked hstd'
  · intro ety entry hfind hstd
    obtain ⟨_, hlinked, hstd'⟩ := linkMaps_find?_right hets hfind
      (fun _ _ h => entity_link_isStandard (entity_link_comm _ _ _ _ h) hstd) hstd
    exact hclosed _ _ hlinked hstd'

/--
The result never declares the entity type of an action as an entity type.
-/
theorem linker_action_types_not_entity_types
    {p c t : PartialSchema}
    {uid : EntityUID}
    (hlink : link p c = .ok t)
    (haction : t.acts.contains uid) :
    ¬t.ets.contains uid.ty := by
  obtain ⟨hcollision, -⟩ := link_ok hlink
  rw [linker_preserves_entity_declarations hlink, not_or]
  exact collisionCheck_ok hcollision ((linker_preserves_action_declarations hlink uid).mp haction)

/--
Every entity definition of the result is a definition from either input.
-/
theorem linker_definitions_come_from_inputs
    {p c t : PartialSchema}
    {ety : EntityType}
    {entry : EntitySchemaEntry}
    (hlink : link p c = .ok t)
    (hfind : t.ets.find? ety = some (.defined entry)) :
    p.ets.find? ety = some (.defined entry) ∨ c.ets.find? ety = some (.defined entry) := by
  obtain ⟨-, ets, hets, -, hclose⟩ := link_ok hlink
  have hraw : ets.find? ety = some (.defined entry) := by
    have hfind' := hfind
    rw [closeForLink_find? hclose, Option.map_eq_some_iff] at hfind'
    obtain ⟨raw, hraw, hentry⟩ := hfind'
    cases raw with
    | external => simp [PartialEntitySchemaEntry.withAncestors] at hentry
    | defined raw =>
      rw [closeForLink_find?_defined hclose hraw, Option.some.injEq] at hfind
      rw [hraw, hfind]
  exact linkMaps_entity_defined hets hraw

/--
Every action entry of the result is that action's entry in either input.
-/
theorem linker_actions_come_from_inputs
    {p c t : PartialSchema}
    {uid : EntityUID}
    {entry : PartialActionSchemaEntry}
    (hlink : link p c = .ok t)
    (hfind : t.acts.find? uid = some entry) :
    p.acts.find? uid = some entry ∨ c.acts.find? uid = some entry := by
  obtain ⟨-, -, -, hacts, -⟩ := link_ok hlink
  rcases linkAt_some (hfind ▸ linkMaps_find? hacts uid) with
    ⟨h₁, -⟩ | ⟨-, h₂⟩ | ⟨x, y, h₁, h₂, hlinked⟩
  · exact .inl h₁
  · exact .inr h₂
  · rcases action_link_eq hlinked with rfl | rfl
    · exact .inl h₁
    · exact .inr h₂

/--
An entity type's ancestors in the result are exactly the entity types reachable
from it through the ancestors listed by either input.
-/
theorem linker_entity_ancestors
    {p c t : PartialSchema}
    {ety ancestor : EntityType}
    {entry : PartialEntitySchemaEntry}
    (hlink : link p c = .ok t)
    (hfind : t.ets.find? ety = some entry) :
    ancestor ∈ entry.ancestors ↔
      Relation.TransGen (fun x y =>
        (∃ e, p.ets.find? x = some e ∧ y ∈ e.ancestors) ∨
        (∃ e, c.ets.find? x = some e ∧ y ∈ e.ancestors)) ety ancestor := by
  obtain ⟨-, ets, hets, -, hclose⟩ := link_ok hlink
  rw [← mem_closedAncestors_linkMaps hets]
  rw [closeForLink_find? hclose, Option.map_eq_some_iff] at hfind
  obtain ⟨raw, hraw, rfl⟩ := hfind
  cases raw with
  | external => rfl
  | defined raw =>
    cases raw with
    | standard => rfl
    | enum =>
      -- An enumerated entity type lists no ancestors, so none are reachable from it.
      refine ⟨fun h => absurd h (Set.not_mem_empty _), fun h => ?_⟩
      obtain ⟨_, e, he, hmem⟩ := transGen_head (mem_closedAncestors.mp h)
      rw [hraw, Option.some.injEq] at he
      subst e
      exact absurd hmem (Set.not_mem_empty _)

/--
The result keeps every declaration of either input.
-/
theorem linker_keeps_declarations
    {p c t : PartialSchema}
    (hlink : link p c = .ok t) :
    DeclarationsKept p t ∧ DeclarationsKept c t := by
  obtain ⟨hpDefs, hcDefs, hpActs, hcActs⟩ := linker_preserves_definitions hlink
  have hets := linker_preserves_entity_declarations hlink
  -- An ancestor that either input lists is reachable in the result.
  have hancestors : ∀ ety ancestor,
      (∃ e, p.ets.find? ety = some e ∧ ancestor ∈ e.ancestors) ∨
      (∃ e, c.ets.find? ety = some e ∧ ancestor ∈ e.ancestors) →
      ∃ entry, t.ets.find? ety = some entry ∧ ancestor ∈ entry.ancestors := by
    intro ety ancestor hedge
    obtain ⟨entry, hentry⟩ : ∃ entry, t.ets.find? ety = some entry := by
      rw [← Map.contains_iff_some_find?, hets]
      exact hedge.imp (fun ⟨_, he, _⟩ => Map.find?_some_implies_contains he)
        (fun ⟨_, he, _⟩ => Map.find?_some_implies_contains he)
    exact ⟨entry, hentry, (linker_entity_ancestors hlink hentry).mpr (.single hedge)⟩
  exact ⟨{
      entities := fun ety h => (hets ety).mpr (.inl h)
      definitions := hpDefs
      standard := (linker_preserves_standard_entities hlink).1
      ancestors := fun ety _ _ he hmem => hancestors ety _ (.inl ⟨_, he, hmem⟩)
      actions := (linker_preserves_action_ancestors hlink).1
      actionDefinitions := hpActs
    }, {
      entities := fun ety h => (hets ety).mpr (.inr h)
      definitions := hcDefs
      standard := (linker_preserves_standard_entities hlink).2
      ancestors := fun ety _ _ he hmem => hancestors ety _ (.inr ⟨_, he, hmem⟩)
      actions := (linker_preserves_action_ancestors hlink).2
      actionDefinitions := hcActs
    }⟩

/--
A partial schema with closed ancestors that keeps the declarations of both
inputs keeps the declarations of the result.
-/
theorem linker_result_kept
    {p c t u : PartialSchema}
    (hlink : link p c = .ok t)
    (hclosed : u.ets.AncestorsClosed)
    (hpu : DeclarationsKept p u)
    (hcu : DeclarationsKept c u) :
    DeclarationsKept t u where
  entities ety h :=
    ((linker_preserves_entity_declarations hlink ety).mp h).elim
      (hpu.entities ety) (hcu.entities ety)
  definitions ety entry h :=
    (linker_definitions_come_from_inputs hlink h).elim
      (hpu.definitions ety entry) (hcu.definitions ety entry)
  standard ety entry h hstd := by
    -- The inputs' entries are standard or external, since the result keeps their definitions.
    have hstandard : ∀ x, p.ets.find? ety = some x ∨ c.ets.find? ety = some x →
        x.isStandard = true := by
      intro x hx
      cases x with
      | external => rfl
      | defined d =>
        have hd := hx.elim ((linker_preserves_definitions hlink).1 ety d)
          ((linker_preserves_definitions hlink).2.1 ety d)
        rw [h, Option.some.injEq] at hd
        exact hd ▸ hstd
    rcases (linker_preserves_entity_declarations hlink ety).mp
      (Map.find?_some_implies_contains h) with hx | hx
    · obtain ⟨x, hx⟩ := Map.contains_iff_some_find?.mp hx
      exact hpu.standard ety x hx (hstandard x (.inl hx))
    · obtain ⟨x, hx⟩ := Map.contains_iff_some_find?.mp hx
      exact hcu.standard ety x hx (hstandard x (.inr hx))
  ancestors ety entry a h ha := by
    -- The ancestors are reachable through the inputs' ancestors, which `u` lists and closes.
    have hdeclared := (linker_preserves_entity_declarations hlink ety).mp
      (Map.find?_some_implies_contains h)
    obtain ⟨z, hz⟩ := Map.contains_iff_some_find?.mp
      (hdeclared.elim (hpu.entities ety) (hcu.entities ety))
    refine ⟨z, hz, hclosed.reach hz
      (transGen_mono ?_ ((linker_entity_ancestors hlink h).mp ha))⟩
    rintro x y (⟨e, he, hy⟩ | ⟨e, he, hy⟩)
    · exact hpu.ancestors x e y he hy
    · exact hcu.ancestors x e y he hy
  actions uid entry h :=
    (linker_actions_come_from_inputs hlink h).elim (hpu.actions uid entry) (hcu.actions uid entry)
  actionDefinitions uid entry h :=
    (linker_actions_come_from_inputs hlink h).elim
      (hpu.actionDefinitions uid entry) (hcu.actionDefinitions uid entry)

/--
No entity type or action is defined by both inputs.
-/
theorem linker_definitions_disjoint
    {p c t : PartialSchema}
    (hlink : link p c = .ok t) :
    (∀ ety e₁ e₂, p.ets.find? ety = some (.defined e₁) →
      c.ets.find? ety ≠ some (.defined e₂)) ∧
    (∀ uid e₁ e₂, p.acts.find? uid = some (.defined e₁) →
      c.acts.find? uid ≠ some (.defined e₂)) := by
  obtain ⟨-, ets, hets, hacts, -⟩ := link_ok hlink
  constructor
  · intro ety e₁ e₂ h₁ h₂
    have := linkMaps_find? hets ety
    simp [h₁, h₂, linkAt, PartialEntitySchemaEntry.link, Functor.map, Except.map] at this
  · intro uid e₁ e₂ h₁ h₂
    have := linkMaps_find? hacts uid
    simp [h₁, h₂, linkAt, PartialActionSchemaEntry.link, Functor.map, Except.map] at this


---- Major Linker results ---

/-- Changing the input order does not change a successful link. -/
theorem linker_commutativity
    {p c t : PartialSchema}
    (hc : c.WellFormed)
    (hlink : link p c = .ok t) :
    link c p = .ok t := by
  obtain ⟨hcollision, ets, hets, hacts, hclose⟩ := link_ok hlink
  rw [link_eq, collisionCheck_comm hcollision,
    linkMaps_comm hc.etsMap entity_link_comm hets,
    linkMaps_comm hc.actsMap action_link_comm hacts]
  simp only [Except.bind_ok, hclose]
  rfl

/-- Changing the input order does not change whether linking fails. -/
theorem linker_commutativity_error
    {p c : PartialSchema}
    (hp : p.WellFormed)
    (hc : c.WellFormed) :
    (∃ err, link p c = .error err) ↔
    (∃ err, link c p = .error err) := by
  constructor <;> rintro ⟨err, herror⟩
  · cases hreverse : link c p with
    | error err' => exact ⟨err', rfl⟩
    | ok t => simp [linker_commutativity hp hreverse] at herror
  · cases hreverse : link p c with
    | error err' => exact ⟨err', rfl⟩
    | ok t => simp [linker_commutativity hc hreverse] at herror

/-- Linking well-formed partial schemas produces a well-formed partial schema. -/
theorem linker_preserves_well_formedness
    {p c t : PartialSchema}
    (hp : p.WellFormed)
    (hc : c.WellFormed)
    (hlink : link p c = .ok t) :
    t.WellFormed := by
  obtain ⟨hpt, hct⟩ := linker_keeps_declarations hlink
  rw [PartialSchema.wellFormed_iff]
  refine ⟨?closed, ⟨?etsMap, ?ets⟩, ⟨?actsMap, ?acts, ?disjoint, ?acyclic, ?transitive⟩⟩
  case closed =>
    -- Ancestors are reachable sets, and reachability is transitive.
    intro ety entry ancestor ancestorEntry hfind hmem hfind'
    rw [Set.subset_def]
    intro a ha
    rw [linker_entity_ancestors hlink hfind] at hmem ⊢
    exact hmem.trans ((linker_entity_ancestors hlink hfind').mp ha)
  case etsMap => exact Map.mapOnValues_wf.mp (link_ets_wf hlink)
  case ets =>
    intro ety ventry hventry
    obtain ⟨entry, hfind, rfl⟩ := PartialSchema.wfEnv_ets_find? hventry
    cases entry with
    | defined entry =>
      rcases linker_definitions_come_from_inputs hlink hfind with h | h
      · exact hpt.definition_wf hp h
      · exact hct.definition_wf hc h
    | external ancestors =>
      -- Every ancestor is listed by an input, which declares it standard or external.
      refine PartialEntitySchemaEntry.external_validationView_wf
        (link_external_ancestors_wf hlink hfind) fun a hmem => ?_
      obtain ⟨_, hedge⟩ := transGen_tail ((linker_entity_ancestors hlink hfind).mp hmem)
      rcases hedge with ⟨_, he, hmem⟩ | ⟨_, he, hmem⟩
      · exact hpt.ancestor_isStandard hp he hmem
      · exact hct.ancestor_isStandard hc he hmem
  case actsMap => exact Map.mapOnValues_wf.mp (link_acts_wf hlink)
  case acts =>
    intro uid ventry hventry
    obtain ⟨entry, hfind, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry
    rcases linker_actions_come_from_inputs hlink hfind with h | h
    · exact hpt.action_wf hp h
    · exact hct.action_wf hc h
  case disjoint =>
    intro uid haction
    rw [PartialSchema.wfEnv_acts_contains] at haction
    rw [PartialSchema.wfEnv_ets_contains]
    exact linker_action_types_not_entity_types hlink haction
  case acyclic =>
    intro uid ventry hventry
    obtain ⟨entry, hfind, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry
    rw [PartialActionSchemaEntry.validationView_ancestors]
    rcases linker_actions_come_from_inputs hlink hfind with h | h
    · exact hp.acyclic h
    · exact hc.acyclic h
  case transitive =>
    intro uid₁ ventry₁ uid₂ ventry₂ hventry₁ hventry₂ hmem
    obtain ⟨entry₁, hfind₁, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry₁
    obtain ⟨entry₂, hfind₂, rfl⟩ := PartialSchema.wfEnv_acts_find? hventry₂
    rw [PartialActionSchemaEntry.validationView_ancestors] at hmem ⊢
    rw [PartialActionSchemaEntry.validationView_ancestors]
    rcases linker_actions_come_from_inputs hlink hfind₁ with h | h
    · exact hpt.transitive hp h hfind₂ hmem
    · exact hct.transitive hc h hfind₂ hmem

/--
A complete link passes the existing schema well-formedness check.
-/
theorem linker_completed_schema_well_formed
    {p c t : PartialSchema}
    {schema : Schema}
    (hp : p.WellFormed)
    (hc : c.WellFormed)
    (hlink : link p c = .ok t)
    (hcomplete : t.asSchema? = some schema) :
    schema.validateWellFormed = .ok () := by
  obtain ⟨-, hwf⟩ :=
    PartialSchema.wellFormed_iff.mp (linker_preserves_well_formedness hp hc hlink)
  have hview := validationView_eq_of_asSchema? hcomplete
  -- Every environment of `schema` has the maps of the environment `t.WellFormed` checks.
  refine Cedar.Thm.schema_validate_well_formed_is_complete fun env henv => ?_
  obtain ⟨hets, hacts, -⟩ := Cedar.Thm.mem_environments henv
  exact TypeEnv.maps_wf_of_eq (by simp [PartialSchema.wfEnv, hview, hets])
    (by simp [PartialSchema.wfEnv, hview, hacts]) hwf

/-- Changing the grouping does not change a successful link. -/
theorem linker_associativity
    {p c d t₁ t : PartialSchema}
    (hp : p.WellFormed)
    (hc : c.WellFormed)
    (hd : d.WellFormed)
    (hpc : link p c = .ok t₁)
    (hpcd : link t₁ d = .ok t) :
    ∃ t₂, link c d = .ok t₂ ∧ link p t₂ = .ok t := by
  have ht₁ := linker_preserves_well_formedness hp hc hpc
  have ht := linker_preserves_well_formedness ht₁ hd hpcd
  obtain ⟨hpt₁, hct₁⟩ := linker_keeps_declarations hpc
  obtain ⟨ht₁t, hdt⟩ := linker_keeps_declarations hpcd
  have hpt := hpt₁.trans ht₁t
  have hct := hct₁.trans ht₁t
  -- `c` and `d` link, since `t` keeps both and `t₁` keeps the definitions of `c`.
  obtain ⟨t₂, hcd⟩ := link_exists_of_kept hc hd ht hct hdt
    ⟨fun ety e₁ e₂ h =>
        (linker_definitions_disjoint hpcd).1 ety e₁ e₂ (hct₁.definitions ety e₁ h),
      fun uid e₁ e₂ h =>
        (linker_definitions_disjoint hpcd).2 uid e₁ e₂ (hct₁.actionDefinitions uid e₁ h)⟩
  have ht₂ := linker_preserves_well_formedness hc hd hcd
  have ht₂t := linker_result_kept hcd ht.1 hct hdt
  -- `p` and `t₂` link, since `t` keeps both and each definition of `t₂` is one of `c` or `d`.
  obtain ⟨t', hpt₂⟩ := link_exists_of_kept hp ht₂ ht hpt ht₂t
    ⟨fun ety e₁ e₂ h₁ h₂ => (linker_definitions_come_from_inputs hcd h₂).elim
        ((linker_definitions_disjoint hpc).1 ety e₁ e₂ h₁)
        ((linker_definitions_disjoint hpcd).1 ety e₁ e₂ (hpt₁.definitions ety e₁ h₁)),
      fun uid e₁ e₂ h₁ h₂ => (linker_actions_come_from_inputs hcd h₂).elim
        ((linker_definitions_disjoint hpc).2 uid e₁ e₂ h₁)
        ((linker_definitions_disjoint hpcd).2 uid e₁ e₂
          (hpt₁.actionDefinitions uid e₁ h₁))⟩
  -- Both groupings give the same result, since each keeps the declarations of the other.
  have ht' := linker_preserves_well_formedness hp ht₂ hpt₂
  obtain ⟨hpt', ht₂t'⟩ := linker_keeps_declarations hpt₂
  obtain ⟨hct₂, hdt₂⟩ := linker_keeps_declarations hcd
  have ht₁t' := linker_result_kept hpc ht'.1 hpt' (hct₂.trans ht₂t')
  have heq := DeclarationsKept.antisymm ht' ht (linker_result_kept hpt₂ ht.1 hpt ht₂t)
    (linker_result_kept hpcd ht'.1 ht₁t' (hdt₂.trans ht₂t'))
  exact ⟨t₂, hcd, heq ▸ hpt₂⟩

/-- Changing the grouping does not change whether linking fails. -/
theorem linker_associativity_error
    {p c d : PartialSchema}
    (hp : p.WellFormed)
    (hc : c.WellFormed)
    (hd : d.WellFormed) :
    (∃ err, (do
      let t₁ ← link p c
      link t₁ d) = .error err) ↔
    (∃ err, (do
      let t₂ ← link c d
      link p t₂) = .error err) := by
  -- Each grouping succeeds with the result of the other.
  have hleft : ∀ t, (do let t₁ ← link p c; link t₁ d) = .ok t →
      (do let t₂ ← link c d; link p t₂) = .ok t := by
    intro t h
    obtain ⟨t₁, hpc, hpcd⟩ := do_eq_ok.mp h
    obtain ⟨t₂, hcd, hpt₂⟩ := linker_associativity hp hc hd hpc hpcd
    exact do_eq_ok.mpr ⟨t₂, hcd, hpt₂⟩
  have hright : ∀ t, (do let t₂ ← link c d; link p t₂) = .ok t →
      (do let t₁ ← link p c; link t₁ d) = .ok t := by
    intro t h
    obtain ⟨t₂, hcd, hpt₂⟩ := do_eq_ok.mp h
    -- Reverse both links, regroup, then reverse back.
    have ht₂ := linker_preserves_well_formedness hc hd hcd
    obtain ⟨t₁, hcp, hdt₁⟩ := linker_associativity hd hc hp
      (linker_commutativity hd hcd) (linker_commutativity ht₂ hpt₂)
    have ht₁ := linker_preserves_well_formedness hc hp hcp
    exact do_eq_ok.mpr ⟨t₁, linker_commutativity hp hcp, linker_commutativity ht₁ hdt₁⟩
  constructor <;> rintro ⟨err, herr⟩
  · cases h : (do let t₂ ← link c d; link p t₂) with
    | error err' => exact ⟨err', rfl⟩
    | ok t => simp [hright t h] at herr
  · cases h : (do let t₁ ← link p c; link t₁ d) with
    | error err' => exact ⟨err', rfl⟩
    | ok t => simp [hleft t h] at herr

/-- Every well-formed partial schema has a complete linking extension. -/
theorem linker_completion_exists
    {p : PartialSchema}
    (hp : p.WellFormed) :
    ∃ c t schema,
      c.WellFormed ∧
      link p c = .ok t ∧
      t.asSchema? = some schema := by
  -- Link `p` with its complement; the completion of `p` keeps the declarations of both.
  have hc := hp.complement
  have hu := hp.completion
  have hpu := DeclarationsKept.completion p
  have hcu := DeclarationsKept.complement_completion hp.etsMap
  obtain ⟨t, hlink⟩ := link_exists_of_kept hp hc hu hpu hcu
    (PartialSchema.complement_definitions_disjoint hp.etsMap)
  -- The link is the completion of `p`, since each keeps the declarations of the other.
  obtain ⟨hpt, hct⟩ := linker_keeps_declarations hlink
  have heq := DeclarationsKept.antisymm hu (linker_preserves_well_formedness hp hc hlink)
    (DeclarationsKept.completion_of_complement hp.etsMap hpt hct)
    (linker_result_kept hlink hu.1 hpu hcu)
  exact ⟨p.complement, t, p.validationView, hc, hlink,
    heq ▸ toPartialSchema_asSchema? p.validationView⟩

/-- A defined entity keeps its closed ancestor set after linking. -/
theorem stable_entity_ancestor
    {p c t : PartialSchema}
    {ety : EntityType}
    {entry : EntitySchemaEntry}
    (hp : p.WellFormed)
    (hc : c.WellFormed)
    (hlink : link p c = .ok t)
    (hentry : p.ets.find? ety = some (.defined entry)) :
    ∃ linkedEntry,
      t.ets.find? ety = some (.defined linkedEntry) ∧
      linkedEntry.ancestors = entry.ancestors :=
  ⟨entry, (linker_preserves_definitions hlink).1 _ _ hentry, rfl⟩

end Cedar.Validation
