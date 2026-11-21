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

import Cedar.Validation.Relational.Typing

/-! # Decided premises

`Decidable` instances for the typing relation's schema lookups, so that a derived generator checks them
with `decide` rather than a derived checker: a decided check has its completeness laws for free
(`DecOptCompleteAll`, `DecOptRefuteCompleteAll`), which the generators' completeness proofs need. -/

namespace Cedar.Validation.Relational

open Cedar.Spec Cedar.Data Cedar.Validation

theorem mapContains_iff_mem {α β : Type} {k : α} {v : β} {l : List (α × β)} :
    MapContains k v (.mk l) ↔ (k, v) ∈ l := by
  constructor
  · intro h
    generalize hm : (Map.mk l) = m at h
    induction h generalizing l with
    | here rest => cases hm; exact List.mem_cons_self
    | there k' v' rest _ ih => cases hm; exact List.mem_cons_of_mem _ (ih rfl)
  · intro h
    induction l with
    | nil => cases h
    | cons p l ih =>
      rcases List.mem_cons.mp h with h' | h'
      · subst h'; exact .here _ _ _
      · obtain ⟨k', v'⟩ := p; exact .there _ _ _ _ _ (ih h')

theorem setContains_mk_iff_mem {α : Type} {x : α} {l : List α} :
    SetContains x (.mk l) ↔ x ∈ l := by
  constructor
  · intro h
    generalize hs : (Set.mk l) = s at h
    induction h generalizing l with
    | here rest => cases hs; exact List.mem_cons_self
    | there y rest _ ih => cases hs; exact List.mem_cons_of_mem _ (ih rfl)
  · intro h
    induction l with
    | nil => cases h
    | cons y l ih =>
      rcases List.mem_cons.mp h with h' | h'
      · subst h'; exact .here _ _
      · exact .there _ _ _ (ih h')

/-- The value of the first binding of `⟨a, b⟩`. -/
def pairKeyLookup {v : Type} (a : EntityType) (b : String) : List (EntityUID × v) → Option v
  | [] => none
  | (k, v') :: m => if k.ty = a ∧ k.eid = b then some v' else pairKeyLookup a b m

theorem mapContainsPairKey_iff {v : Type} {a : EntityType} {b : String} {va : v}
    {l : List (EntityUID × v)} :
    MapContainsPairKey a b va (.mk l) ↔ pairKeyLookup a b l = some va := by
  constructor
  · intro h
    generalize hm : (Map.mk l) = m at h
    induction h generalizing l with
    | here => cases hm; simp [pairKeyLookup]
    | nextA hne _ ih =>
      cases hm; simp only [pairKeyLookup]; rw [if_neg (fun h => hne h.1.symm)]; exact ih rfl
    | nextB hne _ ih =>
      cases hm; simp only [pairKeyLookup]; rw [if_neg (fun h => hne h.2.symm)]; exact ih rfl
  · intro h
    induction l with
    | nil => simp [pairKeyLookup] at h
    | cons p l ih =>
      obtain ⟨⟨a', b'⟩, v'⟩ := p
      simp only [pairKeyLookup] at h
      by_cases hk : a' = a ∧ b' = b
      · rw [if_pos hk] at h
        obtain ⟨rfl, rfl⟩ := hk
        cases h
        exact .here
      · rw [if_neg hk] at h
        by_cases ha : a = a'
        · subst ha
          exact .nextB (fun hb => hk ⟨rfl, hb.symm⟩) (ih h)
        · exact .nextA ha (ih h)

theorem pairKeyLookup_isSome_of_mem {v : Type} {k : EntityUID} {x : v} {l : List (EntityUID × v)}
    (h : (k, x) ∈ l) : (pairKeyLookup k.ty k.eid l).isSome := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    simp only [pairKeyLookup]
    split
    · rfl
    · rcases List.mem_cons.mp h with h | h
      · subst h; simp_all
      · exact ih h

theorem mem_of_pairKeyLookup {v : Type} {a : EntityType} {b : String} {x : v}
    {l : List (EntityUID × v)} (h : pairKeyLookup a b l = some x) : (⟨a, b⟩, x) ∈ l := by
  induction l with
  | nil => simp [pairKeyLookup] at h
  | cons p l ih =>
    obtain ⟨⟨a', b'⟩, v'⟩ := p
    simp only [pairKeyLookup] at h
    split at h
    next hk =>
      obtain ⟨rfl, rfl⟩ := hk
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem exists_mapContains_iff {α β : Type} {k : α} {l : List (α × β)} :
    (∃ v, MapContains k v (.mk l)) ↔ ∃ p ∈ l, p.1 = k := by
  simp only [mapContains_iff_mem]
  exact ⟨fun ⟨v, h⟩ => ⟨_, h, rfl⟩, fun ⟨⟨k', v⟩, h, hk⟩ => ⟨v, by simp only at hk; subst hk; exact h⟩⟩

theorem validEntityType_iff {ety : EntityType} {ets : List (EntityType × EntitySchemaEntry)}
    {acts : List (EntityUID × ActionSchemaEntry)} :
    ValidEntityType ety (.mk ets) (.mk acts) ↔ (∃ p ∈ ets, p.1 = ety) ∨ (∃ p ∈ acts, p.1.ty = ety) := by
  constructor
  · intro h
    match h with
    | .inSchema _ entry _ _ h => exact .inl (exists_mapContains_iff.mp ⟨entry, h⟩)
    | .isAction _ _ _ _ _ h => exact .inr ⟨_, mem_of_pairKeyLookup (mapContainsPairKey_iff.mp h), rfl⟩
  · rintro (h | ⟨⟨k, x⟩, h, rfl⟩)
    · obtain ⟨v, hv⟩ := exists_mapContains_iff.mpr h
      exact .inSchema _ v _ _ hv
    · have := pairKeyLookup_isSome_of_mem h
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp this
      exact .isAction _ k.eid e _ _ (mapContainsPairKey_iff.mpr he)

instance {ety : EntityType} {ets : EntitySchema} {acts : ActionSchema} :
    Decidable (ValidEntityType ety ets acts) :=
  match ets, acts with
  | .mk _, .mk _ => decidable_of_iff _ validEntityType_iff.symm

/-- `eid` is a member of an enumerated entity type's entry. -/
def enumHas (eid : String) : EntitySchemaEntry → Bool
  | .enum (.mk eids) => eids.contains eid
  | .standard _ => false

theorem validEntityUID_mk_iff {ety : EntityType} {eid : String}
    {ets : List (EntityType × EntitySchemaEntry)} {acts : List (EntityUID × ActionSchemaEntry)} :
    ValidEntityUID ety eid (.mk ets) (.mk acts) ↔
      (∃ p ∈ ets, p.1 = ety ∧ p.2.isStandard = true) ∨ (∃ p ∈ ets, p.1 = ety ∧ enumHas eid p.2 = true) ∨
        (pairKeyLookup ety eid acts).isSome := by
  constructor
  · intro h
    match h with
    | .standard _ _ _ _ _ h => exact .inl ⟨_, mapContains_iff_mem.mp h, rfl, rfl⟩
    | .enum _ _ (.mk l) _ _ h hs =>
      refine .inr (.inl ⟨_, mapContains_iff_mem.mp h, rfl, ?_⟩)
      simp only [enumHas, List.contains_iff_mem]
      exact setContains_mk_iff_mem.mp hs
    | .action _ _ _ _ _ h => exact .inr (.inr (by rw [mapContainsPairKey_iff.mp h]; rfl))
  · rintro (⟨⟨k, e⟩, h, rfl, hs⟩ | ⟨⟨k, e⟩, h, rfl, he⟩ | h)
    · cases e with
      | standard entry => exact .standard _ _ entry _ _ (mapContains_iff_mem.mpr h)
      | enum _ => simp [EntitySchemaEntry.isStandard] at hs
    · cases e with
      | standard _ => simp [enumHas] at he
      | enum eids =>
        obtain ⟨l⟩ := eids
        simp only [enumHas, List.contains_iff_mem] at he
        exact .enum _ _ _ _ _ (mapContains_iff_mem.mpr h) (setContains_mk_iff_mem.mpr he)
    · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
      exact .action _ _ _ _ e (mapContainsPairKey_iff.mpr he)

instance {ety : EntityType} {eid : String} {ets : EntitySchema} {acts : ActionSchema} :
    Decidable (ValidEntityUID ety eid ets acts) :=
  match ets, acts with
  | .mk _, .mk _ => decidable_of_iff _ validEntityUID_mk_iff.symm

/-- The ancestors an action entry lists. -/
def ancestorList (e : ActionSchemaEntry) : List EntityUID :=
  match e.ancestors with
  | .mk l => l

theorem setContains_ancestors_iff {u : EntityUID} {e : ActionSchemaEntry} :
    SetContains u e.ancestors ↔ u ∈ ancestorList e := by
  unfold ancestorList
  split
  next l h =>
    rw [h]
    exact setContains_mk_iff_mem

theorem actionDescendentOf_iff {u₁ u₂ : EntityUID} {acts : List (EntityUID × ActionSchemaEntry)} :
    ActionDescendentOf (.mk acts) u₁ u₂ ↔
      (u₁ = u₂ ∧ ∃ p ∈ acts, p.1 = u₁) ∨ (∃ p ∈ acts, p.1 = u₁ ∧ u₂ ∈ ancestorList p.2) := by
  constructor
  · intro h
    match h with
    | .refl _ _ _ h => exact .inl ⟨rfl, _, mapContains_iff_mem.mp h, rfl⟩
    | .ancestor _ _ _ _ h hs => exact .inr ⟨_, mapContains_iff_mem.mp h, rfl, setContains_ancestors_iff.mp hs⟩
  · rintro (⟨rfl, ⟨k, e⟩, h, rfl⟩ | ⟨⟨k, e⟩, h, rfl, hs⟩)
    · exact .refl _ _ e (mapContains_iff_mem.mpr h)
    · exact .ancestor _ _ _ e (mapContains_iff_mem.mpr h) (setContains_ancestors_iff.mpr hs)

instance {acts : ActionSchema} {u₁ u₂ : EntityUID} : Decidable (ActionDescendentOf acts u₁ u₂) :=
  match acts with
  | .mk _ => decidable_of_iff _ actionDescendentOf_iff.symm

theorem notActionDescendentOf_iff {u₁ u₂ : EntityUID} {acts : List (EntityUID × ActionSchemaEntry)} :
    NotActionDescendentOf (.mk acts) u₁ u₂ ↔
      u₁ ≠ u₂ ∧ ∃ p ∈ acts, p.1 = u₁ ∧ u₂ ∉ ancestorList p.2 := by
  constructor
  · intro h
    match h with
    | .diff _ _ _ _ hne h hs =>
      exact ⟨hne, _, mapContains_iff_mem.mp h, rfl, fun hm => hs (setContains_ancestors_iff.mpr hm)⟩
  · rintro ⟨hne, ⟨k, e⟩, h, rfl, hs⟩
    exact .diff _ _ _ e hne (mapContains_iff_mem.mpr h) (fun hm => hs (setContains_ancestors_iff.mp hm))

instance {acts : ActionSchema} {u₁ u₂ : EntityUID} : Decidable (NotActionDescendentOf acts u₁ u₂) :=
  match acts with
  | .mk _ => decidable_of_iff _ notActionDescendentOf_iff.symm

theorem isTargetOf_iff {b : Bool} {env : TypeEnv} {T : EntityType} :
    IsTargetOf b env T ↔ ValidEntityType T env.ets env.acts ∨ b = false := by
  constructor
  · intro h
    match h with
    | .strict _ _ _ h => exact .inl h
    | .lax _ _ => exact .inr rfl
  · rintro (h | rfl)
    · exact .strict _ _ _ h
    · exact .lax _ _

instance {b : Bool} {env : TypeEnv} {T : EntityType} : Decidable (IsTargetOf b env T) :=
  decidable_of_iff _ isTargetOf_iff.symm

theorem extHasIf_iff {b : Bool} {a : Attr} {as : List Attr} :
    ExtHasIf b a as ↔ extHasAttrsParsed a as = true ∨ b = false := by
  constructor
  · intro h
    match h with
    | .yes _ _ _ h => exact .inl h
    | .no _ _ => exact .inr rfl
  · rintro (h | rfl)
    · exact .yes _ _ _ h
    · exact .no _ _

instance {b : Bool} {a : Attr} {as : List Attr} : Decidable (ExtHasIf b a as) :=
  decidable_of_iff _ extHasIf_iff.symm

theorem primNeq_iff {p q : Prim} : PrimNeq p q ↔ p ≠ q := by
  constructor
  · intro h
    cases h <;> simp_all
  · intro h
    cases p <;> cases q <;> first
      | exact absurd rfl h
      | (constructor; intro he; exact h (by rw [he]))
      | constructor

instance {p q : Prim} : Decidable (PrimNeq p q) := decidable_of_iff _ primNeq_iff.symm

end Cedar.Validation.Relational
