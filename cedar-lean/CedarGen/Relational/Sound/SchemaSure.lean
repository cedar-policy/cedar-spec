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

import CedarGen.Relational.Sound.RequestVariety
import CedarGen.Relational.Sound.SchemaGenSound
import CedarGen.Relational.SchemaGenProb
import Specimen.Enum.Laws.BacktrackWithWeight
import Specimen.Correctness.Workers
import Specimen.Correctness.SureWalk

/-! # The schema generator never fails

Proved of the derived code at `SGen`. Every derived worker the schema generator runs, and every
hand-written instance and leaf it draws from, loses no mass (`Tot`: it succeeds or fails, surely);
then a search succeeds surely where one of its branches does (`sok_backtrack_of_sure`). The entity
list's `nil` always succeeds, so the entity schema never fails (`sok_we1`); the request's action,
placed first from the full name pool with no actions before it, always succeeds, so the actions never
fail once the budget allows one environment (`sok_wa_top`). Hence `genTypeEnvB_instance_sok`. -/

namespace Cedar.Validation.Relational.SchemaGen.Sure
open Specimen.Correctness Specimen.Backtrack Cedar.Spec
open Specimen.Correctness Basalt ENNReal

variable {A B : Type}

/-! ## Leaves -/

theorem sok_choose (lo hi : Nat) (h : lo ≤ hi) : sok (RandomChoice.choose lo hi h : SGen _) = 1 := by
  rw [sok, sexpect_choose, SPMF.expect_one]; exact SPMF.mass_choose _ _ _

theorem sok_elements {α : Type} (xs : List α) (h : xs ≠ []) : sok (elements xs h : SGen α) = 1 := by
  unfold elements
  exact sok_bind_one (sok_map_one _ (sok_choose _ _ _)) fun _ => sok_pure _

theorem sok_oneOf {α : Type} (gs : List (Unit → SGen α)) (h : gs ≠ []) (hall : ∀ g ∈ gs, sok (g ()) = 1) :
    sok (oneOf gs h : SGen α) = 1 := by
  unfold oneOf
  exact sok_bind_one (sok_choose _ _ _) fun i => hall _ (List.getElem_mem _)

theorem sok_arbString (n : Nat) : sok (ArbitrarySized.arbitrarySized n : SGen String) = 1 := by
  refine sok_frequency _ fun p hp _ => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact sok_elements _ (by simp [namePool])
  · exact sok_bind_one (sok_chooseNat _ _ _) fun _ =>
      sok_bind_one (sok_vectorOf (sok_bind_one (sok_chooseNat _ _ _) fun _ => sok_pure _) _) fun _ => sok_pure _
  · refine sok_bind_one (sok_chooseNat _ _ _) fun _ =>
      sok_bind_one (sok_vectorOf (sok_frequency _ fun p hp _ => ?_) _) fun _ => sok_pure _
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> exact sok_bind_one (sok_chooseNat _ _ _) fun _ => sok_pure _

theorem sok_arbListString (n : Nat) : sok (ArbitrarySized.arbitrarySized n : SGen (List String)) = 1 :=
  sok_bind_one (sok_chooseNat _ _ _) fun _ => sok_vectorOf (sok_arbString n) _

theorem sok_arbName (n : Nat) : sok (ArbitrarySized.arbitrarySized n : SGen Name) = 1 := by
  refine sok_bind_one (sok_arbString n) fun _ => sok_bind_one (sok_frequency _ fun p hp _ => ?_) fun _ => sok_pure _
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact sok_pure _
  · exact sok_arbListString n

theorem sok_arbMode (n : Nat) : sok (ArbitrarySized.arbitrarySized n : SGen HierMode) = 1 := by
  cases n <;> refine sok_oneOf _ ?_ ?_ <;> simp [sok_pure]


/-! ## Hand-written instances -/

theorem tot_defined (ets : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun et => Cedar.Validation.Relational.Schema.DefinedEntityType ets et) (G := SGen) s l) := by
  dsimp only [BacktrackGenFor.gen]
  tot_walk []

theorem sok_pickOneAction (built : List (EntityUID × List EntityUID)) (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun a => PickOneActionAncestor built a) (G := SGen) s l) = 1 := by
  refine sok_bind_one_of_support (sok_chooseNat _ _ _) fun i hi => ?_
  have := (chooseNat_range hi).2
  split
  · exact sok_pure _
  · rw [List.getElem?_eq_getElem (by omega)]
    exact sok_pure _

theorem sok_pickOneE (built : List (EntityType × List EntityType)) (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun a => PickOneAncestor built a) (G := SGen) s l) = 1 := by
  refine sok_bind_one_of_support (sok_chooseNat _ _ _) fun i hi => ?_
  have := (chooseNat_range hi).2
  split
  · exact sok_pure _
  · rw [List.getElem?_eq_getElem (by omega)]
    exact sok_pure _

theorem sok_attrAbove (b : Attr) (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun a => b < a) (G := SGen) s l) = 1 := by
  refine sok_frequency _ fun p hp _ => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact sok_bind_one (sok_chooseNat _ _ _) fun _ => sok_pure _
  · refine sok_bind_one ?_ fun _ => sok_pure _
    refine sok_bind_one (sok_chooseNat _ _ _) fun _ =>
      sok_bind_one (sok_vectorOf (sok_frequency _ fun p hp _ => ?_) _) fun _ => sok_pure _
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> exact sok_bind_one (sok_chooseNat _ _ _) fun _ => sok_pure _

/-! ## Derived workers -/

noncomputable abbrev notInGen : ℕ → ℕ → ℕ → List EntityType → SGen EntityType :=
  worker% gen Schema.NotInET [0]
noncomputable abbrev keyAboveGen : ℕ → ℕ → ℕ → Option Attr → SGen Attr :=
  worker% gen Schema.KeyAbove [1]
noncomputable abbrev attrsGen : ℕ → ℕ → ℕ → Option Attr → List EntityType → SGen (List (Attr × Cedar.Validation.QualifiedType)) :=
  worker% gen Schema.WfAttrs [2]
noncomputable abbrev cedarTypeGen : ℕ → ℕ → ℕ → List EntityType → SGen Cedar.Validation.CedarType :=
  worker% gen Schema.WfCedarType [1]
noncomputable abbrev tagsGen : ℕ → ℕ → ℕ → List EntityType → SGen (Option Cedar.Validation.CedarType) :=
  worker% gen Schema.WfTags [1]

theorem tot_notIn : ∀ (fuel iS sz : Nat) (names : List EntityType), Tot (notInGen fuel iS sz names)
  | 0, _, _, _ => by rw [notInGen, (worker% gen Schema.NotInET [0] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, names => by
    rw [notInGen, (worker% gen Schema.NotInET [0] eq_def)]
    rcases sz with _ | s <;> rcases names with _ | ⟨x, rest⟩ <;>
      tot_search [tot_fact% (tot_notIn f), sok_fact% sok_arbName]

theorem sok_notIn_nil (f iS sz : Nat) : sok (notInGen (f + 1) iS sz []) = 1 := by
  rw [notInGen, (worker% gen Schema.NotInET [0] eq_def)]
  rcases sz with _ | s <;> sok_walk [sok_fact% sok_arbName]

theorem sok_keyAb (f iS sz : Nat) (a : Option Attr) : sok (keyAboveGen (f + 1) iS sz a) = 1 := by
  rw [keyAboveGen, (worker% gen Schema.KeyAbove [1] eq_def)]
  rcases a with _ | b <;> rcases sz with _ | s <;> sok_walk [sok_fact% sok_arbString, sok_fact% sok_attrAbove]

theorem tot_keyAb : ∀ (fuel iS sz : Nat) (a : Option Attr), Tot (keyAboveGen fuel iS sz a)
  | 0, _, _, _ => by rw [keyAboveGen, (worker% gen Schema.KeyAbove [1] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, a => tot_of_sok (sok_keyAb f iS sz a)

theorem tot_attrs_cty : ∀ (fuel : Nat), (∀ iS sz a ets, Tot (attrsGen fuel iS sz a ets)) ∧ (∀ iS sz ets, Tot (cedarTypeGen fuel iS sz ets))
  | 0 => ⟨fun _ _ _ _ => by rw [attrsGen, (worker% gen Schema.WfAttrs [2] eq_def)]; exact tot_outOfFuel,
          fun _ _ _ => by rw [cedarTypeGen, (worker% gen Schema.WfCedarType [1] eq_def)]; exact tot_outOfFuel⟩
  | f + 1 => by
    obtain ⟨ihA, ihC⟩ := tot_attrs_cty f
    refine ⟨fun iS sz a ets => ?_, fun iS sz ets => ?_⟩
    · rw [attrsGen, (worker% gen Schema.WfAttrs [2] eq_def)]
      rcases sz with _ | s <;> tot_search [tot_fact% tot_keyAb, tot_fact% ihA, tot_fact% ihC]
    · rw [cedarTypeGen, (worker% gen Schema.WfCedarType [1] eq_def)]
      rcases sz with _ | s <;> tot_search [tot_fact% tot_defined, tot_fact% ihA, tot_fact% ihC]

theorem tot_attrs (fuel iS sz : Nat) (a : Option Attr) (ets : List EntityType) : Tot (attrsGen fuel iS sz a ets) :=
  (tot_attrs_cty fuel).1 iS sz a ets

theorem tot_cty (fuel iS sz : Nat) (ets : List EntityType) : Tot (cedarTypeGen fuel iS sz ets) :=
  (tot_attrs_cty fuel).2 iS sz ets

theorem sok_attrs (f iS sz : Nat) (a : Option Attr) (ets : List EntityType) : sok (attrsGen (f + 1) iS sz a ets) = 1 := by
  rw [attrsGen, (worker% gen Schema.WfAttrs [2] eq_def)]
  rcases sz with _ | s <;> sok_search [tot_fact% tot_keyAb, tot_fact% tot_attrs, tot_fact% tot_cty]

theorem sok_tags (f iS sz : Nat) (ets : List EntityType) : sok (tagsGen (f + 1) iS sz ets) = 1 := by
  rw [tagsGen, (worker% gen Schema.WfTags [1] eq_def)]
  rcases sz with _ | s <;> sok_search [tot_fact% tot_cty]


theorem tot_gen_defined (ets : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun et => Cedar.Validation.Relational.Schema.DefinedEntityType ets et) (G := SGen) s l) :=
  tot_defined ets s l

theorem tot_gen_attrs (a : Option Attr) (ets : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.WfAttrs a ets x) (G := SGen) s l) :=
  tot_attrs _ _ _ _ _

theorem sok_gen_attrs (a : Option Attr) (ets : List EntityType) (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.WfAttrs a ets x) (G := SGen) s l) = 1 :=
  sok_attrs _ _ _ _ _

theorem sok_gen_tags (ets : List EntityType) (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.WfTags ets x) (G := SGen) s l) = 1 :=
  sok_tags _ _ _ _

theorem tot_gen_tags (ets : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.WfTags ets x) (G := SGen) s l) :=
  tot_of_sok (sok_gen_tags _ _ _)

theorem tot_gen_notIn (ets : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.NotInET x ets) (G := SGen) s l) :=
  tot_notIn _ _ _ _

theorem sok_gen_notIn_nil (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.NotInET x []) (G := SGen) s l) = 1 :=
  sok_notIn_nil _ _ _

noncomputable abbrev selectRemoveGen : ℕ → ℕ → ℕ → (α : Type) → List α → SGen (α × List α) :=
  worker% gen Schema.SelectRemove [2, 3]
noncomputable abbrev appendETGen : ℕ → ℕ → ℕ → List EntityType → List EntityType → SGen (List EntityType) :=
  worker% gen Schema.AppendET [2]
noncomputable abbrev appendUIDGen : ℕ → ℕ → ℕ → List EntityUID → List EntityUID → SGen (List EntityUID) :=
  worker% gen Schema.AppendUID [2]
noncomputable abbrev pickAncestorsGen : ℕ → ℕ → ℕ → List (EntityType × List EntityType) → SGen (List EntityType) :=
  worker% gen Schema.PickClosedAncestors [1]
noncomputable abbrev pickActionAncestorsGen : ℕ → ℕ → ℕ → List (EntityUID × List EntityUID) → SGen (List EntityUID) :=
  worker% gen Schema.PickClosedActionAncestors [1]

theorem tot_selRem : ∀ (fuel iS sz : Nat) (α : Type) (xs : List α), Tot (selectRemoveGen fuel iS sz α xs)
  | 0, _, _, _, _ => by rw [selectRemoveGen, (worker% gen Schema.SelectRemove [2, 3] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, α, xs => by
    rw [selectRemoveGen, (worker% gen Schema.SelectRemove [2, 3] eq_def)]
    rcases sz with _ | s <;> rcases xs with _ | ⟨x, xs⟩ <;> tot_search [tot_fact% (tot_selRem f)]

theorem sok_selRem (f iS sz : Nat) (α : Type) (xs : List α) (h : xs ≠ []) : sok (selectRemoveGen (f + 1) iS sz α xs) = 1 := by
  rw [selectRemoveGen, (worker% gen Schema.SelectRemove [2, 3] eq_def)]
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  rcases sz with _ | s <;> sok_search [tot_fact% tot_selRem]

theorem tot_appE : ∀ (fuel iS sz : Nat) (xs ys : List EntityType), Tot (appendETGen fuel iS sz xs ys)
  | 0, _, _, _, _ => by rw [appendETGen, (worker% gen Schema.AppendET [2] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, xs, ys => by
    rw [appendETGen, (worker% gen Schema.AppendET [2] eq_def)]
    rcases sz with _ | s <;> rcases xs with _ | ⟨x, xs⟩ <;> tot_search [tot_fact% (tot_appE f)]

theorem tot_appU : ∀ (fuel iS sz : Nat) (xs ys : List EntityUID), Tot (appendUIDGen fuel iS sz xs ys)
  | 0, _, _, _, _ => by rw [appendUIDGen, (worker% gen Schema.AppendUID [2] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, xs, ys => by
    rw [appendUIDGen, (worker% gen Schema.AppendUID [2] eq_def)]
    rcases sz with _ | s <;> rcases xs with _ | ⟨x, xs⟩ <;> tot_search [tot_fact% (tot_appU f)]

theorem tot_gen_appE (xs ys : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun m => Cedar.Validation.Relational.Schema.AppendET xs ys m) (G := SGen) s l) :=
  tot_appE _ _ _ _ _

theorem tot_gen_appU (xs ys : List EntityUID) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun m => Cedar.Validation.Relational.Schema.AppendUID xs ys m) (G := SGen) s l) :=
  tot_appU _ _ _ _ _

theorem tot_pickE : ∀ (fuel iS sz : Nat) (b : List (EntityType × List EntityType)), Tot (pickAncestorsGen fuel iS sz b)
  | 0, _, _, _ => by rw [pickAncestorsGen, (worker% gen Schema.PickClosedAncestors [1] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, b => by
    rw [pickAncestorsGen, (worker% gen Schema.PickClosedAncestors [1] eq_def)]
    rcases sz with _ | s <;> rcases b with _ | ⟨⟨p, ps⟩, b⟩ <;> tot_search [tot_fact% (tot_pickE f), tot_fact% tot_gen_appE]

theorem tot_pickA : ∀ (fuel iS sz : Nat) (b : List (EntityUID × List EntityUID)), Tot (pickActionAncestorsGen fuel iS sz b)
  | 0, _, _, _ => by rw [pickActionAncestorsGen, (worker% gen Schema.PickClosedActionAncestors [1] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, b => by
    rw [pickActionAncestorsGen, (worker% gen Schema.PickClosedActionAncestors [1] eq_def)]
    rcases sz with _ | s <;> rcases b with _ | ⟨⟨p, ps⟩, b⟩ <;> tot_search [tot_fact% (tot_pickA f), tot_fact% tot_gen_appU]

theorem sok_pickA_nil (f iS sz : Nat) : sok (pickActionAncestorsGen (f + 1) iS sz []) = 1 := by
  rw [pickActionAncestorsGen, (worker% gen Schema.PickClosedActionAncestors [1] eq_def)]
  cases sz <;> sok_walk []

theorem tot_gen_pickE (b : List (EntityType × List EntityType)) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun c => Cedar.Validation.Relational.Schema.PickClosedAncestors b c) (G := SGen) s l) :=
  tot_pickE _ _ _ _

theorem tot_gen_pickA (b : List (EntityUID × List EntityUID)) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun c => Cedar.Validation.Relational.Schema.PickClosedActionAncestors b c) (G := SGen) s l) :=
  tot_pickA _ _ _ _

theorem tot_gen_pickOneE (b : List (EntityType × List EntityType)) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun c => PickOneAncestor b c) (G := SGen) s l) :=
  tot_of_sok (sok_pickOneE _ _ _)

theorem tot_gen_pickOneA (b : List (EntityUID × List EntityUID)) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun c => PickOneActionAncestor b c) (G := SGen) s l) :=
  tot_of_sok (sok_pickOneAction _ _ _)


/-! ## The entity workers -/

noncomputable abbrev ancestorsGen : ℕ → ℕ → ℕ → HierMode → List (EntityType × List EntityType) → SGen (List EntityType) :=
  worker% gen SchemaGen.Ancestors [2]
noncomputable abbrev ancestorsModeGen : ℕ → ℕ → ℕ → List (EntityType × List EntityType) → SGen (HierMode × List EntityType) :=
  worker% gen SchemaGen.Ancestors [0, 2]
noncomputable abbrev entitiesGen : ℕ → ℕ → ℕ → HierMode → List (EntityType × List EntityType) → List EntityType → SGen (List EntityType × List (EntityType × Cedar.Validation.EntitySchemaEntry)) :=
  worker% gen SchemaGen.WfEntitiesGoR [3, 4]
noncomputable abbrev entitiesModeGen : ℕ → ℕ → ℕ → List (EntityType × List EntityType) → List EntityType → SGen (HierMode × List EntityType × List (EntityType × Cedar.Validation.EntitySchemaEntry)) :=
  worker% gen SchemaGen.WfEntitiesGoR [0, 3, 4]
noncomputable abbrev entities1Gen : ℕ → ℕ → ℕ → List (EntityType × List EntityType) → List EntityType → SGen (HierMode × List EntityType × List (EntityType × Cedar.Validation.EntitySchemaEntry)) :=
  worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4]

theorem tot_anc : ∀ (fuel iS sz : Nat) (r : HierMode) (b : List (EntityType × List EntityType)), Tot (ancestorsGen fuel iS sz r b)
  | 0, _, _, _, _ => by rw [ancestorsGen, (worker% gen SchemaGen.Ancestors [2] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, r, b => by
    rw [ancestorsGen, (worker% gen SchemaGen.Ancestors [2] eq_def)]
    rcases sz with _ | s <;> rcases r <;> tot_search [tot_fact% tot_gen_pickE, tot_fact% tot_gen_pickOneE]

theorem sok_anc02 (f iS sz : Nat) (b : List (EntityType × List EntityType)) : sok (ancestorsModeGen (f + 1) iS sz b) = 1 := by
  rw [ancestorsModeGen, (worker% gen SchemaGen.Ancestors [0, 2] eq_def)]
  rcases sz with _ | s <;> sok_search [tot_fact% tot_gen_pickE, tot_fact% tot_gen_pickOneE]

theorem tot_anc02 : ∀ (fuel iS sz : Nat) (b : List (EntityType × List EntityType)), Tot (ancestorsModeGen fuel iS sz b)
  | 0, _, _, _ => by rw [ancestorsModeGen, (worker% gen SchemaGen.Ancestors [0, 2] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, b => tot_of_sok (sok_anc02 f iS sz b)

theorem tot_listString (n : Nat) : Tot (ArbitrarySized.arbitrarySized n : SGen (List String)) :=
  tot_of_sok (sok_arbListString n)

theorem tot_mode (n : Nat) : Tot (ArbitrarySized.arbitrarySized n : SGen HierMode) :=
  tot_of_sok (sok_arbMode n)

theorem tot_we : ∀ (fuel iS sz : Nat) (r : HierMode) (b : List (EntityType × List EntityType)) (names : List EntityType),
    Tot (entitiesGen fuel iS sz r b names)
  | 0, _, _, _, _, _ => by rw [entitiesGen, (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, r, b, names => by
    rw [entitiesGen, (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_def)]
    rcases sz with _ | s <;> tot_search [tot_fact% (tot_we f), tot_fact% tot_notIn, tot_fact% tot_attrs, tot_fact% tot_gen_tags, tot_fact% tot_anc, tot_fact% tot_listString]

theorem sok_we (f iS sz : Nat) (r : HierMode) (b : List (EntityType × List EntityType)) (names : List EntityType) :
    sok (entitiesGen (f + 1) iS sz r b names) = 1 := by
  rw [entitiesGen, (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_def)]
  rcases sz with _ | s <;> sok_search [tot_fact% tot_we, tot_fact% tot_notIn, tot_fact% tot_attrs, tot_fact% tot_gen_tags, tot_fact% tot_anc, tot_fact% tot_listString]

theorem tot_we0 : ∀ (fuel iS sz : Nat) (b : List (EntityType × List EntityType)) (names : List EntityType),
    Tot (entitiesModeGen fuel iS sz b names)
  | 0, _, _, _, _ => by rw [entitiesModeGen, (worker% gen SchemaGen.WfEntitiesGoR [0, 3, 4] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, b, names => by
    rw [entitiesModeGen, (worker% gen SchemaGen.WfEntitiesGoR [0, 3, 4] eq_def)]
    rcases sz with _ | s <;> tot_search [tot_fact% (tot_we0 f), tot_fact% tot_we, tot_fact% tot_notIn, tot_fact% tot_attrs, tot_fact% tot_gen_tags, tot_fact% tot_anc02, tot_fact% tot_listString, tot_fact% tot_mode]

theorem sok_we0 (f iS sz : Nat) (b : List (EntityType × List EntityType)) (names : List EntityType) :
    sok (entitiesModeGen (f + 1) iS sz b names) = 1 := by
  rw [entitiesModeGen, (worker% gen SchemaGen.WfEntitiesGoR [0, 3, 4] eq_def)]
  rcases sz with _ | s <;> sok_search [tot_fact% tot_we0, tot_fact% tot_we, tot_fact% tot_notIn, tot_fact% tot_attrs, tot_fact% tot_gen_tags, tot_fact% tot_anc02, tot_fact% tot_listString, tot_fact% tot_mode] sure [sok_fact% sok_arbMode]

/-- **The entity schema never fails.** -/
theorem sok_we1 (f iS sz : Nat) : sok (entities1Gen (f + 1) iS sz [] []) = 1 := by
  rw [entities1Gen, (worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4] eq_def)]
  rcases sz with _ | s <;> sok_search [tot_fact% tot_we0, tot_fact% tot_we, tot_fact% tot_notIn, tot_fact% tot_attrs, tot_fact% tot_gen_tags, tot_fact% tot_anc02, tot_fact% tot_listString, tot_fact% tot_mode]
    sure [sok_fact% sok_notIn_nil, sok_fact% sok_attrs, sok_fact% sok_tags, sok_fact% sok_anc02, sok_fact% sok_we]


/-! ## The action workers -/

noncomputable abbrev principalTypesGen : ℕ → ℕ → ℕ → List EntityType → SGen (List EntityType) :=
  worker% gen Schema.WfPrincipalTypes [1]
noncomputable abbrev resourceTypesGen : ℕ → ℕ → ℕ → List EntityType → SGen (List EntityType) :=
  worker% gen Schema.WfResourceTypes [1]
noncomputable abbrev resourcesWithinGen : ℕ → ℕ → ℕ → List EntityType → ℕ → List EntityType → SGen (List EntityType) :=
  worker% gen SchemaGen.ResourcesWithin [3]
noncomputable abbrev actionAncestorsGen : ℕ → ℕ → ℕ → HierMode → List (EntityUID × List EntityUID) → SGen (List EntityUID) :=
  worker% gen SchemaGen.ActAncestors [2]
noncomputable abbrev actionsBudgetGen : ℕ → ℕ → ℕ → HierMode → List EntityType → List (EntityUID × List EntityUID) → List String → ℕ → SGen (List (EntityUID × Cedar.Validation.ActionSchemaEntry)) :=
  worker% gen SchemaGen.WfActionsGoB [5]
noncomputable abbrev actionsGen : ℕ → ℕ → ℕ → HierMode → List EntityType → List (EntityUID × List EntityUID) → List String → ℕ → SGen (List (EntityUID × Cedar.Validation.ActionSchemaEntry) × Cedar.Validation.RequestType) :=
  worker% gen SchemaGen.WfActionsGoR [5, 6]
noncomputable abbrev typeEnvGen : ℕ → ℕ → ℕ → ℕ → SGen (HierMode × Cedar.Validation.TypeEnv) :=
  worker% gen SchemaGen.GenTypeEnvB [0, 2]

theorem sok_gen_eqAct (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun x : EntityType => x = Cedar.Validation.Relational.Schema.actionEntityType) (G := SGen) s l) = 1 :=
  sok_pure _

theorem tot_gen_eqAct (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun x : EntityType => x = Cedar.Validation.Relational.Schema.actionEntityType) (G := SGen) s l) :=
  tot_pure _

theorem tot_wpt : ∀ (fuel iS sz : Nat) (ets : List EntityType), Tot (principalTypesGen fuel iS sz ets)
  | 0, _, _, _ => by rw [principalTypesGen, (worker% gen Schema.WfPrincipalTypes [1] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, ets => by
    rw [principalTypesGen, (worker% gen Schema.WfPrincipalTypes [1] eq_def)]
    rcases sz with _ | s <;> tot_search [tot_fact% (tot_wpt f), tot_fact% tot_gen_defined]

theorem tot_wrt : ∀ (fuel iS sz : Nat) (ets : List EntityType), Tot (resourceTypesGen fuel iS sz ets)
  | 0, _, _, _ => by rw [resourceTypesGen, (worker% gen Schema.WfResourceTypes [1] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, ets => by
    rw [resourceTypesGen, (worker% gen Schema.WfResourceTypes [1] eq_def)]
    rcases sz with _ | s <;> tot_search [tot_fact% (tot_wrt f), tot_fact% tot_gen_defined]

theorem tot_bt : ∀ (fuel iS sz : Nat) (ets : List EntityType) (b : Nat), Tot (Variety.boundedTypesGen fuel iS sz ets b)
  | 0, _, _, _, _ => by rw [Variety.boundedTypesGen, (worker% gen SchemaGen.BoundedTypes [2] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, ets, b => by
    rw [Variety.boundedTypesGen, (worker% gen SchemaGen.BoundedTypes [2] eq_def)]
    rcases sz with _ | s <;> rcases b with _ | b <;> tot_search [tot_fact% (tot_bt f), tot_fact% tot_gen_defined]

theorem tot_cb : ∀ (fuel iS sz : Nat) (ets : List EntityType) (b : Nat), Tot (Variety.containsBoundedGen fuel iS sz ets b)
  | 0, _, _, _, _ => by rw [Variety.containsBoundedGen, (worker% gen SchemaGen.ContainsBounded [2, 3] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, ets, b => by
    rw [Variety.containsBoundedGen, (worker% gen SchemaGen.ContainsBounded [2, 3] eq_def)]
    rcases sz with _ | s <;> rcases b with _ | b <;> tot_search [tot_fact% (tot_cb f), tot_fact% tot_bt, tot_fact% tot_gen_defined]

theorem tot_rw : ∀ (fuel iS sz : Nat) (ets : List EntityType) (b : Nat) (ps : List EntityType), Tot (resourcesWithinGen fuel iS sz ets b ps)
  | 0, _, _, _, _, _ => by rw [resourcesWithinGen, (worker% gen SchemaGen.ResourcesWithin [3] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, ets, b, ps => by
    rw [resourcesWithinGen, (worker% gen SchemaGen.ResourcesWithin [3] eq_def)]
    rcases sz with _ | s <;> rcases ps with _ | ⟨p, ps⟩ <;> tot_search [tot_fact% tot_wrt, tot_fact% tot_bt]

theorem tot_actAnc : ∀ (fuel iS sz : Nat) (r : HierMode) (b : List (EntityUID × List EntityUID)), Tot (actionAncestorsGen fuel iS sz r b)
  | 0, _, _, _, _ => by rw [actionAncestorsGen, (worker% gen SchemaGen.ActAncestors [2] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, r, b => by
    rw [actionAncestorsGen, (worker% gen SchemaGen.ActAncestors [2] eq_def)]
    rcases sz with _ | s <;> rcases r <;> tot_search [tot_fact% tot_gen_pickA, tot_fact% tot_gen_pickOneA]

/-- With no actions before it, an action's ancestors are drawn surely, in every mode. -/
theorem sok_actAnc_nil (f iS sz : Nat) (r : HierMode) : sok (actionAncestorsGen (f + 1) iS sz r []) = 1 := by
  rw [actionAncestorsGen, (worker% gen SchemaGen.ActAncestors [2] eq_def)]
  rcases sz with _ | s <;> rcases r <;> sok_walk [sok_fact% sok_pickA_nil, sok_fact% sok_pickOneAction]

theorem tot_wb : ∀ (fuel iS sz : Nat) (r : HierMode) (ets : List EntityType) (built : List (EntityUID × List EntityUID))
    (avail : List String) (b : Nat), Tot (actionsBudgetGen fuel iS sz r ets built avail b)
  | 0, _, _, _, _, _, _, _ => by rw [actionsBudgetGen, (worker% gen SchemaGen.WfActionsGoB [5] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, r, ets, built, avail, b => by
    rw [actionsBudgetGen, (worker% gen SchemaGen.WfActionsGoB [5] eq_def)]
    rcases sz with _ | s <;> tot_search [tot_fact% tot_gen_eqAct, tot_fact% (tot_wb f), tot_fact% tot_wpt, tot_fact% tot_attrs, tot_fact% tot_rw, tot_fact% tot_selRem, tot_fact% tot_actAnc]

theorem sok_wb (f iS sz : Nat) (r : HierMode) (ets : List EntityType) (built : List (EntityUID × List EntityUID))
    (avail : List String) (b : Nat) : sok (actionsBudgetGen (f + 1) iS sz r ets built avail b) = 1 := by
  rw [actionsBudgetGen, (worker% gen SchemaGen.WfActionsGoB [5] eq_def)]
  rcases sz with _ | s <;> sok_search [tot_fact% tot_gen_eqAct, tot_fact% tot_wb, tot_fact% tot_wpt, tot_fact% tot_attrs, tot_fact% tot_rw, tot_fact% tot_selRem, tot_fact% tot_actAnc]

theorem tot_wa : ∀ (fuel iS sz : Nat) (r : HierMode) (ets : List EntityType) (built : List (EntityUID × List EntityUID))
    (avail : List String) (b : Nat), Tot (actionsGen fuel iS sz r ets built avail b)
  | 0, _, _, _, _, _, _, _ => by rw [actionsGen, (worker% gen SchemaGen.WfActionsGoR [5, 6] eq_def)]; exact tot_outOfFuel
  | f + 1, iS, sz, r, ets, built, avail, b => by
    rw [actionsGen, (worker% gen SchemaGen.WfActionsGoR [5, 6] eq_def)]
    rcases sz with _ | s <;> tot_search [tot_fact% tot_gen_eqAct, tot_fact% (tot_wa f), tot_fact% tot_wb, tot_fact% tot_wpt, tot_fact% tot_attrs, tot_fact% tot_rw, tot_fact% tot_selRem, tot_fact% tot_actAnc, tot_fact% tot_cb]


/-! ## The whole generator -/

theorem wfEntitiesGoR_names_sub {r built names allNames rest}
    (h : WfEntitiesGoR r built names allNames rest) : ∀ x ∈ names, x ∈ allNames := by
  induction h with
  | nil => exact fun _ hx => hx
  | standard _ _ _ _ _ _ _ _ _ _ _ _ _ ih | enum _ _ _ _ _ _ _ _ ih =>
    exact fun x hx => ih x (List.mem_cons_of_mem _ hx)

theorem wfEntitiesGo1_names_ne_nil {r names entries}
    (h : WfEntitiesGo1 r [] [] names entries) : names ≠ [] := by
  cases h with
  | standard _ _ _ _ _ _ _ _ _ _ h | enum _ _ _ _ _ h =>
    exact List.ne_nil_of_mem (wfEntitiesGoR_names_sub h _ List.mem_cons_self)

/-- **The actions never fail** from no actions, a nonempty pool of names, some entity type and a budget
of at least one environment: the request's action is placed first surely, and every other try only
retries. -/
theorem sok_wa_top (f iS sz : Nat) (r : HierMode) (ets : List EntityType) (avail : List String) (b : Nat)
    (hets : ets ≠ []) (havail : avail ≠ []) (hb : 1 ≤ b) : sok (actionsGen (f + 1) iS sz r ets [] avail b) = 1 := by
  rw [actionsGen, (worker% gen SchemaGen.WfActionsGoR [5, 6] eq_def)]
  rcases sz with _ | s <;> apply sok_backtrack_of_sure
  -- every try loses no mass
  case htot | htot =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    all_goals ((repeat' apply And.intro) <;> tot_walk [tot_fact% tot_gen_eqAct, tot_fact% tot_wa, tot_fact% tot_wb, tot_fact% tot_wpt, tot_fact% tot_attrs, tot_fact% tot_rw, tot_fact% tot_selRem, tot_fact% tot_actAnc, tot_fact% tot_cb])
  -- the request's action, placed first from the full pool, surely
  case h | h =>
    refine ⟨_, List.mem_cons_self, by norm_num, ?_⟩
    refine sok_bind_one (sok_gen_eqAct _ _) fun _ => ?_
    refine sok_bind_one (sok_gen_eqAct _ _) fun _ => ?_
    refine sok_bind_one (sok_gen_attrs _ _ _ _) fun _ => ?_
    refine sok_bind_one_of_support (Variety.cb_sok iS (iS + 1) iS ets b hets hb (by omega)) fun x hp => ?_
    obtain ⟨p, ps⟩ := x
    have hcb := (worker% gen SchemaGen.ContainsBounded [2, 3] sound)
      (iS + 1) iS iS ets b (p, ps) hp
    have hlen := hcb.boundedTypes.length_le
    have hpos : 0 < ps.length := List.length_pos_iff.mpr hcb.definedEntityType.ne_nil
    refine sok_bind_one (Variety.cb_sok iS (iS + 1) iS ets _ hets (Nat.div_pos hlen hpos) (by omega)) fun _ => ?_
    refine sok_bind_one (sok_selRem iS iS iS String avail havail) fun _ => ?_
    refine sok_bind_one (sok_actAnc_nil _ _ _ _) fun _ => ?_
    exact sok_bind_one (sok_wb _ _ _ _ _ _ _ _) fun _ => sok_pure _

theorem sok_gt (s l budget : Nat) (hb : 1 ≤ budget) : sok (typeEnvGen (s + 1) l s budget) = 1 := by
  rw [typeEnvGen, (worker% gen SchemaGen.GenTypeEnvB [0, 2] eq_def)]
  rcases s with _ | s <;>
    refine sok_backtrack_one _ (by simp [sumWeights]) ?_ <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq] <;>
    refine sok_bind_one_of_support (sok_we1 l l l) fun ⟨r, names, entries⟩ => fun hp => ?_ <;>
    have hne := ((worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4] sound)
      (l + 1) l l [] [] _ hp) |> wfEntitiesGo1_names_ne_nil <;>
    exact sok_bind_one (sok_wa_top l l l r names Cedar.Validation.Relational.Schema.actionEidPool budget hne
      (by simp [Cedar.Validation.Relational.Schema.actionEidPool]) hb) fun _ => sok_pure _


theorem envCount_pos_of_wf {env : TypeEnv} (h : Cedar.Validation.Relational.Schema.WfTypeEnv env) :
    0 < env.schema.environments.length := by
  rw [environments_length]
  cases h with
  | mk _ _ _ _ _ _ hreq => exact hreq.envCount_pos

/-- **The schema generator, as its instance runs it, never fails when its budget allows one
request environment, and never succeeds otherwise.** Its action names are drawn without replacement
from the fixed pool `actionEidPool` (eleven names), but running out of names never makes it fail: the
search backtracks to placing the request's action earlier, and the first action, from the full pool,
is placed surely. -/
theorem genTypeEnvB_instance_sok (budget s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2) (G := SGen) s l) =
      if 1 ≤ budget then 1 else 0 := by
  split
  · exact sok_gt s l budget ‹_›
  · refine sok_eq_zero fun ⟨r, env⟩ h => ?_
    have := Sound.genTypeEnvB_instance_generated budget s l r env h
    have := envCount_pos_of_wf this.1
    omega

end Cedar.Validation.Relational.SchemaGen.Sure

#print axioms Cedar.Validation.Relational.SchemaGen.Sure.genTypeEnvB_instance_sok
