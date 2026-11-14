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

import CedarGen.Relational.SchemaGen
import Specimen.Correctness.SureWalk
import Specimen.Correctness.Workers

/-! # Distribution facts about the derived schema generator

Proved of the derived code at `SGen`: the append producer and the action-ancestor picker succeed
surely when their sizes allow (`app_sok`, `pickA_sok`); an action after the first gets a parent with
probability at least one half (`pickA_nonempty`); in the `dense` mode a type with `n` before it gets
no parent with probability `(1/2)^n` (`pickA_empty`, `pickE_empty`), and in the `sparse` mode with
probability `1/(n+1)` (`pickOne_empty`, `pickOneAction_empty`). -/

namespace Cedar.Validation.Relational.SchemaGen.Prob

open Specimen.Correctness Specimen.Backtrack Cedar.Spec Basalt ENNReal

/-- The derived append producer for `AppendUID xs ys merged`, `merged` out. -/
noncomputable abbrev appendUIDGen : Nat → Nat → Nat → List EntityUID → List EntityUID → SGen (List EntityUID) :=
  worker% gen Schema.AppendUID [2]

/-- The derived picker for `PickClosedActionAncestors built ancestors`, `ancestors` out. -/
noncomputable abbrev pickActionAncestorsGen : Nat → Nat → Nat → List (EntityUID × List EntityUID) → SGen (List EntityUID) :=
  worker% gen Schema.PickClosedActionAncestors [1]

/-- The derived append producer for `AppendET xs ys merged` (entity types), `merged` out. -/
noncomputable abbrev appendETGen : Nat → Nat → Nat → List EntityType → List EntityType → SGen (List EntityType) :=
  worker% gen Schema.AppendET [2]

/-- The derived picker for `PickClosedAncestors built ancestors` (entity types), `ancestors` out. -/
noncomputable abbrev pickAncestorsGen : Nat → Nat → Nat → List (EntityType × List EntityType) → SGen (List EntityType) :=
  worker% gen Schema.PickClosedAncestors [1]

/-! ## Surely -/

theorem app_sok : ∀ (xs ys : List EntityUID) (fuel iS sz : Nat), xs.length ≤ sz → sz < fuel →
    sok (appendUIDGen fuel iS sz xs ys) = 1 := by
  intro xs
  induction xs with
  | nil =>
    intro ys fuel iS sz _ hf
    apply sok_eq_one_of_le
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [appendUIDGen, worker% gen Schema.AppendUID [2] eq_def]
    walk
    all_goals sure_close
  | cons x xs ih =>
    intro ys fuel iS sz hl hf
    apply sok_eq_one_of_le
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    have h := le_spec_of_sok (ih ys f iS s (by omega) (by omega))
    unfold appendUIDGen at h
    rw [appendUIDGen, worker% gen Schema.AppendUID [2] eq_def]
    walk [h]
    all_goals sure_close

theorem pickA_sok : ∀ (b : List (EntityUID × List EntityUID)) (fuel iS sz : Nat),
    b.length ≤ sz → sz < fuel → (∀ q ∈ b, q.2.length ≤ iS) → iS < 10000 →
    sok (pickActionAncestorsGen fuel iS sz b) = 1 := by
  intro b
  induction b with
  | nil =>
    intro fuel iS sz _ hf _ _
    apply sok_eq_one_of_le
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [pickActionAncestorsGen, worker% gen Schema.PickClosedActionAncestors [1] eq_def]
    walk
    all_goals sure_close
  | cons q b ih =>
    intro fuel iS sz hl hf hps hiS
    apply sok_eq_one_of_le
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    obtain ⟨p, pset⟩ := q
    have hb := le_spec_of_sok (ih f iS s (by omega) (by omega) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hiS)
    have ha := fun chosen => le_spec_of_sok (app_sok pset chosen (iS + 1) iS iS (hps _ List.mem_cons_self) (Nat.lt_succ_self _))
    unfold pickActionAncestorsGen at hb; unfold appendUIDGen at ha
    rw [pickActionAncestorsGen, worker% gen Schema.PickClosedActionAncestors [1] eq_def]
    unfold_gen_instances
    walk [hb, ha]
    all_goals sure_close

theorem appE_sok : ∀ (xs ys : List EntityType) (fuel iS sz : Nat), xs.length ≤ sz → sz < fuel →
    sok (appendETGen fuel iS sz xs ys) = 1 := by
  intro xs
  induction xs with
  | nil =>
    intro ys fuel iS sz _ hf
    apply sok_eq_one_of_le
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [appendETGen, worker% gen Schema.AppendET [2] eq_def]
    walk
    all_goals sure_close
  | cons x xs ih =>
    intro ys fuel iS sz hl hf
    apply sok_eq_one_of_le
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    have h := le_spec_of_sok (ih ys f iS s (by omega) (by omega))
    unfold appendETGen at h
    rw [appendETGen, worker% gen Schema.AppendET [2] eq_def]
    walk [h]
    all_goals sure_close

theorem pickE_sok : ∀ (b : List (EntityType × List EntityType)) (fuel iS sz : Nat),
    b.length ≤ sz → sz < fuel → (∀ q ∈ b, q.2.length ≤ iS) → iS < 10000 →
    sok (pickAncestorsGen fuel iS sz b) = 1 := by
  intro b
  induction b with
  | nil =>
    intro fuel iS sz _ hf _ _
    apply sok_eq_one_of_le
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [pickAncestorsGen, worker% gen Schema.PickClosedAncestors [1] eq_def]
    walk
    all_goals sure_close
  | cons q b ih =>
    intro fuel iS sz hl hf hps hiS
    apply sok_eq_one_of_le
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    obtain ⟨p, pset⟩ := q
    have hb := le_spec_of_sok (ih f iS s (by omega) (by omega) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hiS)
    have ha := fun chosen => le_spec_of_sok (appE_sok pset chosen (iS + 1) iS iS (hps _ List.mem_cons_self) (Nat.lt_succ_self _))
    unfold pickAncestorsGen at hb; unfold appendETGen at ha
    rw [pickAncestorsGen, worker% gen Schema.PickClosedAncestors [1] eq_def]
    unfold_gen_instances
    walk [hb, ha]
    all_goals sure_close

/-! ## An action after the first gets a parent with probability at least one half -/

theorem pickA_nonempty (q : EntityUID × List EntityUID) (b : List (EntityUID × List EntityUID))
    (fuel iS sz : Nat) (hl : b.length < sz) (hf : sz < fuel) (hps : ∀ q' ∈ q :: b, q'.2.length ≤ iS)
    (hiS : iS < 10000) :
    1 / 2 ≤ sprob (pickActionAncestorsGen fuel iS sz (q :: b)) {xs | xs ≠ []} := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
  obtain ⟨p, pset⟩ := q
  have hb := le_spec_of_sok (pickA_sok b f iS s (by omega) (by omega) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hiS)
  have ha := fun chosen => le_spec_of_sok (app_sok pset chosen (iS + 1) iS iS (hps _ List.mem_cons_self) (Nat.lt_succ_self _))
  unfold pickActionAncestorsGen at hb; unfold appendUIDGen at ha
  have hs : SuccOnly (succVal ({xs : List EntityUID | xs ≠ []}.indicator 1)) := by
    intro o ho; rcases o with _ | (e | a) <;> simp_all [succVal, IsFailure]
  change 1 / 2 ≤ SPMF.expectObs.spec (pickActionAncestorsGen (f + 1) iS (s + 1) ((p, pset) :: b))
    (succVal ({xs : List EntityUID | xs ≠ []}.indicator 1))
  rw [pickActionAncestorsGen, worker% gen Schema.PickClosedActionAncestors [1] eq_def]
  unfold_gen_instances
  walk [hb, ha]
  all_goals try sure_close
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, Bool.false_eq_true,
    optW, succVal, Set.indicator, Set.mem_ofPred_eq, ne_eq, reduceCtorEq, not_false_eq_true, Pi.one_apply,
    iInf_const, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, add_zero, zero_add, mul_zero, mul_one]
  -- the branch that picks `p` counts fully, the other at least nothing
  rw [show (1 : ℝ≥0∞) / 2 = 3 / (3 + 3) by
    rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num]
  exact ENNReal.div_le_div_right le_add_self _

/-! ## Exact: the probability of no parent -/

/-- Exactly: an action with `n` actions before it gets no parent with probability `(3/6)^n`. -/
theorem pickA_empty : ∀ (b : List (EntityUID × List EntityUID)) (fuel iS sz : Nat),
    b.length ≤ sz → sz < fuel → (∀ q ∈ b, q.2.length ≤ iS) → iS < 10000 →
    sprob (pickActionAncestorsGen fuel iS sz b) {[]} = ((3 : ENNReal) / ((3 + 3 : Nat) : ENNReal)) ^ b.length := by
  intro b
  induction b with
  | nil =>
    intro fuel iS sz _ hf _ _
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    change SPMF.expectObs.spec (pickActionAncestorsGen (f + 1) iS sz []) (succVal (({[]} : Set (List EntityUID)).indicator 1)) = _
    rw [pickActionAncestorsGen, worker% gen Schema.PickClosedActionAncestors [1] eq_def]
    apply le_antisymm
    · walk
      all_goals first | (sure_close; done) | (sok_close; done) | num_close
    · walk
      all_goals first | (sure_close; done) | num_close
  | cons q b ih =>
    intro fuel iS sz hl hf hps hiS
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    obtain ⟨p, pset⟩ := q
    have hps' : ∀ q ∈ b, q.2.length ≤ iS := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    have hok := pickA_sok b f iS s (by omega) (by omega) hps' hiS
    have hokA := fun chosen => app_sok pset chosen (iS + 1) iS iS (hps _ List.mem_cons_self) (Nat.lt_succ_self _)
    have he := ih f iS s (by omega) (by omega) hps' hiS
    change SPMF.expectObs.spec (pickActionAncestorsGen f iS s b) (succVal (({[]} : Set (List EntityUID)).indicator 1)) = _ at he
    have hsup := spec_le_sup (pickActionAncestorsGen f iS s b)
    have hsupA := fun chosen => spec_le_sup (appendUIDGen (iS + 1) iS iS pset chosen)
    unfold pickActionAncestorsGen at hok he hsup; unfold appendUIDGen at hokA hsupA
    change SPMF.expectObs.spec (pickActionAncestorsGen (f + 1) iS (s + 1) ((p, pset) :: b))
      (succVal (({[]} : Set (List EntityUID)).indicator 1)) = _
    rw [pickActionAncestorsGen, worker% gen Schema.PickClosedActionAncestors [1] eq_def]
    unfold_gen_instances
    simp only [bind_pure]
    apply le_antisymm
    · walk [he.le, hsup, hsupA]
      all_goals try (first | (sure_close; done) | (sok_close; done))
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, Bool.false_eq_true,
        Specimen.Correctness.optW, Specimen.Correctness.succVal, spec_refute_succVal, Set.indicator,
        Set.mem_singleton_iff, Pi.one_apply, reduceCtorEq, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero,
        add_zero, zero_add, mul_zero, mul_one, iSup_const,
        List.cons_ne_nil, ite_false, iSup_zero, ENNReal.iSup_zero, max_self, List.length_cons]
      refine le_of_eq ?_
      rw [pow_succ]
      simp only [ENNReal.div_eq_inv_mul]
      ring
    · have hlo := le_spec_of_sok hok
      have hloA := fun chosen => le_spec_of_sok (hokA chosen)
      walk [he.ge, hlo, hloA]
      all_goals try (first | (sure_close; done) | (sok_close; done))
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
        Specimen.Correctness.optW, Specimen.Correctness.succVal, spec_refute_succVal, Set.indicator,
        Set.mem_singleton_iff, Pi.one_apply, reduceCtorEq, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero,
        add_zero, zero_add, mul_zero, mul_one, List.length_cons]
      rw [pow_succ, show (3 / (3 + 3) : ℝ≥0∞) ^ b.length * (3 / (3 + 3)) =
        (3 * (3 / (3 + 3)) ^ b.length + 0) / (3 + 3) by simp only [ENNReal.div_eq_inv_mul, add_zero]; ring]
      gcongr
      exact zero_le

/-- Exactly: in the `dense` mode, an entity type with `n` standard types before it gets no parent
    with probability `(3/6)^n`. -/
theorem pickE_empty : ∀ (b : List (EntityType × List EntityType)) (fuel iS sz : Nat),
    b.length ≤ sz → sz < fuel → (∀ q ∈ b, q.2.length ≤ iS) → iS < 10000 →
    sprob (pickAncestorsGen fuel iS sz b) {[]} = ((3 : ENNReal) / ((3 + 3 : Nat) : ENNReal)) ^ b.length := by
  intro b
  induction b with
  | nil =>
    intro fuel iS sz _ hf _ _
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    change SPMF.expectObs.spec (pickAncestorsGen (f + 1) iS sz []) (succVal (({[]} : Set (List EntityType)).indicator 1)) = _
    rw [pickAncestorsGen, worker% gen Schema.PickClosedAncestors [1] eq_def]
    apply le_antisymm
    · walk
      all_goals first | (sure_close; done) | (sok_close; done) | num_close
    · walk
      all_goals first | (sure_close; done) | num_close
  | cons q b ih =>
    intro fuel iS sz hl hf hps hiS
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    obtain ⟨p, pset⟩ := q
    have hps' : ∀ q ∈ b, q.2.length ≤ iS := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    have hok := pickE_sok b f iS s (by omega) (by omega) hps' hiS
    have hokA := fun chosen => appE_sok pset chosen (iS + 1) iS iS (hps _ List.mem_cons_self) (Nat.lt_succ_self _)
    have he := ih f iS s (by omega) (by omega) hps' hiS
    change SPMF.expectObs.spec (pickAncestorsGen f iS s b) (succVal (({[]} : Set (List EntityType)).indicator 1)) = _ at he
    have hsup := spec_le_sup (pickAncestorsGen f iS s b)
    have hsupA := fun chosen => spec_le_sup (appendETGen (iS + 1) iS iS pset chosen)
    unfold pickAncestorsGen at hok he hsup; unfold appendETGen at hokA hsupA
    change SPMF.expectObs.spec (pickAncestorsGen (f + 1) iS (s + 1) ((p, pset) :: b))
      (succVal (({[]} : Set (List EntityType)).indicator 1)) = _
    rw [pickAncestorsGen, worker% gen Schema.PickClosedAncestors [1] eq_def]
    unfold_gen_instances
    simp only [bind_pure]
    apply le_antisymm
    · walk [he.le, hsup, hsupA]
      all_goals try (first | (sure_close; done) | (sok_close; done))
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, Bool.false_eq_true,
        Specimen.Correctness.optW, Specimen.Correctness.succVal, spec_refute_succVal, Set.indicator,
        Set.mem_singleton_iff, Pi.one_apply, reduceCtorEq, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero,
        add_zero, zero_add, mul_zero, mul_one, iSup_const,
        List.cons_ne_nil, ite_false, iSup_zero, ENNReal.iSup_zero, max_self, List.length_cons]
      refine le_of_eq ?_
      rw [pow_succ]
      simp only [ENNReal.div_eq_inv_mul]
      ring
    · have hlo := le_spec_of_sok hok
      have hloA := fun chosen => le_spec_of_sok (hokA chosen)
      walk [he.ge, hlo, hloA]
      all_goals try (first | (sure_close; done) | (sok_close; done))
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
        Specimen.Correctness.optW, Specimen.Correctness.succVal, spec_refute_succVal, Set.indicator,
        Set.mem_singleton_iff, Pi.one_apply, reduceCtorEq, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero,
        add_zero, zero_add, mul_zero, mul_one, List.length_cons]
      rw [pow_succ, show (3 / (3 + 3) : ℝ≥0∞) ^ b.length * (3 / (3 + 3)) =
        (3 * (3 / (3 + 3)) ^ b.length + 0) / (3 + 3) by simp only [ENNReal.div_eq_inv_mul, add_zero]; ring]
      gcongr
      exact zero_le

/-! ## Exact: the `sparse` mode -/

theorem pickOne_empty (built : List (EntityType × List EntityType)) (sz iS : Nat) :
    sprob (BacktrackGenFor.gen (P := fun ancestors => PickOneAncestor built ancestors)
      (G := SGen) sz iS) {[]} = 1 / ((built.length + 1 : Nat) : ENNReal) := by
  change SPMF.expectObs.spec (BacktrackGenFor.gen (P := fun ancestors => PickOneAncestor built ancestors)
      (G := SGen) sz iS) (succVal (({[]} : Set (List EntityType)).indicator 1)) = _
  simp only [BacktrackGenFor.gen]
  apply le_antisymm
  · walk
    all_goals try (sure_close; done)
    simp only [Specimen.Correctness.succVal, Set.indicator, Set.mem_singleton_iff, Pi.one_apply, Nat.sub_zero]
    -- only the draw `0`, no parent, gives `[]`
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp only [hi, ↓reduceIte]; split <;> simp
    · simp
  · walk
    all_goals try (sure_close; done)
    simp only [Specimen.Correctness.succVal, Set.indicator, Set.mem_singleton_iff, Pi.one_apply, Nat.sub_zero]
    -- only the draw `0`, no parent, gives `[]`
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp only [hi, ↓reduceIte]; split <;> simp
    · simp

theorem pickOneAction_empty (built : List (EntityUID × List EntityUID)) (sz iS : Nat) :
    sprob (BacktrackGenFor.gen (P := fun ancestors => PickOneActionAncestor built ancestors)
      (G := SGen) sz iS) {[]} = 1 / ((built.length + 1 : Nat) : ENNReal) := by
  change SPMF.expectObs.spec (BacktrackGenFor.gen (P := fun ancestors => PickOneActionAncestor built ancestors)
      (G := SGen) sz iS) (succVal (({[]} : Set (List EntityUID)).indicator 1)) = _
  simp only [BacktrackGenFor.gen]
  apply le_antisymm
  · walk
    all_goals try (sure_close; done)
    simp only [Specimen.Correctness.succVal, Set.indicator, Set.mem_singleton_iff, Pi.one_apply, Nat.sub_zero]
    -- only the draw `0`, no parent, gives `[]`
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp only [hi, ↓reduceIte]; split <;> simp
    · simp
  · walk
    all_goals try (sure_close; done)
    simp only [Specimen.Correctness.succVal, Set.indicator, Set.mem_singleton_iff, Pi.one_apply, Nat.sub_zero]
    -- only the draw `0`, no parent, gives `[]`
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp only [hi, ↓reduceIte]; split <;> simp
    · simp

end Cedar.Validation.Relational.SchemaGen.Prob
