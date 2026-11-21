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

import CedarGen.Relational.InstanceComplete
import CedarGen.Relational.Sound.SchemaVariety

/-! # Two entity types are possible

At leaf size at least one, the schema generator produces a schema with two entity types with positive
probability (`genTypeEnvB_instance_two_types`), so `genTypeEnvB_instance_varied_length`'s condition
is not vacuous. The proof follows one run: the first entity type is an enum, and the rest of the list
starts with another, whose name the name generator draws different from the first (`produces_name_ne`);
every other draw on the way succeeds surely (`exists_produces_of_sok`). -/

namespace Cedar.Validation.Relational.SchemaGen.Sure
open Specimen.Correctness Specimen.Backtrack Cedar.Spec Basalt ENNReal

/-- What succeeds with positive probability can be produced. -/
theorem exists_produces_of_sok {A : Type} {g : SGen A} (h : sok g ≠ 0) : ∃ x, Produces g x := by
  by_contra hn
  exact h (sok_eq_zero fun x hx => hn ⟨x, hx⟩)

theorem produces_elements {α : Type} (xs : List α) (h : xs ≠ []) (i : Nat) (hi : i < xs.length) :
    Produces (elements xs h : SGen α) xs[i] := by
  unfold elements
  exact produces_bind_of (Cedar.Validation.Relational.produces_map_of
    (produces_choose 0 (xs.length - 1) (by omega) ⟨i, Nat.zero_le _, by omega⟩)) (produces_pure_iff.mpr rfl)

/-- A name from `namePool` with no path. -/
theorem produces_name_pool (n i : Nat) (hi : i < namePool.length) :
    Produces (ArbitrarySized.arbitrarySized n : SGen Name) ⟨namePool[i], []⟩ := by
  refine produces_bind_of (Cedar.Validation.Relational.produces_frequency_at 0 (by simp) (by simp)
    (produces_elements namePool (by simp [namePool]) i hi)) ?_
  exact produces_bind_of (Cedar.Validation.Relational.produces_frequency_at 0 (by simp) (by simp)
    (produces_pure_iff.mpr rfl)) (produces_pure_iff.mpr rfl)

/-- Any name has another the name generator can produce. -/
theorem produces_name_ne (n : Nat) (x : Name) :
    ∃ y, Produces (ArbitrarySized.arbitrarySized n : SGen Name) y ∧ y ≠ x := by
  by_cases hx : x = ⟨namePool[6], []⟩
  · exact ⟨_, produces_name_pool n 7 (by simp [namePool]), by subst hx; simp [namePool]⟩
  · exact ⟨_, produces_name_pool n 6 (by simp [namePool]), fun h => hx h.symm⟩


/-- A name other than `x`, at leaf size `k + 1`. -/
theorem produces_notIn_one (k : Nat) (x : EntityType) :
    ∃ y, Produces (notInGen (k + 2) (k + 1) (k + 1) [x]) y := by
  obtain ⟨y, hy, hne⟩ := produces_name_ne (k + 1) x
  refine ⟨y, ?_⟩
  rw [notInGen, (worker% gen Schema.NotInET [0] eq_def)]
  simp only [produces_backtrack_iff, List.filterMap, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.mem_nil_iff, or_false, exists_eq_left]
  refine ⟨by decide, produces_bind_of (a := y) ?_ ?_⟩
  · rw [(worker% gen Schema.NotInET [0] eq_def)]
    rcases k with _ | k <;> simp only [produces_backtrack_iff, List.filterMap, Bool.false_eq_true,
      ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_left] <;>
      exact ⟨by decide, produces_bind_of hy (produces_pure_iff.mpr rfl)⟩
  · simp [DecOpt.negOpt, DecOpt.decOpt, hne]

/-- At leaf size `k + 1`, after one entity type, the rest of the entity list can be nonempty. -/
theorem produces_entitiesMode_cons (k : Nat) (b : List (EntityType × List EntityType)) (x : EntityType) :
    ∃ out, Produces (entitiesModeGen (k + 2) (k + 1) (k + 1) b [x]) out ∧ out.2.2 ≠ [] := by
  obtain ⟨et, het⟩ := produces_notIn_one k x
  obtain ⟨⟨r, d, rest⟩, ho⟩ := exists_produces_of_sok (g := entitiesModeGen (k + 1) (k + 1) k b [et, x])
    (by rw [sok_we0]; simp)
  obtain ⟨eids, he⟩ := exists_produces_of_sok (g := (ArbitrarySized.arbitrarySized (k + 1) : SGen (List String)))
    (by rw [sok_arbListString]; simp)
  refine ⟨(r, d, (et, .enum (Data.Set.mk eids)) :: rest), ?_, by simp⟩
  rw [entitiesModeGen, (worker% gen SchemaGen.WfEntitiesGoR [0, 3, 4] eq_def)]
  simp only [produces_backtrack_iff, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
    exists_eq_left]
  refine .inr (.inr ⟨by decide, produces_bind_of het (produces_bind_of ho (produces_bind_of he ?_))⟩)
  exact produces_pure_iff.mpr rfl

/-- At leaf size `k + 1`, the entity schema can declare two types. -/
theorem produces_entities1_two (k : Nat) :
    ∃ out, Produces (entities1Gen (k + 2) (k + 1) (k + 1) [] []) out ∧ 2 ≤ out.2.2.length := by
  obtain ⟨et, het⟩ := exists_produces_of_sok (g := notInGen (k + 2) (k + 1) (k + 1) [])
    (by rw [sok_notIn_nil]; simp)
  obtain ⟨⟨r, d, rest⟩, ho, hne⟩ := produces_entitiesMode_cons k [] et
  obtain ⟨eids, he⟩ := exists_produces_of_sok (g := (ArbitrarySized.arbitrarySized (k + 1) : SGen (List String)))
    (by rw [sok_arbListString]; simp)
  refine ⟨(r, d, (et, .enum (Data.Set.mk eids)) :: rest), ?_, ?_⟩
  · rw [entities1Gen, (worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4] eq_def)]
    simp only [produces_backtrack_iff, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
      exists_eq_left]
    exact .inr ⟨by decide, produces_bind_of het (produces_bind_of ho (produces_bind_of he
      (produces_pure_iff.mpr rfl)))⟩
  · obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp

/-- At leaf size `k + 1`, with a budget of at least one request environment, the schema generator can
produce a schema with two entity types. -/
theorem produces_typeEnv_two (s k budget : Nat) (hb : 1 ≤ budget) :
    ∃ p, Produces (typeEnvGen (s + 1) (k + 1) s budget) p ∧ 2 ≤ p.2.ets.toList.length := by
  obtain ⟨⟨r, names, entries⟩, he, h2⟩ := produces_entities1_two k
  have hne := ((worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4] sound)
    (k + 2) (k + 1) (k + 1) [] [] _ he) |> wfEntitiesGo1_names_ne_nil
  obtain ⟨⟨acts, reqty⟩, ha⟩ := exists_produces_of_sok
    (g := actionsGen (k + 2) (k + 1) (k + 1) r names [] Cedar.Validation.Relational.Schema.actionEidPool budget)
    (by rw [sok_wa_top _ _ _ _ _ _ _ hne (by simp [Cedar.Validation.Relational.Schema.actionEidPool]) hb]; simp)
  refine ⟨(r, ⟨Data.Map.mk entries, Data.Map.mk acts, reqty⟩), ?_, h2⟩
  rw [typeEnvGen, (worker% gen SchemaGen.GenTypeEnvB [0, 2] eq_def)]
  rcases s with _ | s <;> simp only [produces_backtrack_iff, List.mem_cons, List.mem_nil_iff, or_false,
    exists_eq_left] <;>
    exact ⟨by decide, produces_bind_of he (produces_bind_of ha (produces_pure_iff.mpr rfl))⟩

/-- What can be produced has positive probability. -/
theorem sprob_ne_zero_of_produces {A : Type} {g : SGen A} {E : Set A} {x : A} (h : Produces g x)
    (hx : x ∈ E) : sprob g E ≠ 0 := by
  unfold sprob sexpect
  exact (SPMF.expect_pos_iff.mpr ⟨_, h, by simp [succVal, Set.indicator_of_mem hx]⟩).ne'

/-- **Two entity types have positive probability.** As its instance runs it, at leaf size at least one
and with a budget of at least one request environment, the schema generator produces a schema with
two entity types with positive probability. -/
theorem genTypeEnvB_instance_two_types (budget s l : Nat) (hb : 1 ≤ budget) (hl : 1 ≤ l) :
    sprob (BacktrackGenFor.gen (P := fun p : HierMode × TypeEnv => GenTypeEnvB p.1 budget p.2)
      (G := SGen) s l) {p | 2 ≤ p.2.ets.toList.length} ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hl
  obtain ⟨p, hp, h2⟩ := produces_typeEnv_two s k budget hb
  exact sprob_ne_zero_of_produces hp h2

end Cedar.Validation.Relational.SchemaGen.Sure
