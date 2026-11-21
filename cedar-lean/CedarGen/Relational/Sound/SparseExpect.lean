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
import Specimen.Correctness.CondMean
import Specimen.Correctness.StepOf
import Mathlib.NumberTheory.Harmonic.Bounds
import Specimen.Correctness.Workers
import Specimen.Correctness.MeanWalk
import CedarGen.Relational.Sound.SchemaSure

/-! The sparse mode's ancestor draws, and the entity list's chance of success, which the bound on the
mean number of ancestors (`SparseAncestors`) is proved from. -/

namespace Cedar.Validation.Relational.SchemaGen.Sound

open Cedar.Spec Cedar.Validation Cedar.Validation.Relational Cedar.Validation.Relational.Schema
open Specimen.Correctness Basalt ENNReal

local notation "SGenA" => (SGen (List EntityType))

/-- The sparse ancestors of a built list. -/
noncomputable abbrev ancGen (B : List (EntityType × List EntityType)) (s l : Nat) : SGenA :=
  BacktrackGenFor.gen (P := fun a => Ancestors .sparse B a) (G := SGen) s l

theorem ancGen_eq (B : List (EntityType × List EntityType)) (s l : Nat) :
    ancGen B s l = Specimen.Backtrack.backtrack
      [(4, fun _ => BacktrackGenFor.gen (P := fun a => PickOneAncestor B a) (G := SGen) l l)] := by
  unfold ancGen
  unfold_gen_instances []
  rw [(worker% gen SchemaGen.Ancestors [2] eq_body)]
  delta_worker gen SchemaGen.Ancestors [2] body
  cases s <;> simp

/-- The sparse pick. -/
noncomputable abbrev pickOne (B : List (EntityType × List EntityType)) (s l : Nat) : SGenA :=
  BacktrackGenFor.gen (P := fun a => PickOneAncestor B a) (G := SGen) s l

theorem pickOne_eq (B : List (EntityType × List EntityType)) (s l : Nat) :
    pickOne B s l = (do
      let i ← chooseNat 0 B.length
      if i = 0 then pure [] else
      match B[i - 1]? with
      | some (p, pset) => pure (p :: pset)
      | none => Specimen.Fail.fail : SGenA) := rfl

/-- Indices `1 … n` of a list are its entries. -/
theorem sum_range_getElem? {β : Type} (f : β → ℝ≥0∞) : ∀ (B : List β),
    ∑ i ∈ Finset.range B.length, (match B[i]? with | some b => f b | none => 0) = (B.map f).sum
  | [] => by simp
  | b :: B => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
    rw [sum_range_getElem? f B]

/-- **The sparse pick, on average:** no parent, or each built type with its closure, uniformly. -/
theorem sexpect_pickOne (B : List (EntityType × List EntityType)) (s l : Nat) (φ : List EntityType → ℝ≥0∞) :
    sexpect (pickOne B s l) φ = (φ [] + (B.map fun q => φ (q.1 :: q.2)).sum) / (B.length + 1 : ℕ) := by
  rw [pickOne_eq, sexpect_bind, sexpect_chooseNat]
  congr 1
  · rw [show Finset.Icc 0 B.length = Finset.range (B.length + 1) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_range]; omega,
      Finset.sum_range_succ', ← sum_range_getElem? (fun q => φ (q.1 :: q.2)) B]
    simp only [ite_true, sexpect_pure, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    cases B[i]? with
    | none => simp
    | some q => simp [sexpect_pure]

theorem sok_pickOne (B : List (EntityType × List EntityType)) (s l : Nat) : sok (pickOne B s l) = 1 := by
  unfold sok
  rw [sexpect_pickOne]
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one]
  rw [Nat.cast_add, Nat.cast_one, add_comm]
  exact ENNReal.div_self (by simp) (by simp)

theorem sfail_pickOne (B : List (EntityType × List EntityType)) (s l : Nat) : sfail (pickOne B s l) = 0 :=
  sfail_eq_zero_of_sok (sok_pickOne B s l)

theorem sexpect_ancGen (B : List (EntityType × List EntityType)) (s l : Nat) (φ : List EntityType → ℝ≥0∞) :
    sexpect (ancGen B s l) φ = sexpect (pickOne B l l) φ := by
  rw [ancGen_eq, sexpect_backtrack_eq _ _ (by simp [Specimen.Backtrack.sumWeights])
    (by simp only [List.mem_singleton]; rintro p rfl; exact sok_pickOne B l l)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Specimen.Backtrack.sumWeights]
  rw [mul_comm]
  exact ENNReal.mul_div_cancel_right (by simp) (by simp)

theorem sok_ancGen (B : List (EntityType × List EntityType)) (s l : Nat) : sok (ancGen B s l) = 1 := by
  unfold sok; rw [sexpect_ancGen]; exact sok_pickOne B l l

theorem sfail_ancGen (B : List (EntityType × List EntityType)) (s l : Nat) : sfail (ancGen B s l) = 0 :=
  sfail_eq_zero_of_sok (sok_ancGen B s l)

/-! ## The entity list's chance of success does not depend on the ancestors built -/

#specimen_body_of gen SchemaGen.WfEntitiesGoR [3, 4]

open Cedar.Validation.Relational.SchemaGen.Sure (entitiesGen entitiesModeGen entities1Gen)

/-- In the sparse mode, the entity list succeeds and fails as often from any built list. -/
theorem entities_profile (iS : Nat) : ∀ (fuel size : Nat) (B B' : List (EntityType × List EntityType))
    (names : List EntityType),
    SameProfile (entitiesGen fuel iS size .sparse B names) (entitiesGen fuel iS size .sparse B' names)
  | 0, _, _, _, _ => by
    rw [entitiesGen, (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_1),
      (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_1)]
    exact sameProfile_refl _
  | fuel + 1, size, B, B', names => by
    rw [entitiesGen, (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_body),
      (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_body)]
    delta_worker gen SchemaGen.WfEntitiesGoR [3, 4] body
    cases size with
    | zero => exact sameProfile_refl _
    | succ size' =>
      refine sameProfile_backtrack (.cons ⟨rfl, sameProfile_refl _⟩ (.cons ⟨rfl, ?_⟩ (.cons ⟨rfl, ?_⟩ .nil)))
      · refine sameProfile_bind fun et => sameProfile_bind fun attrs => sameProfile_bind fun tags => ?_
        refine sameProfile_bind_uniform
          ⟨by rw [sok_ancGen, sok_ancGen], by rw [sfail_ancGen, sfail_ancGen]⟩ fun anc anc' => ?_
        refine sameProfile_bind_uniform (entities_profile iS fuel size' _ _ _) fun ⟨d, rest⟩ ⟨d', rest'⟩ => ?_
        exact ⟨by simp, by simp⟩
      · refine sameProfile_bind fun et => ?_
        refine sameProfile_bind_uniform (entities_profile iS fuel size' B B' _) fun ⟨d, rest⟩ ⟨d', rest'⟩ => ?_
        exact ⟨by rw [sok_bind, sok_bind]; simp, by rw [sfail_bind, sfail_bind]; simp⟩

/-! ## Counting ancestors -/

theorem ofReal_list_sum {β : Type} (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) : ∀ l : List β,
    (l.map fun b => ENNReal.ofReal (f b)).sum = ENNReal.ofReal (l.map f).sum
  | [] => by simp
  | b :: l => by
    rw [List.map_cons, List.sum_cons, ofReal_list_sum f hf l, List.map_cons, List.sum_cons,
      ENNReal.ofReal_add (hf b) (List.sum_nonneg fun x hx => by
        obtain ⟨b', -, rfl⟩ := List.mem_map.mp hx; exact hf b')]

/-- The ancestors a built list records, counted with multiplicity. -/
def closureLen (B : List (EntityType × List EntityType)) : ℕ := (B.map fun q => q.2.length).sum

theorem closureLen_cons (q : EntityType × List EntityType) (B : List (EntityType × List EntityType)) :
    closureLen (q :: B) = q.2.length + closureLen B := by simp [closureLen]

/-- The sparse worker succeeds equally often from any built list. -/
theorem entities_sok_eq (iS fuel size : Nat) (B B' : List (EntityType × List EntityType)) (names : List EntityType) :
    sok (entitiesGen fuel iS size .sparse B names) = sok (entitiesGen fuel iS size .sparse B' names) :=
  (entities_profile iS fuel size B B' names).1

/-- `H(n + 1) - 1`, as the sum of the harmonic series from `2`. -/
theorem harmonic_tail_one : ∀ n : ℕ, ∑ j ∈ Finset.Ioc 1 (n + 1), (1 : ℝ) / j = (harmonic (n + 1) : ℝ) - 1
  | 0 => by simp [harmonic]
  | n + 1 => by
    rw [Finset.sum_Ioc_succ_top (by omega), harmonic_tail_one n, harmonic_succ (n + 1), Rat.cast_add,
      Rat.cast_inv, Rat.cast_natCast]
    ring

end Cedar.Validation.Relational.SchemaGen.Sound
