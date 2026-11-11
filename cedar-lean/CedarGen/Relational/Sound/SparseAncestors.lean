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

import CedarGen.Relational.Sound.SparseExpect
import Specimen.Correctness.MeanWalk
import CedarGen.Relational.Sound.SchemaSure
import Specimen.Correctness.Workers

/-! # Per type, the mean ancestor closure is logarithmic

In the sparse mode, the expected number of ancestors of a uniformly chosen standard entity type is,
over the generator's successes with at least one standard type, at most `H(N) - 1 ≤ ln N`, where `N`
bounds the number of standard types. For the schema generator's entity part, as its instance runs it
at leaf size `l`, `N = l + 1`. -/

namespace Cedar.Validation.Relational.SchemaGen.Sound

open Cedar.Spec Cedar.Validation Cedar.Validation.Relational Cedar.Validation.Relational.Schema
open Specimen.Correctness Specimen.Backtrack Basalt ENNReal

open Cedar.Validation.Relational.SchemaGen.Sure (entitiesGen entitiesModeGen entities1Gen)


/-! ## Ancestor statistics -/

/-- The standard entries' ancestor lists: their total length, and their number. -/
def ancStats : List (EntityType × EntitySchemaEntry) → ℕ × ℕ
  | [] => (0, 0)
  | (_, .standard e) :: rest => ((ancStats rest).1 + e.ancestors.elts.length, (ancStats rest).2 + 1)
  | (_, .enum _) :: rest => ancStats rest

/-- The mean number of ancestors of a standard entry; `0` without one. -/
noncomputable def meanAnc (entries : List (EntityType × EntitySchemaEntry)) : ℝ :=
  if (ancStats entries).2 = 0 then 0 else ((ancStats entries).1 : ℝ) / (ancStats entries).2

theorem meanAnc_eq (entries : List (EntityType × EntitySchemaEntry)) :
    meanAnc entries = ((ancStats entries).1 : ℝ) / (ancStats entries).2 := by
  unfold meanAnc; split <;> simp_all

/-! ## The potential -/

/-- The harmonic series from `m + 1` to `N`; empty past `N`. -/
noncomputable def htail (m N : ℕ) : ℝ := ∑ j ∈ Finset.Ioc m N, (1 : ℝ) / j

theorem htail_nonneg (m N : ℕ) : 0 ≤ htail m N := Finset.sum_nonneg fun _ _ => by positivity

theorem htail_succ (m N : ℕ) (h : m + 1 ≤ N) : htail m N = 1 / ((m : ℝ) + 1) + htail (m + 1) N := by
  unfold htail
  rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ m) h, Nat.Ioc_succ_singleton, Finset.sum_singleton]
  push_cast; ring

theorem htail_one (n : ℕ) : ENNReal.ofReal (htail 1 n) = ENNReal.ofReal ((harmonic n : ℝ) - 1) := by
  cases n with
  | zero =>
    rw [ENNReal.ofReal_of_nonpos (by simp [htail]), ENNReal.ofReal_of_nonpos (by simp [harmonic])]
  | succ n => rw [htail, harmonic_tail_one]

theorem harmonic_sub_one_le_log (n : ℕ) : (harmonic n : ℝ) - 1 ≤ Real.log n := by
  have := harmonic_le_one_add_log n; linarith

/-- The potential at `m` standard types with `L` ancestors in all: their mean, and what the types
still to come may add to it. -/
noncomputable def Ψ (L m N : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((L : ℝ) / m + htail (max m 1) N)

/-- The potential at the end of the entity list, from a built list `B`. -/
noncomputable def ancOut (B : List (EntityType × List EntityType)) (N : ℕ)
    (out : List EntityType × List (EntityType × EntitySchemaEntry)) : ℝ≥0∞ :=
  Ψ (closureLen B + (ancStats out.2).1) (B.length + (ancStats out.2).2) N

theorem sum_map_real (c d t : ℝ) : ∀ B : List (EntityType × List EntityType),
    (B.map fun q => ((q.2.length : ℝ) + c) / d + t).sum = ((closureLen B : ℝ) + B.length * c) / d + B.length * t
  | [] => by simp [closureLen]
  | q :: B => by
    rw [List.map_cons, List.sum_cons, sum_map_real c d t B, closureLen_cons, List.length_cons]
    push_cast; ring

/-- **The potential is a supermartingale under the sparse pick.** -/
theorem Ψ_pick (et : EntityType) (B : List (EntityType × List EntityType)) (N : ℕ) (h : B.length + 1 ≤ N) :
    (Ψ (closureLen ((et, []) :: B)) (B.length + 1) N +
        (B.map fun q => Ψ (closureLen ((et, q.1 :: q.2) :: B)) (B.length + 1) N).sum) /
      (B.length + 1 : ℕ) ≤ Ψ (closureLen B) B.length N := by
  rcases Nat.eq_zero_or_pos B.length with h0 | hm
  · rw [List.length_eq_zero_iff] at h0; subst h0; simp [Ψ, closureLen]
  · set m := B.length with hmdef
    set L := closureLen B with hL
    set T1 := htail (m + 1) N
    have hB : (B.map fun q => Ψ (closureLen ((et, q.1 :: q.2) :: B)) (m + 1) N) =
        B.map fun q => ENNReal.ofReal (((q.2.length : ℝ) + ((L : ℝ) + 1)) / ((m : ℝ) + 1) + T1) := by
      refine List.map_congr_left fun q _ => ?_
      simp only [Ψ, closureLen_cons, List.length_cons, max_eq_left (by omega : 1 ≤ m + 1), T1, ← hL]
      congr 2; push_cast; ring
    have h0 : Ψ (closureLen ((et, []) :: B)) (m + 1) N = ENNReal.ofReal ((L : ℝ) / ((m : ℝ) + 1) + T1) := by
      simp only [Ψ, closureLen_cons, List.length_nil, zero_add, max_eq_left (by omega : 1 ≤ m + 1), T1,
        ← hL]
      push_cast; rfl
    have hT : ∀ q : EntityType × List EntityType,
        0 ≤ ((q.2.length : ℝ) + ((L : ℝ) + 1)) / ((m : ℝ) + 1) + T1 :=
      fun q => add_nonneg (by positivity) (htail_nonneg _ _)
    rw [hB, h0, ofReal_list_sum _ hT, sum_map_real,
      ← ENNReal.ofReal_add (add_nonneg (by positivity) (htail_nonneg _ _))
        (add_nonneg (by positivity) (mul_nonneg (by positivity) (htail_nonneg _ _))),
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos (by positivity)]
    simp only [Ψ, max_eq_left (by omega : 1 ≤ m)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [htail_succ m N h]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have key : (L : ℝ) / m + (1 / ((m : ℝ) + 1) + T1) -
        (L / ((m : ℝ) + 1) + T1 + ((L + m * (L + 1)) / ((m : ℝ) + 1) + m * T1)) / ((m + 1 : ℕ) : ℝ) =
        (L + m) / (m * ((m : ℝ) + 1) ^ 2) := by
      push_cast
      field_simp
      ring
    have : 0 ≤ ((L : ℝ) + m) / (m * ((m : ℝ) + 1) ^ 2) := by positivity
    linarith

/-! ## The sparse entity list, from any built list -/

/-- A standard type placed with its ancestors moves them from the output to the built list. -/
theorem ancOut_standard (B : List (EntityType × List EntityType)) (N : ℕ) (et : EntityType)
    (anc : List EntityType) (attrs) (tags) (d : List EntityType) (rest : List (EntityType × EntitySchemaEntry)) :
    ancOut B N (d, (et, .standard ⟨Cedar.Data.Set.mk anc, attrs, tags⟩) :: rest) ≤ ancOut ((et, anc) :: B) N (d, rest) :=
  le_of_eq (by
    simp only [ancOut, ancStats, closureLen_cons, List.length_cons, Cedar.Data.Set.elts]
    congr 1 <;> omega)

/-- **The potential, on the sparse pick:** over the ancestors drawn after `B`, the potential with one more
type is on average at most the potential at `B`. -/
theorem meanLeW_ancGen_Ψ (B : List (EntityType × List EntityType)) (N : ℕ) ⦃s l : ℕ⦄ ⦃C : Type⦄ ⦃k : List EntityType → SGen C⦄ ⦃F W : C → ℝ≥0∞⦄
    (hk : ∀ anc, MeanLeW (k anc) F W (Ψ (anc.length + closureLen B) (B.length + 1) N))
    (hq : ∀ anc anc', sexpect (k anc) W = sexpect (k anc') W) (hB : B.length + 1 ≤ N) :
    MeanLeW (ancGen B s l >>= k) F W (Ψ (closureLen B) B.length N) := by
  refine meanLeW_bind_uniform hk (fun anc => hq anc []) ?_
  unfold MeanLe
  rw [sexpect_ancGen, sexpect_pickOne, sok_ancGen, mul_one]
  simpa [closureLen_cons] using Ψ_pick default B N hB


theorem entities_meanLe_anc (iS N : Nat) : ∀ (fuel size : Nat) (B : List (EntityType × List EntityType))
    (names : List EntityType), B.length + size ≤ N →
    MeanLe (entitiesGen fuel iS size .sparse B names) (ancOut B N) (Ψ (closureLen B) B.length N)
  | 0, _, _, _, _ => by
    rw [entitiesGen, (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_1)]
    unfold MeanLe; rw [sexpect_outOfFuel]; exact zero_le
  | fuel + 1, size, B, names, hN => by
    rw [entitiesGen, (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_def), ← meanLeW_iff_meanLe]
    cases size <;> mean_walk [entities_meanLe_anc iS N fuel, unfold_fact% (meanLeW_ancGen_Ψ B N)]
    all_goals mean_close [Sure.sok_arbListString, entities_sok_eq, ancOut_standard, ancOut,
      ancStats, closureLen_cons]

theorem meanAnc_le_ancOut (N : ℕ) (out : List EntityType × List (EntityType × EntitySchemaEntry)) :
    ENNReal.ofReal (meanAnc out.2) ≤ ancOut [] N out := by
  simp only [ancOut, Ψ, closureLen, List.map_nil, List.sum_nil, List.length_nil, zero_add, meanAnc_eq]
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (htail_nonneg _ _))

/-- **Per type, for the sparse worker.** From no types, at size `n`, the mean number of
ancestors of a standard entity type is, over the successes, at most `H(n) - 1`. -/
theorem sparse_mean_ancestors (fuel iS size : ℕ) (names : List EntityType) :
    MeanLe (entitiesGen fuel iS size .sparse [] names)
      (fun out => ENNReal.ofReal (meanAnc out.2))
      (ENNReal.ofReal ((harmonic size : ℝ) - 1)) := by
  have h := entities_meanLe_anc iS size fuel size [] names (by simp)
  unfold MeanLe at *
  refine le_trans (sexpect_mono _ fun out => meanAnc_le_ancOut size out) (h.trans_eq ?_)
  simp [Ψ, closureLen, htail_one]

/-- …at most `ln n`. -/
theorem sparse_mean_ancestors_log (fuel iS size : ℕ) (names : List EntityType) :
    MeanLe (entitiesGen fuel iS size .sparse [] names)
      (fun out => ENNReal.ofReal (meanAnc out.2))
      (ENNReal.ofReal (Real.log size)) :=
  meanLe_mono (ENNReal.ofReal_le_ofReal (harmonic_sub_one_le_log size)) (sparse_mean_ancestors fuel iS size names)

/-! ## Given at least one standard type -/

theorem sexpect_zero_fun {A : Type} (g : SGen A) : sexpect g (fun _ => 0) = 0 := by
  simpa using sexpect_mul_left g 0 (fun _ => 1)

theorem meanAnc_std_le (N : ℕ) (et : EntityType) (attrs) (tags) (d : List EntityType)
    (rest : List (EntityType × EntitySchemaEntry)) :
    ENNReal.ofReal (meanAnc ((et, .standard (StandardSchemaEntry.mk (Cedar.Data.Set.mk []) attrs tags)) :: rest))
      ≤ ancOut [(et, [])] N (d, rest) := by
  simp only [ancOut, Ψ, meanAnc_eq, ancStats, closureLen, Cedar.Data.Set.elts, List.length_nil,
    List.length_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Nat.add_comm 1]
  exact le_add_of_nonneg_right (htail_nonneg _ _)

theorem anc_sparse_nil {anc : List EntityType} (h : Ancestors .sparse [] anc) : anc = [] := by
  cases h with
  | sparse _ _ hp =>
    cases hp with
    | none => rfl
    | one _ _ hm => cases hm

/-- From no types, the sparse mode draws no ancestors, and the others have mean `0`. -/
theorem meanLeW_anc_sparse {C : Type} {l : ℕ} {k : HierMode × List EntityType → SGen C} {F W : C → ℝ≥0∞}
    {c : ℝ≥0∞} (hk : MeanLeW (k (.sparse, [])) F W c) (h0 : ∀ a anc, a ≠ .sparse → MeanLeW (k (a, anc)) F W 0) :
    MeanLeW (BacktrackGenFor.gen (P := fun x : HierMode × List EntityType => Ancestors x.1 [] x.2)
      (G := SGen) l l >>= k) F W c := by
  refine meanLeW_bind_support fun ⟨a, anc⟩ hp => ?_
  have ha := (worker% gen SchemaGen.Ancestors [0, 2] sound) _ _ _ _ _ hp
  cases a with
  | sparse => obtain rfl := anc_sparse_nil ha; exact hk
  | dense | flat =>
    refine meanLeW_of_zero (le_antisymm ?_ zero_le)
    simpa [MeanLeW] using h0 _ anc (by decide)

/-- From no types, the sparse ancestors are none. -/
theorem meanLeW_ancGen_nil {C : Type} {s l : ℕ} {k : List EntityType → SGen C} {F W : C → ℝ≥0∞} {c : ℝ≥0∞}
    (h : MeanLeW (k []) F W c) : MeanLeW (ancGen [] s l >>= k) F W c := by
  unfold MeanLeW at *
  rw [sexpect_bind, sexpect_bind, sexpect_ancGen, sexpect_ancGen, sexpect_pickOne, sexpect_pickOne]
  simpa using h

theorem entities_meanLeW_anc (iS N : ℕ) : ∀ (fuel size : ℕ) (names : List EntityType), size ≤ N →
    MeanLeW (entitiesGen fuel iS size .sparse [] names) (fun out => ENNReal.ofReal (meanAnc out.2))
      (fun out => if 1 ≤ (ancStats out.2).2 then 1 else 0) (ENNReal.ofReal (htail 1 N))
  | 0, _, _, _ => by
    rw [entitiesGen, (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_1)]
    exact meanLeW_of_zero (sexpect_outOfFuel _)
  | fuel + 1, size, names, hN => by
    rw [entitiesGen, (worker% gen SchemaGen.WfEntitiesGoR [3, 4] eq_def)]
    cases size <;> mean_walk [unfold_fact% @meanLeW_ancGen_nil, entities_meanLeW_anc iS N fuel,
      entities_meanLe_anc iS N]
    all_goals mean_close [Sure.sok_arbListString, meanAnc_std_le, meanAnc, ancStats, Ψ, closureLen]

/-- **Per type, given a standard type.** The sparse worker at size `n`, from no types: the
mean number of ancestors of a standard entity type, over its successes with at least one, is at most
`H(n) - 1`. -/
theorem sparse_mean_ancestors_cond (fuel iS size : ℕ) (names : List EntityType) :
    sexpect (entitiesGen fuel iS size .sparse [] names) (fun out => ENNReal.ofReal (meanAnc out.2)) ≤
      ENNReal.ofReal ((harmonic size : ℝ) - 1) *
        sprob (entitiesGen fuel iS size .sparse [] names) {out | 1 ≤ (ancStats out.2).2} := by
  have h := entities_meanLeW_anc iS size fuel size names le_rfl
  unfold MeanLeW at h
  rw [htail_one] at h
  refine h.trans_eq ?_
  unfold sprob
  congr 1
  exact sexpect_congr _ fun out => by simp [Set.indicator]

/-- …at most `ln n`. -/
theorem sparse_mean_ancestors_cond_log (fuel iS size : ℕ) (names : List EntityType) :
    sexpect (entitiesGen fuel iS size .sparse [] names) (fun out => ENNReal.ofReal (meanAnc out.2)) ≤
      ENNReal.ofReal (Real.log size) *
        sprob (entitiesGen fuel iS size .sparse [] names) {out | 1 ≤ (ancStats out.2).2} :=
  (sparse_mean_ancestors_cond fuel iS size names).trans
    (by gcongr; exact harmonic_sub_one_le_log size)

/-! ## The schema generator's entity part, as its instance runs it

The mode is drawn at the first standard type, by `Ancestors` on no built types (or, with none, at the
end of the list). Only the sparse runs count, on both sides. -/


/-- The mean number of ancestors, on the sparse runs. -/
noncomputable abbrev sparseMeanF : HierMode × List EntityType × List (EntityType × EntitySchemaEntry) → ℝ≥0∞ :=
  fun o => if o.1 = .sparse then ENNReal.ofReal (meanAnc o.2.2) else 0

/-- The sparse runs with a standard type. -/
noncomputable abbrev sparseStdW : HierMode × List EntityType × List (EntityType × EntitySchemaEntry) → ℝ≥0∞ :=
  fun o => if o.1 = .sparse ∧ 1 ≤ (ancStats o.2.2).2 then 1 else 0

theorem sparseMeanF_std_le (N : ℕ) (et : EntityType) (attrs) (tags) (d : List EntityType)
    (rest : List (EntityType × EntitySchemaEntry)) :
    sparseMeanF (.sparse, d, (et, .standard (StandardSchemaEntry.mk (Cedar.Data.Set.mk []) attrs tags)) :: rest)
      ≤ ancOut [(et, [])] N (d, rest) := by
  simpa [sparseMeanF] using meanAnc_std_le N et attrs tags d rest

theorem we0_meanLeW (iS N : ℕ) : ∀ (fuel sz : ℕ) (names : List EntityType), sz ≤ N →
    MeanLeW (entitiesModeGen fuel iS sz [] names) sparseMeanF sparseStdW (ENNReal.ofReal (htail 1 N))
  | 0, _, _, _ => by
    rw [entitiesModeGen, (worker% gen SchemaGen.WfEntitiesGoR [0, 3, 4] eq_1)]
    exact meanLeW_of_zero (sexpect_outOfFuel _)
  | fuel + 1, sz, names, hN => by
    rw [entitiesModeGen, (worker% gen SchemaGen.WfEntitiesGoR [0, 3, 4] eq_def)]
    cases sz <;> mean_walk [unfold_fact% @meanLeW_anc_sparse, we0_meanLeW iS N fuel, entities_meanLe_anc iS N]
    all_goals mean_close [Sure.sok_arbListString, sparseMeanF_std_le, sparseMeanF, sparseStdW, meanAnc, ancStats,
      Ψ, closureLen]

theorem e1_meanLeW (l : ℕ) :
    MeanLeW (entities1Gen (l + 1) l l [] []) sparseMeanF sparseStdW (ENNReal.ofReal (htail 1 (l + 1))) := by
  rw [entities1Gen, (worker% gen SchemaGen.WfEntitiesGo1 [0, 3, 4] eq_def)]
  have hwe0 := we0_meanLeW l (l + 1)
  have hwe := entities_meanLe_anc l (l + 1)
  cases l <;> mean_walk [unfold_fact% @meanLeW_anc_sparse, hwe0, hwe]
  all_goals mean_close [Sure.sok_arbListString, sparseMeanF_std_le, sparseMeanF, sparseStdW, meanAnc, ancStats,
    Ψ, closureLen]

/-- The schema generator's entity part, as `GenTypeEnvB`'s instance runs it at leaf size `l`:
the mode, the type names, the entries. -/
noncomputable abbrev entities1Inst (l : ℕ) : SGen (HierMode × List EntityType × List (EntityType × EntitySchemaEntry)) :=
  BacktrackGenFor.gen (P := fun x : HierMode × List EntityType × List (EntityType × EntitySchemaEntry) =>
    match x with | (a, names, entries) => WfEntitiesGo1 a [] [] names entries) (G := SGen) l l

/-- **Per type, for the schema generator's entities.** At leaf size `l`, over the sparse runs
with at least one standard type, the mean number of ancestors of a standard entity type is at most
`H(l + 1) - 1`. -/
theorem entities1_sparse_mean (l : ℕ) :
    sexpect (entities1Inst l) (fun o => if o.1 = .sparse then ENNReal.ofReal (meanAnc o.2.2) else 0) ≤
      ENNReal.ofReal ((harmonic (l + 1) : ℝ) - 1) *
        sexpect (entities1Inst l) (fun o => if o.1 = .sparse ∧ 1 ≤ (ancStats o.2.2).2 then 1 else 0) := by
  have h := e1_meanLeW l
  unfold MeanLeW at h
  rw [htail_one] at h
  exact h

/-- …at most `ln (l + 1)`. -/
theorem entities1_sparse_mean_log (l : ℕ) :
    sexpect (entities1Inst l) (fun o => if o.1 = .sparse then ENNReal.ofReal (meanAnc o.2.2) else 0) ≤
      ENNReal.ofReal (Real.log (l + 1)) *
        sexpect (entities1Inst l) (fun o => if o.1 = .sparse ∧ 1 ≤ (ancStats o.2.2).2 then 1 else 0) := by
  refine (entities1_sparse_mean l).trans ?_
  gcongr
  have := harmonic_sub_one_le_log (l + 1)
  push_cast at this
  exact this

end Cedar.Validation.Relational.SchemaGen.Sound

#print axioms Cedar.Validation.Relational.SchemaGen.Sound.sparse_mean_ancestors
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.sparse_mean_ancestors_log
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.sparse_mean_ancestors_cond
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.sparse_mean_ancestors_cond_log
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.entities1_sparse_mean
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.entities1_sparse_mean_log
