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

import CedarGen.Relational.SchemaGenProb
import Specimen.Correctness.WalkSGenExpect
import Specimen.Correctness.CondMean
import Specimen.Correctness.SureLaws
import Specimen.Correctness.Workers
import Specimen.Correctness.SureWalk

/-! # Variety of request environments

The schema generator's request environments are bounded by its budget (`genTypeEnvB_iff`); this file
shows they are not degenerate: the request action has two distinct principals, and so at least two
request environments, with probability bounded below, proved of the derived code at `SGen`. -/

namespace Cedar.Validation.Relational.SchemaGen.Variety

open Specimen.Correctness Specimen.Backtrack Cedar.Spec ENNReal

/-- The hand-written picker for `DefinedEntityType ets`: uniform over `ets`. -/
noncomputable abbrev pickTypeGen (ets : List EntityType) (i j : Nat) : SGen EntityType :=
  BacktrackGenFor.gen (P := fun et => Cedar.Validation.Relational.Schema.DefinedEntityType ets et)
    (G := SGen) i j

theorem sum_Icc_getElem? {α : Type} (l : List α) (h : l ≠ []) (f : α → ℝ≥0∞) :
    ∑ k ∈ Finset.Icc 0 (l.length - 1), l[k]?.elim 0 f = (l.map f).sum := by
  have hn := List.length_pos_iff.mpr h
  rw [show Finset.Icc 0 (l.length - 1) = Finset.range l.length by ext; simp; omega, Finset.sum_range,
    ← Fin.sum_univ_fun_getElem]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Option.elim]

/-- The picker is uniform over `ets`. -/
theorem pick_sexpect (ets : List EntityType) (i j : Nat) (h : ets ≠ []) (f : EntityType → ℝ≥0∞) :
    sexpect (pickTypeGen ets i j) f = (ets.map f).sum / ets.length := by
  dsimp only [pickTypeGen, BacktrackGenFor.gen]
  have hn := List.length_pos_iff.mpr h
  simp only [List.isEmpty_iff, h, ↓reduceIte]
  rw [sexpect_bind, sexpect_chooseNat, ← sum_Icc_getElem? ets h,
    show ets.length - 1 - 0 + 1 = ets.length by omega]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  cases ets[k]? with
  | none => exact sexpect_refute f
  | some et => simp [Option.elim, sexpect_pure]

theorem pick_sok (ets : List EntityType) (i j : Nat) (h : ets ≠ []) : sok (pickTypeGen ets i j) = 1 := by
  rw [sok, pick_sexpect ets i j h]
  simp [ENNReal.div_self, h]

/-- Over distinct types, all but at most one differ from `c`. -/
theorem length_sub_one_le {ets : List EntityType} (hd : ets.Nodup) (c : EntityType) :
    ((ets.length - 1 : ℕ) : ℝ≥0∞) ≤ (ets.map fun y => if y = c then 0 else 1).sum := by
  induction ets with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨hy, hd⟩ := List.nodup_cons.mp hd
    by_cases e : y = c
    · subst e
      have : ys.map (fun z => if z = y then (0 : ℝ≥0∞) else 1) = ys.map fun _ => 1 :=
        List.map_congr_left fun z hz => by split_ifs with hz' <;> [exact absurd (hz' ▸ hz) hy; rfl]
      simp [this]
    · calc ((ys.length + 1 - 1 : ℕ) : ℝ≥0∞) ≤ 1 + ((ys.length - 1 : ℕ) : ℝ≥0∞) := by
            exact_mod_cast (by omega : ys.length + 1 - 1 ≤ 1 + (ys.length - 1))
        _ ≤ _ := by simpa [e] using add_le_add_left (ih hd) 1

/-- **A uniform draw then misses what follows it.** Draw `y` uniformly from distinct types, then run
`x`: the type `x` produces first differs from `y` with probability at least `1 - 1/n` of `x`'s
success. So a continuation that succeeds surely into an event when they differ reaches it with at
least that probability. -/
theorem pick_miss {β γ : Type} (ets : List EntityType) (i j : Nat) (hd : ets.Nodup) (h : ets ≠ [])
    (x : SGen (EntityType × β)) (K : EntityType → EntityType × β → SGen γ) (f : γ → ℝ≥0∞)
    (hK : ∀ y r, y ≠ r.1 → 1 ≤ sexpect (K y r) f) :
    ((ets.length - 1 : ℕ) : ℝ≥0∞) * sok x / ets.length ≤ sexpect (pickTypeGen ets i j >>= fun y => x >>= K y) f := by
  rw [sexpect_bind, pick_sexpect ets i j h]
  gcongr
  calc ((ets.length - 1 : ℕ) : ℝ≥0∞) * sok x = sexpect x fun _ => ((ets.length - 1 : ℕ) : ℝ≥0∞) := by
        rw [sok, ← sexpect_mul_left]; simp
    _ ≤ sexpect x fun r => (ets.map fun y => if y = r.1 then 0 else 1).sum :=
        sexpect_mono _ fun r => length_sub_one_le hd r.1
    _ = (ets.map fun y => sexpect x fun r => if y = r.1 then 0 else 1).sum := sexpect_list_sum _ _ _
    _ ≤ (ets.map fun y => sexpect (x >>= K y) f).sum := by
        refine List.sum_le_sum fun y _ => ?_
        rw [sexpect_bind]
        refine sexpect_mono _ fun r => ?_
        by_cases e : y = r.1
        · simp [e]
        · simpa [e] using hK y r e

/-- The derived generator for `BoundedTypes ets n xs`, `xs` out. -/
noncomputable abbrev boundedTypesGen : ℕ → ℕ → ℕ → List EntityType → ℕ → SGen (List EntityType) :=
  (worker% gen SchemaGen.BoundedTypes [2])

/-- The derived generator for `ContainsBounded ets n x xs`, `x` and `xs` out. -/
noncomputable abbrev containsBoundedGen : ℕ → ℕ → ℕ → List EntityType → ℕ → SGen (EntityType × List EntityType) :=
  (worker% gen SchemaGen.ContainsBounded [2, 3])

theorem bt_sok : ∀ (sz fuel iS : Nat) (ets : List EntityType) (b : Nat), ets ≠ [] → sz < fuel →
    sok (boundedTypesGen fuel iS sz ets b) = 1 := by
  intro sz
  induction sz with
  | zero =>
    intro fuel iS ets b hne hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [boundedTypesGen, (worker% gen SchemaGen.BoundedTypes [2] eq_def)]
    cases b <;> sok_search []
  | succ s ih =>
    intro fuel iS ets b hne hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have ih' (iS b) : sok (boundedTypesGen f iS s ets b) = 1 := ih f iS ets b hne (by omega)
    rw [boundedTypesGen, (worker% gen SchemaGen.BoundedTypes [2] eq_def)]
    cases b <;> sok_search [sok_fact% pick_sok, sok_fact% ih']

/-- With no budget, nothing to produce: the search is empty, and fails surely. -/
theorem cb_tot_zero (fuel iS sz : Nat) (ets : List EntityType) : Tot (containsBoundedGen fuel iS sz ets 0) := by
  rw [containsBoundedGen, (worker% gen SchemaGen.ContainsBounded [2, 3] eq_def)]
  rcases fuel with _ | f
  · exact tot_outOfFuel
  · rcases sz with _ | s <;> tot_search []

theorem cb_sok : ∀ (sz fuel iS : Nat) (ets : List EntityType) (b : Nat), ets ≠ [] → 1 ≤ b →
    sz < fuel → sok (containsBoundedGen fuel iS sz ets b) = 1 := by
  intro sz
  have hbt (iS : Nat) (ets : List EntityType) (n : Nat) (h : ets ≠ []) : sok (boundedTypesGen (iS + 1) iS iS ets n) = 1 :=
    bt_sok iS (iS + 1) iS ets n h (by omega)
  induction sz with
  | zero =>
    intro fuel iS ets b hne hb hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [containsBoundedGen, (worker% gen SchemaGen.ContainsBounded [2, 3] eq_def)]
    sok_search [sok_fact% pick_sok, sok_fact% hbt]
  | succ s ih =>
    intro fuel iS ets b hne hb hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    have hrec : Tot (containsBoundedGen f iS s ets n) := by
      rcases n with _ | m
      · exact cb_tot_zero f iS s ets
      · exact tot_of_sok (ih f iS ets (m + 1) hne (by omega) (by omega))
    rw [containsBoundedGen, (worker% gen SchemaGen.ContainsBounded [2, 3] eq_def)]
    sok_search [sok_fact% pick_sok, sok_fact% hbt, tot_fact% hrec]

/-- **The request's principals are varied.** With a budget of at least two environments, distinct
entity types, and size to recurse, `ContainsBounded` gives the request a principal list holding some
type other than the request's principal (so at least two principals, and two request environments)
with probability at least `5/9 · (1 - 1/n)`: the `there` branch's share of the weight, times a fresh
uniform type's chance of differing from the principal. -/
theorem cb_variety (sz fuel iS : Nat) (ets : List EntityType) (b : Nat) (hd : ets.Nodup)
    (hne : ets ≠ []) (hb : 2 ≤ b) (hsz : 1 ≤ sz) (hf : sz < fuel) :
    5 * ((((ets.length - 1 : ℕ) : ℝ≥0∞) * 1) / (ets.length : ℝ≥0∞)) / 9 ≤
      sprob (containsBoundedGen fuel iS sz ets b) {p | ∃ z ∈ p.2, z ≠ p.1} := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  rw [sprob, containsBoundedGen, (worker% gen SchemaGen.ContainsBounded [2, 3] eq_def)]
  simp only [List.filterMap_cons, List.filterMap_nil, ↓reduceIte]
  refine le_trans ?_ (sexpect_backtrack_ge _ _ (by simp [sumWeights]))
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sumWeights, add_zero]
  refine ENNReal.div_le_div (le_trans (mul_le_mul_right ?_ 5) le_add_self) (by norm_num)
  refine le_trans ?_ (pick_miss ets iS iS hd hne _ _ _ fun y r hy => ?_)
  · rw [cb_sok s f iS ets n hne (by omega) (by omega)]
  · simp [DecOpt.negOpt, DecOpt.decOpt, Ne.symm hy, sexpect_pure, Set.indicator, hy]

end Cedar.Validation.Relational.SchemaGen.Variety
