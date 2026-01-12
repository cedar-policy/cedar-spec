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

import Cedar.SymCCOpt.Extractor
import Cedar.Thm.SymCC.Opt.CompiledPolicies

/-!
Proofs that the optimized functions in SymCCOpt.Extractor are equivalent to the unoptimized
ones in SymCC.Extractor.
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.SymCC

theorem cp_extractOpt?_eqv_extract? {cps : List CompiledPolicy} {I : Interpretation} {εnv : SymEnv} :
  cps ≠ [] →
  (∀ cp ∈ cps, cp.εnv = εnv) →
  -- the `CompiledPolicy`s at least have to be constructed with `CompiledPolicy.compile`, even though we don't care about the original uncompiled policies
  (∀ cp ∈ cps, ∃ p Γ, CompiledPolicy.compile p Γ = .ok cp) →
  CompiledPolicy.extractOpt? cps I = SymEnv.extract? (cps.map (Policy.toExpr ∘ CompiledPolicy.policy)) I εnv
:= by
  simp [CompiledPolicy.extractOpt?, SymEnv.extract?]
  intro hnil hεnv hcompile
  split
  · simp at hnil
  · rename_i term εnv' policy footprint acyclicity cps
    simp only [List.mem_cons, forall_eq_or_imp] at hεnv
    replace ⟨hεnv', hεnv⟩ := hεnv ; subst εnv'
    simp_all only [reduceCtorEq, not_false_eq_true, List.map_cons, Function.comp_apply, footprints]
    congr 3
    rw [Data.Set.mapUnion_cons]
    · rw [Data.Set.mapUnion_cons]
      · congr 1
        · replace ⟨p, Γ, hcompile⟩ := hcompile { term, εnv, policy, footprint, acyclicity } (by simp)
          apply cp_compile_produces_the_right_footprint hcompile
        · rw [Data.Set.mapUnion_map (footprint_wf · εnv)]
          apply Data.Set.mapUnion_congr
          intro cp hcp
          replace ⟨p, Γ, hcompile⟩ := hcompile cp (by simp [hcp])
          simp [cp_compile_produces_the_right_footprint hcompile, hεnv cp hcp]
      · intro x hx
        cases hx <;> apply footprint_wf
    · intro cp hcp
      cases hcp
      · replace ⟨p, Γ, hcompile⟩ := hcompile { term, εnv, policy, footprint, acyclicity } (by simp)
        have := cp_compile_produces_the_right_footprint hcompile ; simp at this ; subst footprint
        simp [footprint_wf]
      · rename_i hcp
        replace ⟨p, Γ, hcompile⟩ := hcompile cp (by right ; simp [hcp])
        simp [cp_compile_produces_the_right_footprint hcompile]
        apply footprint_wf

theorem cps_extractOpt?_eqv_extract? {cpss : List CompiledPolicies} {I : Interpretation} {εnv : SymEnv} :
  cpss ≠ [] →
  (∀ cps ∈ cpss, cps.εnv = εnv) →
  -- the `CompiledPolicies` at least have to be constructed with `CompiledPolicies.compile`, even though we don't care about the original uncompiled policies
  (∀ cps ∈ cpss, ∃ ps Γ, CompiledPolicies.compile ps Γ = .ok cps) →
  CompiledPolicies.extractOpt? cpss I = SymEnv.extract? ((cpss.flatMap CompiledPolicies.policies).map Policy.toExpr) I εnv
:= by
  simp [CompiledPolicies.extractOpt?, SymEnv.extract?]
  intro hnil hεnv hcompile
  split
  · simp at hnil
  · rename_i term εnv' policies footprint acyclicity cpss
    simp only [List.mem_cons, forall_eq_or_imp] at hεnv
    replace ⟨hεnv', hεnv⟩ := hεnv ; subst εnv'
    simp_all only [reduceCtorEq, not_false_eq_true, List.mem_cons, forall_eq_or_imp, List.map_cons,
      Function.comp_apply, List.flatten_cons, List.flatMap_cons, List.map_append, footprints]
    congr 3
    · grind
    · replace ⟨⟨ps, Γ, hcompile⟩, hcompile'⟩ := hcompile
      rw [Data.Set.mapUnion_cons]
      · rw [Data.Set.mapUnion_append (by simp [footprint_wf])]
        rw [Data.Set.mapUnion_map (by simp [footprint_wf])]
        rw [Data.Set.mapUnion_map (by simp [footprint_wf])]
        simp only [Union.union, HAppend.hAppend]
        congr 1
        · have := cps_compile_produces_the_right_footprint hcompile ; simp at this ; subst footprint
          simp only [footprints]
          apply Data.Set.mapUnion_map (by simp [footprint_wf])
        · rw [← Data.Set.eq_means_eqv Data.Set.mapUnion_wf Data.Set.mapUnion_wf]
          simp [List.Equiv, List.subset_def]
          constructor
          · intro t
            simp only [Data.Set.in_list_iff_in_set]
            simp only [Data.Set.mem_mapUnion_iff_mem_exists t, List.mem_flatMap,
              Function.comp_apply, forall_exists_index, and_imp]
            intro cps hcps ht
            replace ⟨ps', Γ', hcompile'⟩ := hcompile' cps hcps
            have hfoot := cps_compile_produces_the_right_footprint hcompile'
            simp only [footprints] at hfoot
            rw [Data.Set.mapUnion_map (by simp [footprint_wf])] at hfoot
            rw [← Data.Set.eq_means_eqv] at hfoot
            · simp [List.Equiv, List.subset_def, Data.Set.in_list_iff_in_set] at hfoot
              replace ⟨hfoot, hfoot'⟩ := hfoot
              specialize hfoot ht
              rw [Data.Set.mem_mapUnion_iff_mem_exists] at hfoot
              replace ⟨p, hp, hfoot⟩ := hfoot
              exists p
              rw [hεnv cps hcps] at *
              grind
            · simp [hfoot, Data.Set.mapUnion_wf]
            · simp [Data.Set.mapUnion_wf]
          · intro t
            simp only [Data.Set.in_list_iff_in_set]
            simp only [Data.Set.mem_mapUnion_iff_mem_exists t, List.mem_flatMap,
              Function.comp_apply, forall_exists_index, and_imp]
            intro p cps hcps hp ht
            exists cps
            replace ⟨ps', Γ', hcompile'⟩ := hcompile' cps hcps
            have hfoot := cps_compile_produces_the_right_footprint hcompile'
            simp only [hcps, hfoot, footprints, true_and]
            rw [hεnv cps hcps] at *
            apply Data.Set.mem_mem_implies_mem_mapUnion (s := p.toExpr) ht
            simp only [List.mem_map]
            exists p
      · intro cps hcps
        cases hcps
        · have := cps_compile_produces_the_right_footprint hcompile ; simp at this ; subst footprint
          simp [footprints_wf]
        · rename_i hcps
          have ⟨ps, Γ, hcompile'⟩ := hcompile' cps hcps
          have := cps_compile_produces_the_right_footprint hcompile'
          simp [this, footprints_wf]
