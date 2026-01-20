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

theorem extractOpt?_eqv_extract? {cpsets : List CompiledPolicies} {I : Interpretation} {εnv : SymEnv} :
  cpsets ≠ [] →
  (∀ cpset ∈ cpsets, cpset.εnv = εnv) →
  -- the `CompiledPolicies` at least have to be constructed with `CompiledPolicy.compile` or `CompiledPolicySet.compile`, even though we don't care about the original uncompiled policies
  (∀ cpset ∈ cpsets, match cpset with
    | .policy cp => ∃ p Γ, CompiledPolicy.compile p Γ = .ok cp
    | .pset cpset => ∃ ps Γ, CompiledPolicySet.compile ps Γ = .ok cpset
  ) →
  extractOpt? cpsets I = SymEnv.extract? ((cpsets.flatMap CompiledPolicies.allPolicies).map Policy.toExpr) I εnv
:= by
  simp [extractOpt?, SymEnv.extract?]
  intro hnil hεnv hcompile
  simp only [CompiledPolicies.εnv] at hεnv
  split <;> simp_all only [reduceCtorEq, not_true_eq_false, not_false_eq_true, List.mem_cons,
    forall_eq_or_imp, List.flatMap_cons, List.map_append, footprints]
  rename_i cps cpss
  replace ⟨hεnv', hεnv⟩ := hεnv
  congr 3
  cases cps <;> simp_all only [CompiledPolicies.allPolicies, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  all_goals {
    subst εnv
    first | rename CompiledPolicy => cp | rename CompiledPolicySet => cps
    replace ⟨⟨p, Γ, hcompile⟩, hcompile'⟩ := hcompile ; try rename Policies => ps
    rw [List.mapUnion_cons]
    · simp only [CompiledPolicies.footprint]
      first
      | rw [List.mapUnion_cons (by simp [footprint_wf])]
      | rw [List.mapUnion_append (by simp [footprint_wf])]
      congr 1
      · first
        | apply cp_compile_produces_the_right_footprint hcompile
        | apply cpset_compile_produces_the_right_footprint hcompile
      · rw [List.mapUnion_map]
        rw [← Data.Set.eq_means_eqv List.mapUnion_wf List.mapUnion_wf]
        simp only [List.Equiv, List.subset_def, Data.Set.in_list_iff_in_set,
          List.mem_mapUnion_iff_mem_exists, List.mem_flatMap, Function.comp_apply,
          forall_exists_index, and_imp]
        constructor
        · intro t cps hcps ht
          specialize hcompile' cps hcps
          split at hcompile'
          · rename_i cps cp
            replace ⟨p', Γ', hcompile'⟩ := hcompile'
            have hfoot := cp_compile_produces_the_right_footprint hcompile'
            simp [CompiledPolicies.footprint, hfoot] at ht
            exists cp.policy
            specialize hεnv (.policy cp) hcps ; simp only at hεnv ; rw [← hεnv]
            simp only [ht, and_true]
            exists .policy cp
            simp [hcps, CompiledPolicies.allPolicies]
          · rename_i cps cpset
            replace ⟨ps', Γ', hcompile'⟩ := hcompile'
            have hfoot := cpset_compile_produces_the_right_footprint hcompile'
            simp only [footprints, List.mapUnion_map] at hfoot
            rw [← Data.Set.eq_means_eqv] at hfoot
            · simp only [List.Equiv, List.subset_def, Data.Set.in_list_iff_in_set] at hfoot
              replace ⟨hfoot, hfoot'⟩ := hfoot
              specialize hfoot ht
              rw [List.mem_mapUnion_iff_mem_exists] at hfoot
              replace ⟨p, hp, hfoot⟩ := hfoot
              exists p
              specialize hεnv (.pset cpset) hcps ; simp only at hεnv ; rw [← hεnv]
              simp only [Function.comp_apply] at hfoot
              simp only [hfoot, and_true]
              exists .pset cpset
            · simp [hfoot, List.mapUnion_wf]
            · simp [List.mapUnion_wf]
        · intro t p cps hcps hp ht
          exists cps
          specialize hcompile' cps hcps
          split at hcompile'
          · rename_i cps cp
            simp only [CompiledPolicies.allPolicies, List.mem_cons, List.not_mem_nil,
              or_false] at hp ; subst p
            replace ⟨p', Γ', hcompile'⟩ := hcompile'
            have hfoot := cp_compile_produces_the_right_footprint hcompile'
            simp only [hcps, CompiledPolicies.footprint, hfoot, true_and]
            specialize hεnv (.policy cp) hcps ; simp only at hεnv ; rw [← hεnv] at ht
            exact ht
          · rename_i cps cpset
            simp only [CompiledPolicies.allPolicies] at hp
            replace ⟨ps', Γ', hcompile'⟩ := hcompile'
            have hfoot := cpset_compile_produces_the_right_footprint hcompile'
            simp only [hcps, CompiledPolicies.footprint, hfoot, footprints, true_and]
            specialize hεnv (.pset cpset) hcps ; simp only at hεnv ; rw [← hεnv] at ht
            apply List.mem_mem_implies_mem_mapUnion (s := p.toExpr) ht
            simp only [List.mem_map]
            exists p
    · intro cps hcps
      cases hcps
      · first
        | have := cp_compile_produces_the_right_footprint hcompile
        | have := cpset_compile_produces_the_right_footprint hcompile
        simp only at this
        simp [CompiledPolicies.footprint, this, footprint_wf, footprints_wf]
      · rename_i hcps
        specialize hcompile' cps hcps
        split at hcompile'
        · rename_i cps cp
          replace ⟨p, Γ, hcompile'⟩ := hcompile'
          simp [CompiledPolicies.footprint, cp_compile_produces_the_right_footprint hcompile', footprint_wf]
        · rename_i cps cps
          replace ⟨ps, Γ, hcompile'⟩ := hcompile'
          simp [CompiledPolicies.footprint, cpset_compile_produces_the_right_footprint hcompile', footprints_wf]
  }
