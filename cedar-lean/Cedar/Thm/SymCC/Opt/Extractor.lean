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

theorem extractOpt?_eqv_extract? {cpₛs : List CompiledPolicyₛ} {I : Interpretation} {εnv : SymEnv} :
  cpₛs ≠ [] →
  (∀ cpₛ ∈ cpₛs, cpₛ.εnv = εnv) →
  -- the `CompiledPolicyₛ` at least have to be constructed with `CompiledPolicy.compile` or `CompiledPolicies.compile`, even though we don't care about the original uncompiled policies
  (∀ cpₛ ∈ cpₛs, match cpₛ with
    | .policy cp => ∃ p Γ, CompiledPolicy.compile p Γ = .ok cp
    | .policies cps => ∃ ps Γ, CompiledPolicies.compile ps Γ = .ok cps
  ) →
  extractOpt? cpₛs I = SymEnv.extract? ((cpₛs.flatMap CompiledPolicyₛ.allPolicies).map Policy.toExpr) I εnv
:= by
  simp [extractOpt?, SymEnv.extract?]
  intro hnil hεnv hcompile
  simp only [CompiledPolicyₛ.εnv] at hεnv
  split <;> simp_all only [reduceCtorEq, not_true_eq_false, not_false_eq_true, List.mem_cons,
    forall_eq_or_imp, List.flatMap_cons, List.map_append, footprints]
  rename_i cpₛ cpₛs
  replace ⟨hεnv', hεnv⟩ := hεnv
  congr 3
  cases cpₛ <;> simp_all only [CompiledPolicyₛ.allPolicies, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  all_goals {
    subst εnv
    first | rename CompiledPolicy => cp | rename CompiledPolicies => cps
    replace ⟨⟨p, Γ, hcompile⟩, hcompile'⟩ := hcompile ; try rename Policies => ps
    rw [List.mapUnion_cons]
    · simp only [CompiledPolicyₛ.footprint]
      first
      | rw [List.mapUnion_cons (by simp [footprint_wf])]
      | rw [List.mapUnion_append (by simp [footprint_wf])]
      congr 1
      · first
        | apply cp_compile_produces_the_right_footprint hcompile
        | apply cps_compile_produces_the_right_footprint hcompile
      · rw [List.mapUnion_map]
        rw [← Data.Set.eq_means_eqv List.mapUnion_wf List.mapUnion_wf]
        simp only [List.Equiv, List.subset_def, Data.Set.in_list_iff_in_set,
          List.mem_mapUnion_iff_mem_exists, List.mem_flatMap, Function.comp_apply,
          forall_exists_index, and_imp]
        constructor
        · intro t cpₛ hcpₛ ht
          specialize hcompile' cpₛ hcpₛ
          split at hcompile'
          · rename_i cpₛ cp
            replace ⟨p', Γ', hcompile'⟩ := hcompile'
            have hfoot := cp_compile_produces_the_right_footprint hcompile'
            simp [CompiledPolicyₛ.footprint, hfoot] at ht
            exists cp.policy
            specialize hεnv (.policy cp) hcpₛ ; simp only at hεnv ; rw [← hεnv]
            simp only [ht, and_true]
            exists .policy cp
            simp [hcpₛ, CompiledPolicyₛ.allPolicies]
          · rename_i cpₛ cps
            replace ⟨ps', Γ', hcompile'⟩ := hcompile'
            have hfoot := cps_compile_produces_the_right_footprint hcompile'
            simp only [footprints, List.mapUnion_map] at hfoot
            rw [← Data.Set.eq_means_eqv] at hfoot
            · simp only [List.Equiv, List.subset_def, Data.Set.in_list_iff_in_set] at hfoot
              replace ⟨hfoot, hfoot'⟩ := hfoot
              specialize hfoot ht
              rw [List.mem_mapUnion_iff_mem_exists] at hfoot
              replace ⟨p, hp, hfoot⟩ := hfoot
              exists p
              specialize hεnv (.policies cps) hcpₛ ; simp only at hεnv ; rw [← hεnv]
              simp only [Function.comp_apply] at hfoot
              simp only [hfoot, and_true]
              exists .policies cps
            · simp [hfoot, List.mapUnion_wf]
            · simp [List.mapUnion_wf]
        · intro t p cpₛ hcpₛ hp ht
          exists cpₛ
          specialize hcompile' cpₛ hcpₛ
          split at hcompile'
          · rename_i cpₛ cp
            simp only [CompiledPolicyₛ.allPolicies, List.mem_cons, List.not_mem_nil,
              or_false] at hp ; subst p
            replace ⟨p', Γ', hcompile'⟩ := hcompile'
            have hfoot := cp_compile_produces_the_right_footprint hcompile'
            simp only [hcpₛ, CompiledPolicyₛ.footprint, hfoot, true_and]
            specialize hεnv (.policy cp) hcpₛ ; simp only at hεnv ; rw [← hεnv] at ht
            exact ht
          · rename_i cpₛ cps
            simp only [CompiledPolicyₛ.allPolicies] at hp
            replace ⟨ps', Γ', hcompile'⟩ := hcompile'
            have hfoot := cps_compile_produces_the_right_footprint hcompile'
            simp only [hcpₛ, CompiledPolicyₛ.footprint, hfoot, footprints, true_and]
            specialize hεnv (.policies cps) hcpₛ ; simp only at hεnv ; rw [← hεnv] at ht
            apply List.mem_mem_implies_mem_mapUnion (s := p.toExpr) ht
            simp only [List.mem_map]
            exists p
    · intro cpₛ hcpₛ
      cases hcpₛ
      · first
        | have := cp_compile_produces_the_right_footprint hcompile
        | have := cps_compile_produces_the_right_footprint hcompile
        simp only at this
        simp [CompiledPolicyₛ.footprint, this, footprint_wf, footprints_wf]
      · rename_i hcpₛ
        specialize hcompile' cpₛ hcpₛ
        split at hcompile'
        · rename_i cpₛ cp
          replace ⟨p, Γ, hcompile'⟩ := hcompile'
          simp [CompiledPolicyₛ.footprint, cp_compile_produces_the_right_footprint hcompile', footprint_wf]
        · rename_i cpₛ cps
          replace ⟨ps, Γ, hcompile'⟩ := hcompile'
          simp [CompiledPolicyₛ.footprint, cps_compile_produces_the_right_footprint hcompile', footprints_wf]
  }
