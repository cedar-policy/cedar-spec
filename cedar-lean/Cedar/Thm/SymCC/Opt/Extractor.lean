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

/-- The footprints of compiled policies are the footprints of the policies they contain. -/
private theorem compiledPolicies_footprint_mapUnion {cpss : List CompiledPolicies} {εnv : SymEnv}
  (hεnv : ∀ cps ∈ cpss, cps.εnv = εnv)
  (hcompile : ∀ cps ∈ cpss, match cps with
    | .policy cp => ∃ p Γ, CompiledPolicy.compile p Γ = .ok cp
    | .pset cpset => ∃ ps Γ, CompiledPolicySet.compile ps Γ = .ok cpset) :
  cpss.mapUnion CompiledPolicies.footprint =
    (cpss.flatMap CompiledPolicies.allPolicies).mapUnion ((footprint · εnv) ∘ Policy.toExpr)
:= by
  induction cpss with
  | nil => simp
  | cons cps cpss ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hεnv hcompile
    rw [List.mapUnion_cons, List.flatMap_cons, List.mapUnion_append, ih hεnv.right hcompile.right]
    congr 1
    replace hεnv := hεnv.left
    replace hcompile := hcompile.left
    cases cps with
    | policy cp =>
      replace ⟨_, _, hcompile⟩ := hcompile
      simp only [CompiledPolicies.εnv] at hεnv
      simp [CompiledPolicies.footprint, CompiledPolicies.allPolicies,
        cp_compile_produces_the_right_footprint hcompile, hεnv]
    | pset cpset =>
      replace ⟨_, _, hcompile⟩ := hcompile
      simp only [CompiledPolicies.εnv] at hεnv
      simp [CompiledPolicies.footprint, CompiledPolicies.allPolicies,
        cpset_compile_produces_the_right_footprint hcompile, footprints, hεnv]

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
      | rw [List.mapUnion_cons]
      | rw [List.mapUnion_append]
      congr 1
      · first
        | apply cp_compile_produces_the_right_footprint hcompile
        | apply cpset_compile_produces_the_right_footprint hcompile
      · rw [List.mapUnion_map]
        exact compiledPolicies_footprint_mapUnion hεnv hcompile'
  }
