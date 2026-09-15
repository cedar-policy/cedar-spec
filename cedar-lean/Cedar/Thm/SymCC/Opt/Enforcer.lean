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

import Cedar.SymCCOpt.Enforcer
import Cedar.Thm.SymCC.Opt.CompiledPolicies

/-!
Proofs that the optimized functions in SymCCOpt.Enforcer are equivalent to the unoptimized
ones in SymCC.Enforcer.
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.SymCC

/--
Rephrases the unoptimized `enforce` as the union of the acyclicity and transitivity constraints
using the `Set.map`/`Set.product`/`∪` operations that the optimized `enforce*CompiledPolicy*`
functions are defined with.
-/
theorem enforce_eq_map_union {xs : List Expr} {εnv : SymEnv} :
  enforce xs εnv =
    (footprints xs εnv).map (acyclicity · εnv.entities) ∪
    ((footprints xs εnv).product (footprints xs εnv)).map (fun (t₁, t₂) => transitivity t₁ t₂ εnv.entities)
:= by
  simp only [enforce]
  rw [Data.Set.eq_means_eqv (Data.Set.make_wf _) (Data.Set.union_wf _ _)]
  simp only [List.Equiv, List.subset_def, Data.Set.mem_elts_iff_mem_set, Data.Set.mem_make,
    Data.Set.mem_union, List.mem_union_iff, List.mem_flatMap, List.mem_map, Data.Set.mem_map]
  constructor <;> intro a h
  · rcases h with ⟨x, hx, hf⟩ | ⟨x, hx, y, hy, hf⟩
    · exact Or.inl ⟨x, hx, hf⟩
    · exact Or.inr ⟨(x, y), Data.Set.mem_product.mpr ⟨hx, hy⟩, hf⟩
  · rcases h with ⟨x, hx, hf⟩ | ⟨⟨x, y⟩, hxy, hf⟩
    · exact Or.inl ⟨x, hx, hf⟩
    · rw [Data.Set.mem_product] at hxy
      exact Or.inr ⟨x, hxy.1, y, hxy.2, hf⟩

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `enforce` and `enforceCompiledPolicy` are equivalent.
-/
theorem enforceCompiledPolicy_eqv_enforce_ok {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  enforce [wp.toExpr] (SymEnv.ofTypeEnv Γ) = enforceCompiledPolicy cp
:= by
  intro h₀ h₁
  simp only [
    enforceCompiledPolicy,
    enforce_eq_map_union,
    footprints_singleton,
    cp_compile_produces_the_right_env h₀,
    cp_compile_produces_the_right_footprint h₀,
    cp_compile_produces_the_right_acyclicity h₀,
    cp_compile_produces_the_right_policy h₀ h₁,
  ]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `enforce` and `enforcePairCompiledPolicy` are
equivalent.
-/
theorem enforcePairCompiledPolicy_eqv_enforce_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  enforce [wp₁.toExpr, wp₂.toExpr] (SymEnv.ofTypeEnv Γ) = enforcePairCompiledPolicy cp₁ cp₂
:= by
  intro h₀ h₁ h₂ h₃
  have h_split : [wp₁.toExpr, wp₂.toExpr] = [wp₁.toExpr] ++ [wp₂.toExpr] := by simp
  simp only [
    enforcePairCompiledPolicy,
    enforce_eq_map_union,
    h_split,
    footprints_append,
    footprints_singleton,
    Data.Set.map_union,
    Data.Set.append_eq_union,
    cp_compile_produces_the_right_env h₀,
    cp_compile_produces_the_right_env h₁,
    cp_compile_produces_the_right_footprint h₀,
    cp_compile_produces_the_right_footprint h₁,
    cp_compile_produces_the_right_acyclicity h₀,
    cp_compile_produces_the_right_acyclicity h₁,
    cp_compile_produces_the_right_policy h₀ h₂,
    cp_compile_produces_the_right_policy h₁ h₃,
    reduceIte,
  ]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `enforce` and `enforcePairCompiledPolicySet` are
equivalent.
-/
theorem enforcePairCompiledPolicySet_eqv_enforce_ok {ps₁ ps₂ wps₁ wps₂ : Policies} {cpset₁ cpset₂ : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  CompiledPolicySet.compile ps₁ Γ = .ok cpset₁ →
  CompiledPolicySet.compile ps₂ Γ = .ok cpset₂ →
  wellTypedPolicies ps₁ Γ = .ok wps₁ →
  wellTypedPolicies ps₂ Γ = .ok wps₂ →
  enforce (wps₁.map Policy.toExpr ++ wps₂.map Policy.toExpr) (SymEnv.ofTypeEnv Γ) = enforcePairCompiledPolicySet cpset₁ cpset₂
:= by
  intro hcpset₁ hcpset₂ hwps₁ hwps₂
  simp only [
    enforcePairCompiledPolicySet,
    enforce_eq_map_union,
    footprints_append,
    Data.Set.append_eq_union,
    Data.Set.map_union,
    cpset_compile_produces_the_right_env hcpset₁,
    cpset_compile_produces_the_right_env hcpset₂,
    cpset_compile_produces_the_right_footprint hcpset₁,
    cpset_compile_produces_the_right_footprint hcpset₂,
    cpset_compile_produces_the_right_acyclicity hcpset₁,
    cpset_compile_produces_the_right_acyclicity hcpset₂,
    cpset_compile_produces_the_right_policies hcpset₁ hwps₁,
    cpset_compile_produces_the_right_policies hcpset₂ hwps₂,
    reduceIte,
  ]
