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
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `enforce` and `enforceCompiledPolicy` are equivalent.
-/
theorem enforceCompiledPolicy_eqv_enforce_ok {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  enforce [wp.toExpr] (SymEnv.ofTypeEnv Γ) = enforceCompiledPolicy cp
:= by
  simp [enforce, enforceCompiledPolicy]
  intro h₀ h₁
  simp [
    cp_compile_produces_the_right_env h₀,
    cp_compile_produces_the_right_footprint h₀,
    cp_compile_produces_the_right_acyclicity h₀,
    compiled_policy_eq_wtp h₀ h₁,
  ]
  simp [footprints]
  simp [Data.Set.make_make_eqv, List.Equiv, List.subset_def]
  constructor
  · intro t h₂
    cases h₂
    · left
      rename_i h₂
      replace ⟨t', h₂, ht⟩ := h₂ ; subst t ; rename Term => t
      rw [Data.Set.in_list_iff_in_set] at *
      rw [Data.Set.mem_mapUnion_iff_mem_exists] at h₂
      replace ⟨s, hs, h₂⟩ := h₂
      simp at hs ; subst s
      simp [Data.Set.mem_map]
      exists t
    · right
      rename_i h₂
      simp [List.mem_mapUnion_iff_mem_exists] at *
      replace ⟨s, hs, t', ht', h₂⟩ := h₂ ; subst t ; rename Term => t
      simp [Data.Set.in_list_iff_in_set, Data.Set.mem_mapUnion_iff_mem_exists] at *
      exists s
      simp [hs]
      exists t
  · intro t h₂
    cases h₂
    · left
      rename_i h₂
      simp [Data.Set.in_list_iff_in_set, Data.Set.mem_map] at h₂
      replace ⟨t', ht', h₂⟩ := h₂ ; subst t ; rename Term => t
      exists t
      simp [Data.Set.in_list_iff_in_set, Data.Set.mem_mapUnion_iff_mem_exists]
      exact ht'
    · right
      rename_i h₂
      rw [List.mem_mapUnion_iff_mem_exists] at *
      simp only [List.mem_map] at *
      replace ⟨s, hs, t', ht', h₂⟩ := h₂ ; subst t ; rename Term => t
      exists s
      rw [Data.Set.in_list_iff_in_set] at *
      simp [Data.Set.mem_mapUnion_iff_mem_exists, hs]
      exists t
      simp [Data.Set.in_list_iff_in_set, Data.Set.mem_mapUnion_iff_mem_exists, ht']

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
  simp [enforce, enforcePairCompiledPolicy]
  intro h₀ h₁ h₂ h₃
  simp [
    cp_compile_produces_the_right_env h₀,
    cp_compile_produces_the_right_env h₁,
    cp_compile_produces_the_right_footprint h₀,
    cp_compile_produces_the_right_footprint h₁,
    cp_compile_produces_the_right_acyclicity h₀,
    cp_compile_produces_the_right_acyclicity h₁,
    compiled_policy_eq_wtp h₀ h₂,
    compiled_policy_eq_wtp h₁ h₃,
  ]
  have h_split : [wp₁.toExpr, wp₂.toExpr] = [wp₁.toExpr] ++ [wp₂.toExpr] := by simp
  rw [h_split, footprints_append, footprints_singleton, footprints_singleton]
  simp [Data.Set.make_make_eqv, List.Equiv, List.subset_def]
  constructor
  · intro t₁ h₁
    cases h₁ <;> rename_i h₁
    · replace ⟨t₂, h₁, htemp⟩ := h₁ ; subst t₁
      simp [Data.Set.in_list_iff_in_set] at *
      change t₂ ∈ _ ∪ _ at h₁
      rw [Data.Set.mem_union_iff_mem_or] at h₁
      cases h₁ <;> rename_i h₁
      case' inl => left
      case' inr => right ; left
      all_goals {
        simp [Data.Set.mem_map]
        exists t₂
      }
    · right ; right
      simp [*]
  · intro t₁ h₁
    cases h₁ <;> rename_i h₁ <;> try (cases h₁ <;> rename_i h₁)
    case right.inr.inr => right ; exact h₁
    case' right.inl | right.inr.inl =>
      left
      simp [Data.Set.in_list_iff_in_set, Data.Set.mem_map] at h₁
      replace ⟨t₂, h₁, htemp⟩ := h₁ ; subst t₁
      exists t₂
      simp [Data.Set.in_list_iff_in_set, HAppend.hAppend]
      change t₂ ∈ _ ∪ _
      rw [Data.Set.mem_union_iff_mem_or]
    case' right.inl => left
    case' right.inr.inl => right
    all_goals exact h₁

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `enforce` and `enforcePairCompiledPolicies` are
equivalent.
-/
theorem enforcePairCompiledPolicies_eqv_enforce_ok {ps₁ ps₂ wps₁ wps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  wellTypedPolicies ps₁ Γ = .ok wps₁ →
  wellTypedPolicies ps₂ Γ = .ok wps₂ →
  enforce (wps₁.map Policy.toExpr ++ wps₂.map Policy.toExpr) (SymEnv.ofTypeEnv Γ) = enforcePairCompiledPolicies cps₁ cps₂
:= by
  simp [enforce, enforcePairCompiledPolicies]
  intro hcps₁ hcps₂ hwps₁ hwps₂
  simp [
    cps_compile_produces_the_right_env hcps₁,
    cps_compile_produces_the_right_env hcps₂,
    cps_compile_produces_the_right_footprint hcps₁,
    cps_compile_produces_the_right_footprint hcps₂,
    cps_compile_produces_the_right_acyclicity hcps₁,
    cps_compile_produces_the_right_acyclicity hcps₂,
    compiled_policies_eq_wtps hcps₁ hwps₁,
    compiled_policies_eq_wtps hcps₂ hwps₂,
  ]
  simp [footprints_append]
  rw [Data.Set.make_make_eqv]
  simp [List.Equiv, List.subset_def]
  constructor
  · intro t₁ h₁
    cases h₁ <;> rename_i h₁
    · replace ⟨t₂, h₁, htemp⟩ := h₁ ; subst t₁
      simp [Data.Set.in_list_iff_in_set] at *
      simp [footprints]
      change t₂ ∈ _ ∪ _ at h₁
      rw [Data.Set.mem_union_iff_mem_or] at h₁
      cases h₁ <;> rename_i h₁
      case' inl => left
      case' inr => right ; left
      all_goals {
        simp [footprints] at h₁
        rw [Data.Set.mem_mapUnion_iff_mem_exists] at h₁
        replace ⟨x, h₁, h₂⟩ := h₁
        simp [Data.Set.mem_map]
        exists t₂
        simp [Data.Set.mem_mapUnion_iff_mem_exists]
        exists x
        apply And.intro _ h₂
        rw [List.mem_map] at h₁
        exact h₁
      }
    · right ; right
      simp [*]
  · intro t₁ h₁
    cases h₁ <;> rename_i h₁ <;> try (cases h₁ <;> rename_i h₁)
    case right.inr.inr => right ; exact h₁
    case' right.inl | right.inr.inl =>
      left
      simp [Data.Set.in_list_iff_in_set, Data.Set.mem_map] at h₁
      replace ⟨t₂, h₁, htemp⟩ := h₁ ; subst t₁
      simp [mem_footprints_iff] at h₁
      replace ⟨x, ⟨p, hp, htemp⟩, h₁⟩ := h₁ ; subst x
      exists t₂
      simp [Data.Set.in_list_iff_in_set, HAppend.hAppend]
      change t₂ ∈ _ ∪ _
      rw [Data.Set.mem_union_iff_mem_or]
    case' right.inl => left
    case' right.inr.inl => right
    all_goals {
      simp [mem_footprints_iff]
      exists p.toExpr
      apply And.intro _ h₁
      exists p
    }
