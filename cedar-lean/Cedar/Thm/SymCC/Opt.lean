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

import Cedar.SymCC
import Cedar.SymCCOpt
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.Set
import Cedar.Thm.SymCC.Authorizer
import Cedar.Thm.SymCC.Opt.CompiledPolicies
import Cedar.Thm.WellTypedVerification

/-!
Proofs that the optimized interface in SymCCOpt is equivalent to the unoptimized
interface in SymCC.
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
compilation succeeds, then `verifyEvaluate` and `verifyEvaluateOpt` are
equivalent.
-/
theorem verifyEvaluateOpt_eqv_verifyEvaluate_ok {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} {φ : Term → Term} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  verifyEvaluate φ wp (SymEnv.ofTypeEnv Γ) = .ok (verifyEvaluateOpt φ cp)
:= by
  simp [verifyEvaluate, verifyEvaluateOpt]
  simp [do_eq_ok]
  intro h₀ h₁
  simp [enforceCompiledPolicy_eqv_enforce_ok h₀ h₁]
  exists cp.term ; simp
  exact (cp_compile_produces_the_right_term h₀ h₁).symm

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyNeverErrors` and `verifyNeverErrorsOpt` are
equivalent.
-/
theorem verifyNeverErrorsOpt_eqv_verifyNeverErrors_ok {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  verifyNeverErrors wp (SymEnv.ofTypeEnv Γ) = .ok (verifyNeverErrorsOpt cp)
:= by
  simp [verifyNeverErrors, verifyNeverErrorsOpt]
  exact verifyEvaluateOpt_eqv_verifyEvaluate_ok

/--
If `CompiledPolicy.compile` succeeds, then `wellTypedPolicy` succeeds
-/
theorem compile_ok_then_welltypedpolicy_ok {p : Policy} {Γ : Validation.TypeEnv} :
  Except.isOk (CompiledPolicy.compile p Γ) →
  Except.isOk (wellTypedPolicy p Γ)
:= by
  simp [Except.isOk, Except.toBool]
  simp [CompiledPolicy.compile, Except.mapError]
  cases h₀ : wellTypedPolicy p Γ <;> simp

/--
If `CompiledPolicy.compile` succeeds, then `wellTypedPolicy` succeeds
-/
theorem compile_ok_then_exists_wtp {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  ∃ wp, wellTypedPolicy p Γ = .ok wp
:= by
  intro h₀
  have h₁ := compile_ok_then_welltypedpolicy_ok (by
    simp [Except.isOk_iff_exists]
    exists cp
  )
  simp [Except.isOk_iff_exists] at h₁
  exact h₁

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `neverErrors?` and
`neverErrorsOpt?` are equivalent.
-/
theorem neverErrorsOpt?_eqv_neverErrors?_ok {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p Γ = .ok cp →
  ∃ wp,
    wellTypedPolicy p Γ = .ok wp ∧
    neverErrorsOpt? cp = neverErrors? wp (SymEnv.ofTypeEnv Γ)
:= by
  simp [neverErrors?, neverErrorsOpt?]
  simp [sat?]
  intro hwf h₀
  have ⟨wp, h₁⟩ := compile_ok_then_exists_wtp h₀
  exists wp ; apply And.intro h₁
  have ⟨asserts, h₂⟩ := verifyNeverErrors_is_ok hwf h₁
  simp [h₂]
  simp [cp_compile_produces_the_right_env h₀]
  simp [compiled_policy_eq_wtp h₀ h₁]
  simp [verifyNeverErrorsOpt_eqv_verifyNeverErrors_ok h₀ h₁] at h₂
  subst asserts ; rfl
