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

import Cedar.SymCCOpt.Verifier
import Cedar.Thm.SymCC.Opt.AllowDeny
import Cedar.Thm.SymCC.Opt.Asserts
import Cedar.Thm.SymCC.Opt.CompiledPolicies
import Cedar.Thm.SymCC.Opt.Enforcer

/-!
Proofs that the optimized functions in SymCCOpt.Verifier are equivalent to the unoptimized
ones in SymCC.Verifier.
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.SymCC

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyEvaluate` and `verifyEvaluateOpt` are
equivalent.
-/
theorem verifyEvaluateOpt_eqv_verifyEvaluate_ok {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} {φ : Term → Term} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  verifyEvaluate φ wp (SymEnv.ofTypeEnv Γ) ~ .ok (verifyEvaluateOpt φ cp)
:= by
  simp [verifyEvaluate, verifyEvaluateOpt, ResultAssertsEquiv]
  intro h₀ h₁
  simp [enforceCompiledPolicy_eqv_enforce_ok h₀ h₁]
  cases h₂ : compile wp.toExpr (SymEnv.ofTypeEnv Γ) <;> simp
  case error e =>
    simp only [CompiledPolicy.compile, Except.mapError, h₁, Except.bind_ok] at h₀
    rw [Opt.compile.correctness] at h₀
    simp [h₂] at h₀
  case ok t =>
    have h₃ := (cp_compile_produces_the_right_term h₀ h₁).symm ; simp [h₂] at h₃ ; subst t
    split <;> rename_i hnot
    · apply Asserts.Equiv.constantFalse <;> simp [hnot]
    · apply Asserts.Equiv.rfl

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyEvaluatePair` and `verifyEvaluatePairOpt` are
equivalent.
-/
theorem verifyEvaluatePairOpt_eqv_verifyEvaluatePair_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} {φ : Term → Term → Term} :
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  verifyEvaluatePair φ wp₁ wp₂ (SymEnv.ofTypeEnv Γ) ~ .ok (verifyEvaluatePairOpt φ cp₁ cp₂)
:= by
  simp [verifyEvaluatePair, verifyEvaluatePairOpt, ResultAssertsEquiv]
  intro h₀ h₁ h₂ h₃
  have henv : cp₁.εnv = cp₂.εnv := by
    simp [cp_compile_produces_the_right_env h₀, cp_compile_produces_the_right_env h₁]
  simp [henv]
  simp [enforcePairCompiledPolicy_eqv_enforce_ok h₀ h₁ h₂ h₃]
  cases h₄ : compile wp₁.toExpr (SymEnv.ofTypeEnv Γ) <;> simp
  case error e =>
    simp only [CompiledPolicy.compile, Except.mapError, h₂, Except.bind_ok] at h₀
    rw [Opt.compile.correctness] at h₀
    simp [h₄] at h₀
  case ok t₁ =>
    have h₅ := (cp_compile_produces_the_right_term h₀ h₂).symm ; simp [h₄] at h₅ ; subst t₁
    cases h₆ : compile wp₂.toExpr (SymEnv.ofTypeEnv Γ) <;> simp
    case error e =>
      simp only [CompiledPolicy.compile, Except.mapError, h₃, Except.bind_ok] at h₁
      rw [Opt.compile.correctness] at h₁
      simp [h₆] at h₁
    case ok t₂ =>
      have h₇ := (cp_compile_produces_the_right_term h₁ h₃).symm ; simp [h₆] at h₇ ; subst t₂
      split <;> rename_i hnot
      · apply Asserts.Equiv.constantFalse <;> simp [hnot]
      · apply Asserts.Equiv.rfl

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyIsAuthorized` and `verifyIsAuthorizedOpt` are
equivalent.
-/
theorem verifyIsAuthorizedOpt_eqv_verifyIsAuthorized_ok {ps₁ ps₂ wps₁ wps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} {φ : Term → Term → Term} :
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  wellTypedPolicies ps₁ Γ = .ok wps₁ →
  wellTypedPolicies ps₂ Γ = .ok wps₂ →
  verifyIsAuthorized φ wps₁ wps₂ (SymEnv.ofTypeEnv Γ) ~ .ok (verifyIsAuthorizedOpt φ cps₁ cps₂)
:= by
  simp [verifyIsAuthorized, verifyIsAuthorizedOpt, ResultAssertsEquiv]
  intro hcps₁ hcps₂ hwps₁ hwps₂
  simp [enforcePairCompiledPolicies_eqv_enforce_ok hcps₁ hcps₂ hwps₁ hwps₂]
  have henvs : cps₁.εnv = cps₂.εnv := by
    simp [cps_compile_produces_the_right_env hcps₁, cps_compile_produces_the_right_env hcps₂]
  simp [henvs]
  cases h₁ : SymCC.isAuthorized wps₁ (SymEnv.ofTypeEnv Γ) <;> simp
  case error e =>
    simp_all only [CompiledPolicies.compile, Except.mapError, Except.bind_ok]
    rw [Opt.isAuthorized.correctness] at hcps₁
    simp [h₁] at hcps₁
  case ok t =>
    have h₃ := (cps_compile_produces_the_right_term hcps₁ hwps₁).symm ; simp [h₁] at h₃ ; subst t
    cases h₂ : SymCC.isAuthorized wps₂ (SymEnv.ofTypeEnv Γ) <;> simp
    case error e =>
      simp_all only [CompiledPolicies.compile, Except.mapError, Except.bind_ok]
      rw [Opt.isAuthorized.correctness] at hcps₂
      simp [h₂] at hcps₂
    case ok t =>
      have h₃ := (cps_compile_produces_the_right_term hcps₂ hwps₂).symm ; simp [h₂] at h₃ ; subst t
      split <;> rename_i hnot
      · apply Asserts.Equiv.constantFalse <;> simp [hnot]
      · apply Asserts.Equiv.rfl

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyNeverErrors` and `verifyNeverErrorsOpt` are
equivalent.
-/
theorem verifyNeverErrorsOpt_eqv_verifyNeverErrors_ok {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  verifyNeverErrors wp (SymEnv.ofTypeEnv Γ) ~ .ok (verifyNeverErrorsOpt cp)
:= by
  simp [verifyNeverErrors, verifyNeverErrorsOpt]
  exact verifyEvaluateOpt_eqv_verifyEvaluate_ok

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyAlwaysMatches` and `verifyAlwaysMatchesOpt` are
equivalent.
-/
theorem verifyAlwaysMatchesOpt_eqv_verifyAlwaysMatches_ok {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  verifyAlwaysMatches wp (SymEnv.ofTypeEnv Γ) ~ .ok (verifyAlwaysMatchesOpt cp)
:= by
  simp [verifyAlwaysMatches, verifyAlwaysMatchesOpt]
  exact verifyEvaluateOpt_eqv_verifyEvaluate_ok

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyNeverMatches` and `verifyNeverMatchesOpt` are
equivalent.
-/
theorem verifyNeverMatchesOpt_eqv_verifyNeverMatches_ok {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  verifyNeverMatches wp (SymEnv.ofTypeEnv Γ) ~ .ok (verifyNeverMatchesOpt cp)
:= by
  simp [verifyNeverMatches, verifyNeverMatchesOpt]
  exact verifyEvaluateOpt_eqv_verifyEvaluate_ok

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyMatchesEquivalent` and
`verifyMatchesEquivalentOpt` are equivalent.
-/
theorem verifyMatchesEquivalentOpt_eqv_verifyMatchesEquivalent_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  verifyMatchesEquivalent wp₁ wp₂ (SymEnv.ofTypeEnv Γ) ~ .ok (verifyMatchesEquivalentOpt cp₁ cp₂)
:= by
  simp [verifyMatchesEquivalent, verifyMatchesEquivalentOpt]
  exact verifyEvaluatePairOpt_eqv_verifyEvaluatePair_ok

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyMatchesImplies` and
`verifyMatchesImpliesOpt` are equivalent.
-/
theorem verifyMatchesImpliesOpt_eqv_verifyMatchesImplies_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  verifyMatchesImplies wp₁ wp₂ (SymEnv.ofTypeEnv Γ) ~ .ok (verifyMatchesImpliesOpt cp₁ cp₂)
:= by
  simp [verifyMatchesImplies, verifyMatchesImpliesOpt]
  exact verifyEvaluatePairOpt_eqv_verifyEvaluatePair_ok

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyMatchesDisjoint` and
`verifyMatchesDisjointOpt` are equivalent.
-/
theorem verifyMatchesDisjointOpt_eqv_verifyMatchesDisjoint_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  verifyMatchesDisjoint wp₁ wp₂ (SymEnv.ofTypeEnv Γ) ~ .ok (verifyMatchesDisjointOpt cp₁ cp₂)
:= by
  simp [verifyMatchesDisjoint, verifyMatchesDisjointOpt]
  exact verifyEvaluatePairOpt_eqv_verifyEvaluatePair_ok

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyImplies` and `verifyImpliesOpt` are
equivalent.
-/
theorem verifyImpliesOpt_eqv_verifyImplies_ok {ps₁ ps₂ wps₁ wps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  wellTypedPolicies ps₁ Γ = .ok wps₁ →
  wellTypedPolicies ps₂ Γ = .ok wps₂ →
  verifyImplies wps₁ wps₂ (SymEnv.ofTypeEnv Γ) ~ .ok (verifyImpliesOpt cps₁ cps₂)
:= by
  simp [verifyImplies, verifyImpliesOpt]
  exact verifyIsAuthorizedOpt_eqv_verifyIsAuthorized_ok

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyAlwaysAllows` and `verifyAlwaysAllowsOpt` are
equivalent.
-/
theorem verifyAlwaysAllowsOpt_eqv_verifyAlwaysAllows_ok {ps wps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps Γ = .ok cps →
  wellTypedPolicies ps Γ = .ok wps →
  verifyAlwaysAllows wps (SymEnv.ofTypeEnv Γ) ~ .ok (verifyAlwaysAllowsOpt cps)
:= by
  simp [verifyAlwaysAllows, verifyAlwaysAllowsOpt]
  intro hcps hwps
  apply verifyImpliesOpt_eqv_verifyImplies_ok _ hcps (wellTypedPolicies_allowAll Γ) hwps
  simp [CompiledPolicies.compile, Except.mapError, do_eq_ok, wellTypedPolicies_allowAll]
  rw [Opt.isAuthorized.correctness]
  simp [isAuthorized_allowAll, CompiledPolicies.allowAll, cps_compile_produces_the_right_env hcps, footprints_singleton]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyAlwaysAllows` and `verifyAlwaysAllowsOpt` are
equivalent.
-/
theorem verifyAlwaysDeniesOpt_eqv_verifyAlwaysDenies_ok {ps wps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps Γ = .ok cps →
  wellTypedPolicies ps Γ = .ok wps →
  verifyAlwaysDenies wps (SymEnv.ofTypeEnv Γ) ~ .ok (verifyAlwaysDeniesOpt cps)
:= by
  simp [verifyAlwaysDenies, verifyAlwaysDeniesOpt]
  intro hcps hwps
  apply verifyImpliesOpt_eqv_verifyImplies_ok hcps _ hwps _ (ps₂ := [])
  simp [CompiledPolicies.compile, Except.mapError, do_eq_ok, wellTypedPolicies_empty]
  rw [Opt.isAuthorized.correctness]
  simp [isAuthorized_empty, CompiledPolicies.denyAll, cps_compile_produces_the_right_env hcps]
  simp [footprints_empty, EmptyCollection.emptyCollection, Data.Set.map_empty]
  simp [wellTypedPolicies_empty]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyEquivalent` and `verifyEquivalentOpt` are
equivalent.
-/
theorem verifyEquivalentOpt_eqv_verifyEquivalent_ok {ps₁ ps₂ wps₁ wps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  wellTypedPolicies ps₁ Γ = .ok wps₁ →
  wellTypedPolicies ps₂ Γ = .ok wps₂ →
  verifyEquivalent wps₁ wps₂ (SymEnv.ofTypeEnv Γ) ~ .ok (verifyEquivalentOpt cps₁ cps₂)
:= by
  simp [verifyEquivalent, verifyEquivalentOpt]
  exact verifyIsAuthorizedOpt_eqv_verifyIsAuthorized_ok

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyDisjoint` and `verifyDisjointOpt` are
equivalent.
-/
theorem verifyDisjointOpt_eqv_verifyDisjoint_ok {ps₁ ps₂ wps₁ wps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  wellTypedPolicies ps₁ Γ = .ok wps₁ →
  wellTypedPolicies ps₂ Γ = .ok wps₂ →
  verifyDisjoint wps₁ wps₂ (SymEnv.ofTypeEnv Γ) ~ .ok (verifyDisjointOpt cps₁ cps₂)
:= by
  simp [verifyDisjoint, verifyDisjointOpt]
  exact verifyIsAuthorizedOpt_eqv_verifyIsAuthorized_ok
