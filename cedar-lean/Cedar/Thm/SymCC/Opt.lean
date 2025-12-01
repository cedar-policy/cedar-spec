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
import Cedar.Thm.SymCC.Opt.AllowDeny
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
compilation succeeds, then `verifyIsAuthorized` and `verifyIsAuthorizedOpt` are
equivalent.
-/
theorem verifyIsAuthorizedOpt_eqv_verifyIsAuthorized_ok {ps₁ ps₂ wps₁ wps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} {φ : Term → Term → Term} :
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  wellTypedPolicies ps₁ Γ = .ok wps₁ →
  wellTypedPolicies ps₂ Γ = .ok wps₂ →
  verifyIsAuthorized φ wps₁ wps₂ (SymEnv.ofTypeEnv Γ) = .ok (verifyIsAuthorizedOpt φ cps₁ cps₂)
:= by
  simp [verifyIsAuthorized, verifyIsAuthorizedOpt]
  simp [do_eq_ok]
  intro hcps₁ hcps₂ hwps₁ hwps₂
  simp [enforcePairCompiledPolicies_eqv_enforce_ok hcps₁ hcps₂ hwps₁ hwps₂]
  have henvs : cps₁.εnv = cps₂.εnv := by
    simp [cps_compile_produces_the_right_env hcps₁, cps_compile_produces_the_right_env hcps₂]
  simp [henvs]
  exists cps₁.term ; simp [cps_compile_produces_the_right_term hcps₁ hwps₁]
  exists cps₂.term ; simp [cps_compile_produces_the_right_term hcps₂ hwps₂]

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
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyAlwaysMatches` and `verifyAlwaysMatchesOpt` are
equivalent.
-/
theorem verifyAlwaysMatchesOpt_eqv_verifyAlwaysMatches_ok {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  verifyAlwaysMatches wp (SymEnv.ofTypeEnv Γ) = .ok (verifyAlwaysMatchesOpt cp)
:= by
  sorry

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyNeverMatches` and `verifyNeverMatchesOpt` are
equivalent.
-/
theorem verifyNeverMatchesOpt_eqv_verifyNeverMatches_ok {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  verifyNeverMatches wp (SymEnv.ofTypeEnv Γ) = .ok (verifyNeverMatchesOpt cp)
:= by
  sorry

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
  verifyImplies wps₁ wps₂ (SymEnv.ofTypeEnv Γ) = .ok (verifyImpliesOpt cps₁ cps₂)
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
  verifyAlwaysAllows wps (SymEnv.ofTypeEnv Γ) = .ok (verifyAlwaysAllowsOpt cps)
:= by
  simp [verifyAlwaysAllows, verifyAlwaysAllowsOpt]
  intro hcps hwps
  apply verifyImpliesOpt_eqv_verifyImplies_ok _ hcps (wellTypedPolicies_allowAll Γ) hwps
  simp [CompiledPolicies.compile, Except.mapError, do_eq_ok]
  simp [wellTypedPolicies_allowAll, isAuthorized_allowAll]
  simp [CompiledPolicies.allowAll, cps_compile_produces_the_right_env hcps]
  simp [footprints_singleton]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `verifyAlwaysAllows` and `verifyAlwaysAllowsOpt` are
equivalent.
-/
theorem verifyAlwaysDeniesOpt_eqv_verifyAlwaysDenies_ok {ps wps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps Γ = .ok cps →
  wellTypedPolicies ps Γ = .ok wps →
  verifyAlwaysDenies wps (SymEnv.ofTypeEnv Γ) = .ok (verifyAlwaysDeniesOpt cps)
:= by
  simp [verifyAlwaysDenies, verifyAlwaysDeniesOpt]
  intro hcps hwps
  apply verifyImpliesOpt_eqv_verifyImplies_ok hcps _ hwps _ (ps₂ := [])
  simp [CompiledPolicies.compile, Except.mapError, do_eq_ok]
  simp [wellTypedPolicies_empty, isAuthorized_empty]
  simp [CompiledPolicies.denyAll, cps_compile_produces_the_right_env hcps]
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
  verifyEquivalent wps₁ wps₂ (SymEnv.ofTypeEnv Γ) = .ok (verifyEquivalentOpt cps₁ cps₂)
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
  verifyDisjoint wps₁ wps₂ (SymEnv.ofTypeEnv Γ) = .ok (verifyDisjointOpt cps₁ cps₂)
:= by
  simp [verifyDisjoint, verifyDisjointOpt]
  exact verifyIsAuthorizedOpt_eqv_verifyIsAuthorized_ok

/--
If `SymCC.satisfiedPolicies` fails, that must be because `SymCC.compile` failed
with that error on some policy
-/
theorem satisfiedPolicies_eq_error {e : SymCC.Error} {effect : Effect} {ps : Policies} {εnv : SymEnv} :
  SymCC.satisfiedPolicies effect ps εnv = .error e →
  ∃ p ∈ ps, SymCC.compile p.toExpr εnv = .error e
:= by
  simp only [SymCC.satisfiedPolicies, do_error]
  intro h
  replace ⟨p, hp, h⟩ := List.filterMapM_error_implies_exists_error h
  exists p ; apply And.intro hp
  simp [compileWithEffect] at h
  split at h
  · simp [Functor.map, Except.map] at h
    split at h <;> simp at h
    subst h
    assumption
  · simp at h

/--
If `SymCC.isAuthorized` fails, that must be because `SymCC.compile` failed with
that error on some policy
-/
theorem isAuthorized_eq_error {e : SymCC.Error} {ps : Policies} {εnv : SymEnv} :
  SymCC.isAuthorized ps εnv = .error e →
  ∃ p ∈ ps, SymCC.compile p.toExpr εnv = .error e
:= by
  simp [SymCC.isAuthorized]
  cases h : SymCC.satisfiedPolicies .forbid ps εnv <;> simp
  case error e' => intro _ ; subst e' ; exact satisfiedPolicies_eq_error h
  case ok t => simp only [do_error] ; exact satisfiedPolicies_eq_error

/--
`CompiledPolicy.compile` succeeds iff `wellTypedPolicy` succeeds

Note: `Γ.WellFormed` is technically only required for the reverse direction
-/
theorem compile_ok_iff_welltypedpolicy_ok {p : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed → (
  Except.isOk (CompiledPolicy.compile p Γ) ↔
  Except.isOk (wellTypedPolicy p Γ)
  )
:= by
  simp [Except.isOk, Except.toBool]
  simp [CompiledPolicy.compile, Except.mapError]
  cases h₀ : wellTypedPolicy p Γ <;> simp
  case ok wp =>
    intro hwf
    have ⟨tx, htxwt, htx⟩ := wellTypedPolicy_ok_implies_well_typed_expr h₀
    have ⟨t, ht, _⟩ := compile_well_typed hwf htxwt
    simp_all

/--
`CompiledPolicies.compile` succeeds iff `wellTypedPolicies` succeeds

Note: `Γ.WellFormed` is technically only required for the reverse direction
-/
theorem compile_ok_iff_welltypedpolicies_ok {ps : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed → (
  Except.isOk (CompiledPolicies.compile ps Γ) ↔
  Except.isOk (wellTypedPolicies ps Γ)
  )
:= by
  simp [Except.isOk, Except.toBool]
  simp [CompiledPolicies.compile, Except.mapError]
  cases hwp : wellTypedPolicies ps Γ <;> simp
  case ok wps =>
    intro hwf
    split <;> simp
    rename_i e h
    simp [do_error] at h
    split at h <;> simp at h
    subst e
    rename_i e h
    simp [wellTypedPolicies] at hwp
    replace ⟨wp, hwp', h⟩ := isAuthorized_eq_error h
    replace ⟨p, hp, hwp⟩ := List.mapM_ok_implies_all_from_ok hwp wp hwp'
    have ⟨tx, htxwt, htx⟩ := wellTypedPolicy_ok_implies_well_typed_expr hwp
    have ⟨t, ht, _⟩ := compile_well_typed hwf htxwt
    simp_all

/--
If `CompiledPolicy.compile` succeeds, then `wellTypedPolicy` succeeds

Note: Can be proved without `Γ.WellFormed`
-/
theorem compile_ok_then_exists_wtp {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p Γ = .ok cp →
  ∃ wp, wellTypedPolicy p Γ = .ok wp
:= by
  intro hwf h₀
  have h₁ := (compile_ok_iff_welltypedpolicy_ok hwf).mp (by
    simp [Except.isOk_iff_exists]
    exists cp
  )
  simp [Except.isOk_iff_exists] at h₁
  exact h₁

/--
If `CompiledPolicies.compile` succeeds, then `wellTypedPolicies` succeeds

Note: Can be proved without `Γ.WellFormed`
-/
theorem compile_ok_then_exists_wtps {ps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps Γ = .ok cps →
  ∃ wps, wellTypedPolicies ps Γ = .ok wps
:= by
  intro hwf h₀
  have h₁ := (compile_ok_iff_welltypedpolicies_ok hwf).mp (by
    simp [Except.isOk_iff_exists]
    exists cps
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
  have ⟨wp, h₁⟩ := compile_ok_then_exists_wtp hwf h₀
  exists wp ; apply And.intro h₁
  have ⟨asserts, h₂⟩ := verifyNeverErrors_is_ok hwf h₁
  simp [h₂]
  simp [cp_compile_produces_the_right_env h₀]
  simp [compiled_policy_eq_wtp h₀ h₁]
  simp [verifyNeverErrorsOpt_eqv_verifyNeverErrors_ok h₀ h₁] at h₂
  subst asserts ; rfl

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `alwaysMatches?` and
`alwaysMatchesOpt?` are equivalent.
-/
theorem alwaysMatchesOpt?_eqv_alwaysMatches?_ok {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p Γ = .ok cp →
  ∃ wp,
    wellTypedPolicy p Γ = .ok wp ∧
    alwaysMatchesOpt? cp = alwaysMatches? wp (SymEnv.ofTypeEnv Γ)
:= by
  sorry

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `neverMatches?` and
`neverMatchesOpt?` are equivalent.
-/
theorem neverMatchesOpt?_eqv_neverMatches?_ok {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p Γ = .ok cp →
  ∃ wp,
    wellTypedPolicy p Γ = .ok wp ∧
    neverMatchesOpt? cp = neverMatches? wp (SymEnv.ofTypeEnv Γ)
:= by
  sorry

/--
Full equivalence for `neverErrors?` and `neverErrorsOpt?`, including both the
`.ok` and `.error` cases
-/
theorem neverErrorsOpt?_eqv_neverErrors? {p : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp ← CompiledPolicy.compile p Γ
    pure $ neverErrorsOpt? cp
  ) =
  (do
    let wp ← wellTypedPolicy p Γ |>.mapError .validationError
    pure $ neverErrors? wp (SymEnv.ofTypeEnv Γ)
  )
:= by
  cases hcp : CompiledPolicy.compile p Γ
  case ok cp =>
    intro hwf
    have ⟨wp, hwp, h⟩ := neverErrorsOpt?_eqv_neverErrors?_ok hwf hcp
    simp [Except.mapError, hwp, h]
  case error e =>
    simp [Except.mapError]
    cases hwp : wellTypedPolicy p Γ
    case error e' =>
      simp [CompiledPolicy.compile, Except.mapError, hwp] at hcp
      simp [hcp]
    case ok wp =>
      intro hwf
      have h := compile_ok_iff_welltypedpolicy_ok hwf (p := p)
      simp [hcp, hwp, Except.isOk, Except.toBool] at h

/--
Full equivalence for `alwaysMatches?` and `alwaysMatchesOpt?`, including both the
`.ok` and `.error` cases
-/
theorem alwaysMatchesOpt?_eqv_alwaysMatches? {p : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp ← CompiledPolicy.compile p Γ
    pure $ alwaysMatchesOpt? cp
  ) =
  (do
    let wp ← wellTypedPolicy p Γ |>.mapError .validationError
    pure $ alwaysMatches? wp (SymEnv.ofTypeEnv Γ)
  )
:= by
  sorry

/--
Full equivalence for `neverMatches?` and `neverMatchesOpt?`, including both the
`.ok` and `.error` cases
-/
theorem neverMatchesOpt?_eqv_neverMatches? {p : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp ← CompiledPolicy.compile p Γ
    pure $ neverMatchesOpt? cp
  ) =
  (do
    let wp ← wellTypedPolicy p Γ |>.mapError .validationError
    pure $ neverMatches? wp (SymEnv.ofTypeEnv Γ)
  )
:= by
  sorry

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `implies?` and
`impliesOpt?` are equivalent.
-/
theorem impliesOpt?_eqv_implies?_ok {ps₁ ps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    impliesOpt? cps₁ cps₂ = implies? wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [implies?, impliesOpt?]
  simp [sat?]
  intro hwf hcps₁ hcps₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcps₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcps₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyImplies_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  simp [cps_compile_produces_the_right_env hcps₁]
  simp [compiled_policies_eq_wtps hcps₁ hwps₁, compiled_policies_eq_wtps hcps₂ hwps₂]
  simp [verifyImpliesOpt_eqv_verifyImplies_ok hcps₁ hcps₂ hwps₁ hwps₂] at h₁
  subst asserts ; rfl

/--
Full equivalence for `implies?` and `impliesOpt?`, including both the
`.ok` and `.error` cases
-/
theorem impliesOpt?_eqv_implies? {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cps₁ ← CompiledPolicies.compile ps₁ Γ
    let cps₂ ← CompiledPolicies.compile ps₂ Γ
    pure $ impliesOpt? cps₁ cps₂
  ) =
  (do
    let wps₁ ← wellTypedPolicies ps₁ Γ |>.mapError .validationError
    let wps₂ ← wellTypedPolicies ps₂ Γ |>.mapError .validationError
    pure $ implies? wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₁)
  have h₂ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₂)
  cases hcps₁ : CompiledPolicies.compile ps₁ Γ
  <;> cases hcps₂ : CompiledPolicies.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicies.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cps₁ cps₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := impliesOpt?_eqv_implies?_ok hwf hcps₁ hcps₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₁] at hcps₁
    simp [hcps₁]
  case ok.error.ok.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₂] at hcps₂
    simp [hcps₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `alwaysAllows?` and
`alwaysAllowsOpt?` are equivalent.
-/
theorem alwaysAllowsOpt?_eqv_alwaysAllows?_ok {ps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps Γ = .ok cps →
  ∃ wps,
    wellTypedPolicies ps Γ = .ok wps ∧
    alwaysAllowsOpt? cps = alwaysAllows? wps (SymEnv.ofTypeEnv Γ)
:= by
  simp [alwaysAllows?, alwaysAllowsOpt?]
  simp [sat?]
  intro hwf hcps
  have ⟨wps, hwps⟩ := compile_ok_then_exists_wtps hwf hcps
  exists wps ; apply And.intro hwps
  have ⟨asserts, h₁⟩ := verifyAlwaysAllows_is_ok hwf hwps
  simp [h₁]
  simp [cps_compile_produces_the_right_env hcps]
  simp [compiled_policies_eq_wtps hcps hwps]
  simp [verifyAlwaysAllowsOpt_eqv_verifyAlwaysAllows_ok hcps hwps] at h₁
  subst asserts ; rfl

/--
Full equivalence for `alwaysAllows?` and `alwaysAllowsOpt?`, including both the
`.ok` and `.error` cases
-/
theorem alwaysAllowsOpt?_eqv_alwaysAllows? {ps : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cps ← CompiledPolicies.compile ps Γ
    pure $ alwaysAllowsOpt? cps
  ) =
  (do
    let wps ← wellTypedPolicies ps Γ |>.mapError .validationError
    pure $ alwaysAllows? wps (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps)
  cases hcps : CompiledPolicies.compile ps Γ
  <;> cases hwps : wellTypedPolicies ps Γ
  -- this eliminates all the cases where the behavior of CompiledPolicies.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok cps wps =>
    have ⟨wps', hwps', h⟩ := alwaysAllowsOpt?_eqv_alwaysAllows?_ok hwf hcps
    simp_all
  case error.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps] at hcps
    simp [hcps]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `alwaysDenies?` and
`alwaysDeniesOpt?` are equivalent.
-/
theorem alwaysDeniesOpt?_eqv_alwaysDenies?_ok {ps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps Γ = .ok cps →
  ∃ wps,
    wellTypedPolicies ps Γ = .ok wps ∧
    alwaysDeniesOpt? cps = alwaysDenies? wps (SymEnv.ofTypeEnv Γ)
:= by
  simp [alwaysDenies?, alwaysDeniesOpt?]
  simp [sat?]
  intro hwf hcps
  have ⟨wps, hwps⟩ := compile_ok_then_exists_wtps hwf hcps
  exists wps ; apply And.intro hwps
  have ⟨asserts, h₁⟩ := verifyAlwaysDenies_is_ok hwf hwps
  simp [h₁]
  simp [cps_compile_produces_the_right_env hcps]
  simp [compiled_policies_eq_wtps hcps hwps]
  simp [verifyAlwaysDeniesOpt_eqv_verifyAlwaysDenies_ok hcps hwps] at h₁
  subst asserts ; rfl

/--
Full equivalence for `alwaysDenies?` and `alwaysDeniesOpt?`, including both the
`.ok` and `.error` cases
-/
theorem alwaysDeniesOpt?_eqv_alwaysDenies? {ps : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cps ← CompiledPolicies.compile ps Γ
    pure $ alwaysDeniesOpt? cps
  ) =
  (do
    let wps ← wellTypedPolicies ps Γ |>.mapError .validationError
    pure $ alwaysDenies? wps (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps)
  cases hcps : CompiledPolicies.compile ps Γ
  <;> cases hwps : wellTypedPolicies ps Γ
  -- this eliminates all the cases where the behavior of CompiledPolicies.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok cps wps =>
    have ⟨wps', hwps', h⟩ := alwaysDeniesOpt?_eqv_alwaysDenies?_ok hwf hcps
    simp_all
  case error.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps] at hcps
    simp [hcps]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `equivalent?` and
`equivalentOpt?` are equivalent.
-/
theorem equivalentOpt?_eqv_equivalent?_ok {ps₁ ps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    equivalentOpt? cps₁ cps₂ = equivalent? wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [equivalent?, equivalentOpt?]
  simp [sat?]
  intro hwf hcps₁ hcps₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcps₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcps₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyEquivalent_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  simp [cps_compile_produces_the_right_env hcps₁]
  simp [compiled_policies_eq_wtps hcps₁ hwps₁, compiled_policies_eq_wtps hcps₂ hwps₂]
  simp [verifyEquivalentOpt_eqv_verifyEquivalent_ok hcps₁ hcps₂ hwps₁ hwps₂] at h₁
  subst asserts ; rfl

/--
Full equivalence for `equivalent?` and `equivalentOpt?`, including both the
`.ok` and `.error` cases
-/
theorem equivalentOpt?_eqv_equivalent? {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cps₁ ← CompiledPolicies.compile ps₁ Γ
    let cps₂ ← CompiledPolicies.compile ps₂ Γ
    pure $ equivalentOpt? cps₁ cps₂
  ) =
  (do
    let wps₁ ← wellTypedPolicies ps₁ Γ |>.mapError .validationError
    let wps₂ ← wellTypedPolicies ps₂ Γ |>.mapError .validationError
    pure $ equivalent? wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₁)
  have h₂ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₂)
  cases hcps₁ : CompiledPolicies.compile ps₁ Γ
  <;> cases hcps₂ : CompiledPolicies.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicies.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cps₁ cps₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := equivalentOpt?_eqv_equivalent?_ok hwf hcps₁ hcps₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₁] at hcps₁
    simp [hcps₁]
  case ok.error.ok.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₂] at hcps₂
    simp [hcps₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `disjoint?` and
`disjointOpt?` are equivalent.
-/
theorem disjointOpt?_eqv_disjoint?_ok {ps₁ ps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    disjointOpt? cps₁ cps₂ = disjoint? wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [disjoint?, disjointOpt?]
  simp [sat?]
  intro hwf hcps₁ hcps₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcps₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcps₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyDisjoint_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  simp [cps_compile_produces_the_right_env hcps₁]
  simp [compiled_policies_eq_wtps hcps₁ hwps₁, compiled_policies_eq_wtps hcps₂ hwps₂]
  simp [verifyDisjointOpt_eqv_verifyDisjoint_ok hcps₁ hcps₂ hwps₁ hwps₂] at h₁
  subst asserts ; rfl

/--
Full equivalence for `disjoint?` and `disjointOpt?`, including both the
`.ok` and `.error` cases
-/
theorem disjointOpt?_eqv_disjoint? {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cps₁ ← CompiledPolicies.compile ps₁ Γ
    let cps₂ ← CompiledPolicies.compile ps₂ Γ
    pure $ disjointOpt? cps₁ cps₂
  ) =
  (do
    let wps₁ ← wellTypedPolicies ps₁ Γ |>.mapError .validationError
    let wps₂ ← wellTypedPolicies ps₂ Γ |>.mapError .validationError
    pure $ disjoint? wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₁)
  have h₂ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₂)
  cases hcps₁ : CompiledPolicies.compile ps₁ Γ
  <;> cases hcps₂ : CompiledPolicies.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicies.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cps₁ cps₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := disjointOpt?_eqv_disjoint?_ok hwf hcps₁ hcps₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₁] at hcps₁
    simp [hcps₁]
  case ok.error.ok.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₂] at hcps₂
    simp [hcps₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkNeverErrors` and
`checkNeverErrorsOpt?` are equivalent.
-/
theorem checkNeverErrorsOpt_eqv_checkNeverErrors_ok {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p Γ = .ok cp →
  ∃ wp,
    wellTypedPolicy p Γ = .ok wp ∧
    checkNeverErrorsOpt cp = checkNeverErrors wp (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkNeverErrors, checkNeverErrorsOpt]
  simp [checkUnsat]
  intro hwf h₀
  have ⟨wp, h₁⟩ := compile_ok_then_exists_wtp hwf h₀
  exists wp ; apply And.intro h₁
  have ⟨asserts, h₂⟩ := verifyNeverErrors_is_ok hwf h₁
  simp [h₂]
  simp [cp_compile_produces_the_right_env h₀]
  simp [verifyNeverErrorsOpt_eqv_verifyNeverErrors_ok h₀ h₁] at h₂
  subst asserts ; rfl

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `checkAlwaysMatches` and
`checkAlwaysMatchesOpt` are equivalent.
-/
theorem checkAlwaysMatchesOpt_eqv_checkAlwaysMatches_ok {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p Γ = .ok cp →
  ∃ wp,
    wellTypedPolicy p Γ = .ok wp ∧
    checkAlwaysMatchesOpt cp = checkAlwaysMatches wp (SymEnv.ofTypeEnv Γ)
:= by
  sorry

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `checkNeverMatches` and
`checkNeverMatchesOpt` are equivalent.
-/
theorem checkNeverMatchesOpt_eqv_checkNeverMatches_ok {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p Γ = .ok cp →
  ∃ wp,
    wellTypedPolicy p Γ = .ok wp ∧
    checkNeverMatchesOpt cp = checkNeverMatches wp (SymEnv.ofTypeEnv Γ)
:= by
  sorry

/--
Full equivalence for checkNeverErrors` and `checkNeverErrorsOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkNeverErrorsOpt_eqv_checkNeverErrors {p : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp ← CompiledPolicy.compile p Γ
    pure $ checkNeverErrorsOpt cp
  ) =
  (do
    let wp ← wellTypedPolicy p Γ |>.mapError .validationError
    pure $ checkNeverErrors wp (SymEnv.ofTypeEnv Γ)
  )
:= by
  cases hcp : CompiledPolicy.compile p Γ
  case ok cp =>
    intro hwf
    have ⟨wp, hwp, h⟩ := checkNeverErrorsOpt_eqv_checkNeverErrors_ok hwf hcp
    simp [Except.mapError, hwp, h]
  case error e =>
    simp [Except.mapError]
    cases hwp : wellTypedPolicy p Γ
    case error e' =>
      simp [CompiledPolicy.compile, Except.mapError, hwp] at hcp
      simp [hcp]
    case ok wp =>
      intro hwf
      have h := compile_ok_iff_welltypedpolicy_ok hwf (p := p)
      simp [hcp, hwp, Except.isOk, Except.toBool] at h

/--
Full equivalence for `checkAlwaysMatches` and `checkAlwaysMatchesOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkAlwaysMatchesOpt_eqv_checkAlwaysMatches {p : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp ← CompiledPolicy.compile p Γ
    pure $ checkAlwaysMatchesOpt cp
  ) =
  (do
    let wp ← wellTypedPolicy p Γ |>.mapError .validationError
    pure $ checkAlwaysMatches wp (SymEnv.ofTypeEnv Γ)
  )
:= by
  sorry

/--
Full equivalence for `checkNeverMatches` and `checkNeverMatchesOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkNeverMatchesOpt_eqv_checkNeverMatches {p : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp ← CompiledPolicy.compile p Γ
    pure $ checkNeverMatchesOpt cp
  ) =
  (do
    let wp ← wellTypedPolicy p Γ |>.mapError .validationError
    pure $ checkNeverMatches wp (SymEnv.ofTypeEnv Γ)
  )
:= by
  sorry

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkImplies` and
`checkImpliesOpt` are equivalent.
-/
theorem checkImpliesOpt_eqv_checkImplies_ok {ps₁ ps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    checkImpliesOpt cps₁ cps₂ = checkImplies wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkImplies, checkImpliesOpt]
  simp [checkUnsat]
  intro hwf hcps₁ hcps₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcps₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcps₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyImplies_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  simp [cps_compile_produces_the_right_env hcps₁]
  simp [verifyImpliesOpt_eqv_verifyImplies_ok hcps₁ hcps₂ hwps₁ hwps₂] at h₁
  subst asserts ; rfl

/--
Full equivalence for `checkImplies` and `checkImpliesOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkImpliesOpt_eqv_checkImplies {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cps₁ ← CompiledPolicies.compile ps₁ Γ
    let cps₂ ← CompiledPolicies.compile ps₂ Γ
    pure $ checkImpliesOpt cps₁ cps₂
  ) =
  (do
    let wps₁ ← wellTypedPolicies ps₁ Γ |>.mapError .validationError
    let wps₂ ← wellTypedPolicies ps₂ Γ |>.mapError .validationError
    pure $ checkImplies wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₁)
  have h₂ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₂)
  cases hcps₁ : CompiledPolicies.compile ps₁ Γ
  <;> cases hcps₂ : CompiledPolicies.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicies.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cps₁ cps₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := checkImpliesOpt_eqv_checkImplies_ok hwf hcps₁ hcps₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₁] at hcps₁
    simp [hcps₁]
  case ok.error.ok.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₂] at hcps₂
    simp [hcps₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkAlwaysAllows` and
`checkAlwaysAllowsOpt` are equivalent.
-/
theorem checkAlwaysAllowsOpt_eqv_checkAlwaysAllows_ok {ps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps Γ = .ok cps →
  ∃ wps,
    wellTypedPolicies ps Γ = .ok wps ∧
    checkAlwaysAllowsOpt cps = checkAlwaysAllows wps (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkAlwaysAllows, checkAlwaysAllowsOpt]
  simp [checkUnsat]
  intro hwf hcps
  have ⟨wps, hwps⟩ := compile_ok_then_exists_wtps hwf hcps
  exists wps ; apply And.intro hwps
  have ⟨asserts, h₁⟩ := verifyAlwaysAllows_is_ok hwf hwps
  simp [h₁]
  simp [cps_compile_produces_the_right_env hcps]
  simp [verifyAlwaysAllowsOpt_eqv_verifyAlwaysAllows_ok hcps hwps] at h₁
  subst asserts ; rfl

/--
Full equivalence for `checkAlwaysAllows` and `checkAlwaysAllowsOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkAlwaysAllowsOpt_eqv_checkAlwaysAllows {ps : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cps ← CompiledPolicies.compile ps Γ
    pure $ checkAlwaysAllowsOpt cps
  ) =
  (do
    let wps ← wellTypedPolicies ps Γ |>.mapError .validationError
    pure $ checkAlwaysAllows wps (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps)
  cases hcps : CompiledPolicies.compile ps Γ
  <;> cases hwps : wellTypedPolicies ps Γ
  -- this eliminates all the cases where the behavior of CompiledPolicies.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok cps wps =>
    have ⟨wps', hwps', h⟩ := checkAlwaysAllowsOpt_eqv_checkAlwaysAllows_ok hwf hcps
    simp_all
  case error.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps] at hcps
    simp [hcps]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkAlwaysDenies` and
`checkAlwaysDeniesOpt` are equivalent.
-/
theorem checkAlwaysDeniesOpt_eqv_checkAlwaysDenies_ok {ps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps Γ = .ok cps →
  ∃ wps,
    wellTypedPolicies ps Γ = .ok wps ∧
    checkAlwaysDeniesOpt cps = checkAlwaysDenies wps (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkAlwaysDenies, checkAlwaysDeniesOpt]
  simp [checkUnsat]
  intro hwf hcps
  have ⟨wps, hwps⟩ := compile_ok_then_exists_wtps hwf hcps
  exists wps ; apply And.intro hwps
  have ⟨asserts, h₁⟩ := verifyAlwaysDenies_is_ok hwf hwps
  simp [h₁]
  simp [cps_compile_produces_the_right_env hcps]
  simp [verifyAlwaysDeniesOpt_eqv_verifyAlwaysDenies_ok hcps hwps] at h₁
  subst asserts ; rfl

/--
Full equivalence for `checkAlwaysDenies` and `checkAlwaysDeniesOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkAlwaysDeniesOpt_eqv_checkAlwaysDenies {ps : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cps ← CompiledPolicies.compile ps Γ
    pure $ checkAlwaysDeniesOpt cps
  ) =
  (do
    let wps ← wellTypedPolicies ps Γ |>.mapError .validationError
    pure $ checkAlwaysDenies wps (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps)
  cases hcps : CompiledPolicies.compile ps Γ
  <;> cases hwps : wellTypedPolicies ps Γ
  -- this eliminates all the cases where the behavior of CompiledPolicies.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok cps wps =>
    have ⟨wps', hwps', h⟩ := checkAlwaysDeniesOpt_eqv_checkAlwaysDenies_ok hwf hcps
    simp_all
  case error.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps] at hcps
    simp [hcps]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkEquivalent` and
`checkEquivalentOpt` are equivalent.
-/
theorem checkEquivalentOpt_eqv_checkEquivalent_ok {ps₁ ps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    checkEquivalentOpt cps₁ cps₂ = checkEquivalent wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkEquivalent, checkEquivalentOpt]
  simp [checkUnsat]
  intro hwf hcps₁ hcps₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcps₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcps₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyEquivalent_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  simp [cps_compile_produces_the_right_env hcps₁]
  simp [verifyEquivalentOpt_eqv_verifyEquivalent_ok hcps₁ hcps₂ hwps₁ hwps₂] at h₁
  subst asserts ; rfl

/--
Full equivalence for `checkEquivalent` and `checkEquivalentOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkEquivalentOpt_eqv_checkEquivalent {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cps₁ ← CompiledPolicies.compile ps₁ Γ
    let cps₂ ← CompiledPolicies.compile ps₂ Γ
    pure $ checkEquivalentOpt cps₁ cps₂
  ) =
  (do
    let wps₁ ← wellTypedPolicies ps₁ Γ |>.mapError .validationError
    let wps₂ ← wellTypedPolicies ps₂ Γ |>.mapError .validationError
    pure $ checkEquivalent wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₁)
  have h₂ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₂)
  cases hcps₁ : CompiledPolicies.compile ps₁ Γ
  <;> cases hcps₂ : CompiledPolicies.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicies.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cps₁ cps₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := checkEquivalentOpt_eqv_checkEquivalent_ok hwf hcps₁ hcps₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₁] at hcps₁
    simp [hcps₁]
  case ok.error.ok.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₂] at hcps₂
    simp [hcps₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkDisjoint` and
`checkDisjointOpt` are equivalent.
-/
theorem checkDisjointOpt_eqv_checkDisjoint_ok {ps₁ ps₂ : Policies} {cps₁ cps₂ : CompiledPolicies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicies.compile ps₁ Γ = .ok cps₁ →
  CompiledPolicies.compile ps₂ Γ = .ok cps₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    checkDisjointOpt cps₁ cps₂ = checkDisjoint wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkDisjoint, checkDisjointOpt]
  simp [checkUnsat]
  intro hwf hcps₁ hcps₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcps₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcps₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyDisjoint_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  simp [cps_compile_produces_the_right_env hcps₁]
  simp [verifyDisjointOpt_eqv_verifyDisjoint_ok hcps₁ hcps₂ hwps₁ hwps₂] at h₁
  subst asserts ; rfl

/--
Full equivalence for `checkDisjoint` and `checkDisjointOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkDisjointOpt_eqv_checkDisjoint {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cps₁ ← CompiledPolicies.compile ps₁ Γ
    let cps₂ ← CompiledPolicies.compile ps₂ Γ
    pure $ checkDisjointOpt cps₁ cps₂
  ) =
  (do
    let wps₁ ← wellTypedPolicies ps₁ Γ |>.mapError .validationError
    let wps₂ ← wellTypedPolicies ps₂ Γ |>.mapError .validationError
    pure $ checkDisjoint wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₁)
  have h₂ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps₂)
  cases hcps₁ : CompiledPolicies.compile ps₁ Γ
  <;> cases hcps₂ : CompiledPolicies.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicies.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cps₁ cps₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := checkDisjointOpt_eqv_checkDisjoint_ok hwf hcps₁ hcps₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₁] at hcps₁
    simp [hcps₁]
  case ok.error.ok.error =>
    simp [CompiledPolicies.compile, Except.mapError, hwps₂] at hcps₂
    simp [hcps₂]
