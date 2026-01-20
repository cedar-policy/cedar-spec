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
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.Data.Set
import Cedar.Thm.SymCC.Authorizer
import Cedar.Thm.SymCC.Opt.Asserts
import Cedar.Thm.SymCC.Opt.CompiledPolicies
import Cedar.Thm.SymCC.Opt.Extractor
import Cedar.Thm.SymCC.Opt.Verifier
import Cedar.Thm.WellTypedVerification

/-!
Proofs that the optimized interface in SymCCOpt is equivalent to the unoptimized
interface in SymCC.
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.SymCC

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
    rw [Opt.compile.correctness]
    have ⟨tx, htxwt, htx⟩ := wellTypedPolicy_ok_implies_well_typed_expr h₀
    have ⟨t, ht, _⟩ := compile_well_typed hwf htxwt
    simp_all

/--
`CompiledPolicySet.compile` succeeds iff `wellTypedPolicies` succeeds

Note: `Γ.WellFormed` is technically only required for the reverse direction
-/
theorem compile_ok_iff_welltypedpolicies_ok {ps : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed → (
  Except.isOk (CompiledPolicySet.compile ps Γ) ↔
  Except.isOk (wellTypedPolicies ps Γ)
  )
:= by
  simp [Except.isOk, Except.toBool]
  simp [CompiledPolicySet.compile, Except.mapError]
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
    rw [Opt.isAuthorized.correctness] at h
    simp only [do_error] at h
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
If `CompiledPolicySet.compile` succeeds, then `wellTypedPolicies` succeeds

Note: Can be proved without `Γ.WellFormed`
-/
theorem compile_ok_then_exists_wtps {ps : Policies} {cpset : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps Γ = .ok cpset →
  ∃ wps, wellTypedPolicies ps Γ = .ok wps
:= by
  intro hwf h₀
  have h₁ := (compile_ok_iff_welltypedpolicies_ok hwf).mp (by
    simp [Except.isOk_iff_exists]
    exists cpset
  )
  simp [Except.isOk_iff_exists] at h₁
  exact h₁

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation with `CompiledPolicy.compile` succeeds, then `satAsserts?` and
`satAssertsOpt?` are equivalent.
-/
theorem cp_satAssertsOpt?_eqv_satAsserts?_ok {ps wps : Policies} {cps : List CompiledPolicy} {Γ : Validation.TypeEnv} :
  ps.length = cps.length →
  cps ≠ [] →
  ps.mapM (CompiledPolicy.compile · Γ) = .ok cps →
  ps.mapM (wellTypedPolicy · Γ) = .ok wps →
  satAsserts? wps asserts (SymEnv.ofTypeEnv Γ) = satAssertsOpt? (cps.map CompiledPolicies.policy) asserts
:= by
  intro hlen
  simp [satAsserts?, satAssertsOpt?]
  intro hnil hcps hwps
  have hεnv : ∀ cp ∈ cps, cp.εnv = SymEnv.ofTypeEnv Γ := by
    intro cp hcp
    replace ⟨p, hp, hcps⟩ := List.mapM_ok_implies_all_from_ok hcps cp hcp
    exact cp_compile_produces_the_right_env hcps
  revert hnil
  cases cps <;> simp
  case cons cp cps =>
  cases ps <;> simp at *
  case cons p ps =>
  simp [do_eq_ok] at hwps hcps
  replace ⟨wp, hwp, hwps⟩ := hwps
  simp [Functor.map, Except.map] at hwps
  split at hwps <;> simp at hwps
  subst wps ; rename_i wps hwps
  replace ⟨cp', hcp', hcps⟩ := hcps
  simp [Functor.map, Except.map] at hcps
  split at hcps <;> simp at hcps
  replace ⟨hcps, htemp⟩ := hcps ; subst cp' htemp ; rename_i cps hcps ; have hcp := hcp' ; clear hcp'
  simp only [CompiledPolicies.εnv]
  rw [cp_compile_produces_the_right_env hcp]
  congr
  funext I
  cases I <;> simp only
  case some I =>
  suffices SymEnv.extract? ((wp :: wps).map Policy.toExpr) I (SymEnv.ofTypeEnv Γ) = extractOpt? (.policy cp :: cps.map CompiledPolicies.policy) I by rw [this] ; rfl
  rw [extractOpt?_eqv_extract? (εnv := cp.εnv) (by simp)]
  · congr 1
    · simp only [List.map_cons, List.flatMap_cons, CompiledPolicies.allPolicies,
        List.cons_append, List.nil_append, List.cons.injEq]
      simp only [flatMap_allPolicies_policy, List.map_map]
      simp only [cp_compile_produces_the_right_policy hcp hwp, true_and]
      rw [← List.forall₂_iff_map_eq]
      apply List.Forall₂.imp (R := λ a b => a = b.policy)
      · intro a b h ; subst a ; simp
      · rw [List.mapM_ok_iff_forall₂] at hcps hwps
        apply List.forall₂_trans_ish hwps hcps
        intro p wp cp hwp hcp
        exact (cp_compile_produces_the_right_policy hcp hwp).symm
    · simp [cp_compile_produces_the_right_env hcp]
  · intro cps' hcps'
    cases hcps'
    · rfl
    · rename_i hcps'
      change cps' ∈ cps.map CompiledPolicies.policy at hcps'
      simp only [List.mem_map] at hcps'
      replace ⟨cp', hcp', hcps'⟩ := hcps' ; subst cps'
      replace ⟨hεnv, hεnv'⟩ := hεnv
      simp [CompiledPolicies.εnv, hεnv, hεnv' cp' hcp']
  · intro cps' hcps'
    cases hcps'
    · exists p, Γ
    · rename_i hcps'
      change cps' ∈ cps.map CompiledPolicies.policy at hcps'
      simp only [List.mem_map] at hcps'
      replace ⟨cp', hcp', hcps'⟩ := hcps' ; subst cps'
      simp only
      replace ⟨p', hp', hcps⟩ := List.mapM_ok_implies_all_from_ok hcps cp' hcp'
      exists p', Γ

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation with `CompiledPolicySet.compile` succeeds, then `satAsserts?` and
`satAssertsOpt?` are equivalent.
-/
theorem cpset_satAssertsOpt?_eqv_satAsserts?_ok {pss wpss : List Policies} {cpsets : List CompiledPolicySet} {Γ : Validation.TypeEnv} :
  pss.length = cpsets.length →
  cpsets ≠ [] →
  pss.mapM (CompiledPolicySet.compile · Γ) = .ok cpsets →
  pss.mapM (wellTypedPolicies · Γ) = .ok wpss →
  satAsserts? wpss.flatten asserts (SymEnv.ofTypeEnv Γ) = satAssertsOpt? (cpsets.map CompiledPolicies.pset) asserts
:= by
  intro hlen
  simp [satAsserts?, satAssertsOpt?]
  intro hnil hcpsets hwpss
  have hεnv : ∀ cpset ∈ cpsets, cpset.εnv = SymEnv.ofTypeEnv Γ := by
    intro cpset hcpset
    replace ⟨ps, hps, hcpsets⟩ := List.mapM_ok_implies_all_from_ok hcpsets cpset hcpset
    exact cpset_compile_produces_the_right_env hcpsets
  revert hnil
  cases cpsets <;> simp
  case cons cpset cpsets =>
  cases pss <;> simp at *
  case cons ps pss =>
  simp [do_eq_ok] at hwpss hcpsets
  replace ⟨wps, hwps, hwpss⟩ := hwpss
  simp [Functor.map, Except.map] at hwpss
  split at hwpss <;> simp at hwpss
  subst wpss ; rename_i wpss hwpss
  replace ⟨cpset', hcpset', hcpsets⟩ := hcpsets
  simp [Functor.map, Except.map] at hcpsets
  split at hcpsets <;> simp at hcpsets
  replace ⟨hcpsets, htemp⟩ := hcpsets ; subst cpset' htemp ; rename_i cpsets hcpsets ; have hcpset := hcpset' ; clear hcpset'
  simp only [CompiledPolicies.εnv]
  rw [cpset_compile_produces_the_right_env hcpset]
  congr
  funext I
  cases I <;> simp only
  case some I =>
  suffices SymEnv.extract? (List.map (List.map Policy.toExpr) (wps :: wpss)).flatten I (SymEnv.ofTypeEnv Γ) = extractOpt? (.pset cpset :: cpsets.map CompiledPolicies.pset) I by rw [this] ; rfl
  rw [extractOpt?_eqv_extract? (εnv := cpset.εnv) (by simp)]
  · congr 1
    · simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, CompiledPolicies.allPolicies,
        List.map_append]
      simp only [flatMap_allPolicies_policies]
      congr 2
      · simp [cpset_compile_produces_the_right_policies hcpset hwps]
      · simp [List.flatMap]
        congr 1
        rw [← List.forall₂_iff_map_eq]
        apply List.Forall₂.imp (R := λ a b => a = CompiledPolicySet.policies b)
        · intro a b h ; subst h ; simp
        · rw [List.mapM_ok_iff_forall₂] at hcpsets hwpss
          apply List.forall₂_trans_ish hwpss hcpsets
          intro ps wps cpset hwps hcpset
          exact (cpset_compile_produces_the_right_policies hcpset hwps).symm
    · simp [cpset_compile_produces_the_right_env hcpset]
  · intro cps hcps
    cases hcps
    · rfl
    · rename_i hcps
      change cps ∈ cpsets.map CompiledPolicies.pset at hcps
      simp only [List.mem_map] at hcps
      replace ⟨cpset', hcpset', hcps⟩ := hcps ; subst cps
      replace ⟨hεnv, hεnv'⟩ := hεnv
      simp [CompiledPolicies.εnv, hεnv, hεnv' cpset' hcpset']
  · intro cps hcps
    cases hcps
    · exists ps, Γ
    · rename_i hcps
      change cps ∈ cpsets.map CompiledPolicies.pset at hcps
      simp only [List.mem_map] at hcps
      replace ⟨cpset', hcpset', hcps⟩ := hcps ; subst cps
      replace ⟨ps', hps', hcpsets⟩ := List.mapM_ok_implies_all_from_ok hcpsets cpset' hcpset'
      exists ps', Γ

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
  rw [cp_satAssertsOpt?_eqv_satAsserts?_ok (ps := [p]) (cps := [cp]) (by simp) (by simp)]
  · have := verifyNeverErrorsOpt_eqv_verifyNeverErrors_ok h₀ h₁
    simp [h₂, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.policy cp] (Asserts.Equiv.symm this)
  · simp [h₀]
  · simp [h₁]

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
  simp [alwaysMatches?, alwaysMatchesOpt?]
  simp [sat?]
  intro hwf h₀
  have ⟨wp, h₁⟩ := compile_ok_then_exists_wtp hwf h₀
  exists wp ; apply And.intro h₁
  have ⟨asserts, h₂⟩ := verifyAlwaysMatches_is_ok hwf h₁
  simp [h₂]
  rw [cp_satAssertsOpt?_eqv_satAsserts?_ok (ps := [p]) (cps := [cp]) (by simp) (by simp)]
  · have := verifyAlwaysMatchesOpt_eqv_verifyAlwaysMatches_ok h₀ h₁
    simp [h₂, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.policy cp] (Asserts.Equiv.symm this)
  · simp [h₀]
  · simp [h₁]

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
  simp [neverMatches?, neverMatchesOpt?]
  simp [sat?]
  intro hwf h₀
  have ⟨wp, h₁⟩ := compile_ok_then_exists_wtp hwf h₀
  exists wp ; apply And.intro h₁
  have ⟨asserts, h₂⟩ := verifyNeverMatches_is_ok hwf h₁
  simp [h₂]
  rw [cp_satAssertsOpt?_eqv_satAsserts?_ok (ps := [p]) (cps := [cp]) (by simp) (by simp)]
  · have := verifyNeverMatchesOpt_eqv_verifyNeverMatches_ok h₀ h₁
    simp [h₂, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.policy cp] (Asserts.Equiv.symm this)
  · simp [h₀]
  · simp [h₁]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `matchesEquivalent?` and
`matchesEquivalentOpt?` are equivalent.
-/
theorem matchesEquivalentOpt?_eqv_matchesEquivalent?_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  matchesEquivalentOpt? cp₁ cp₂ = matchesEquivalent? wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp only [matchesEquivalent?, matchesEquivalentOpt?]
  simp only [sat?]
  intro hwf h₀ h₁ h₂ h₃
  have ⟨asserts, h₄⟩ := verifyMatchesEquivalent_is_ok hwf h₂ h₃
  simp only [h₄]
  rw [cp_satAssertsOpt?_eqv_satAsserts?_ok (ps := [p₁, p₂]) (cps := [cp₁, cp₂]) (by simp) (by simp)]
  · have := verifyMatchesEquivalentOpt_eqv_verifyMatchesEquivalent_ok h₀ h₁ h₂ h₃
    simp [h₄, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.policy cp₁, .policy cp₂] (Asserts.Equiv.symm this)
  · simp [h₀, h₁]
  · simp [h₂, h₃]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `matchesImplies?` and
`matchesImpliesOpt?` are equivalent.
-/
theorem matchesImpliesOpt?_eqv_matchesImplies?_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  matchesImpliesOpt? cp₁ cp₂ = matchesImplies? wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp only [matchesImplies?, matchesImpliesOpt?]
  simp only [sat?]
  intro hwf h₀ h₁ h₂ h₃
  have ⟨asserts, h₄⟩ := verifyMatchesImplies_is_ok hwf h₂ h₃
  simp only [h₄]
  rw [cp_satAssertsOpt?_eqv_satAsserts?_ok (ps := [p₁, p₂]) (cps := [cp₁, cp₂]) (by simp) (by simp)]
  · have := verifyMatchesImpliesOpt_eqv_verifyMatchesImplies_ok h₀ h₁ h₂ h₃
    simp [h₄, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.policy cp₁, .policy cp₂] (Asserts.Equiv.symm this)
  · simp [h₀, h₁]
  · simp [h₂, h₃]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `matchesDisjoint?` and
`matchesDisjointOpt?` are equivalent.
-/
theorem matchesDisjointOpt?_eqv_matchesDisjoint?_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  matchesDisjointOpt? cp₁ cp₂ = matchesDisjoint? wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp only [matchesDisjoint?, matchesDisjointOpt?]
  simp only [sat?]
  intro hwf h₀ h₁ h₂ h₃
  have ⟨asserts, h₄⟩ := verifyMatchesDisjoint_is_ok hwf h₂ h₃
  simp only [h₄]
  rw [cp_satAssertsOpt?_eqv_satAsserts?_ok (ps := [p₁, p₂]) (cps := [cp₁, cp₂]) (by simp) (by simp)]
  · have := verifyMatchesDisjointOpt_eqv_verifyMatchesDisjoint_ok h₀ h₁ h₂ h₃
    simp [h₄, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.policy cp₁, .policy cp₂] (Asserts.Equiv.symm this)
  · simp [h₀, h₁]
  · simp [h₂, h₃]

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
  cases hcp : CompiledPolicy.compile p Γ
  case ok cp =>
    intro hwf
    have ⟨wp, hwp, h⟩ := alwaysMatchesOpt?_eqv_alwaysMatches?_ok hwf hcp
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
  cases hcp : CompiledPolicy.compile p Γ
  case ok cp =>
    intro hwf
    have ⟨wp, hwp, h⟩ := neverMatchesOpt?_eqv_neverMatches?_ok hwf hcp
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
Full equivalence for `matchesEquivalent?` and `matchesEquivalentOpt?`, including both the
`.ok` and `.error` cases
-/
theorem matchesEquivalentOpt?_eqv_matchesEquivalent? {p₁ p₂ : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp₁ ← CompiledPolicy.compile p₁ Γ
    let cp₂ ← CompiledPolicy.compile p₂ Γ
    pure $ matchesEquivalentOpt? cp₁ cp₂
  ) =
  (do
    let wp₁ ← wellTypedPolicy p₁ Γ |>.mapError .validationError
    let wp₂ ← wellTypedPolicy p₂ Γ |>.mapError .validationError
    pure $ matchesEquivalent? wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₁)
  have h₂ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₂)
  cases hcp₁ : CompiledPolicy.compile p₁ Γ
  <;> cases hcp₂ : CompiledPolicy.compile p₂ Γ
  <;> cases hwp₁ : wellTypedPolicy p₁ Γ
  <;> cases hwp₂ : wellTypedPolicy p₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicy.compile is inconsistent
  -- with the behavior of wellTypedPolicy on the same policy
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cp₁ cp₂ wp₁ wp₂ =>
    exact matchesEquivalentOpt?_eqv_matchesEquivalent?_ok hwf hcp₁ hcp₂ hwp₁ hwp₂
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₁] at hcp₁
    simp [hcp₁]
  case ok.error.ok.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₂] at hcp₂
    simp [hcp₂]

/--
Full equivalence for `matchesImplies?` and `matchesImpliesOpt?`, including both the
`.ok` and `.error` cases
-/
theorem matchesImpliesOpt?_eqv_matchesImplies? {p₁ p₂ : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp₁ ← CompiledPolicy.compile p₁ Γ
    let cp₂ ← CompiledPolicy.compile p₂ Γ
    pure $ matchesImpliesOpt? cp₁ cp₂
  ) =
  (do
    let wp₁ ← wellTypedPolicy p₁ Γ |>.mapError .validationError
    let wp₂ ← wellTypedPolicy p₂ Γ |>.mapError .validationError
    pure $ matchesImplies? wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₁)
  have h₂ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₂)
  cases hcp₁ : CompiledPolicy.compile p₁ Γ
  <;> cases hcp₂ : CompiledPolicy.compile p₂ Γ
  <;> cases hwp₁ : wellTypedPolicy p₁ Γ
  <;> cases hwp₂ : wellTypedPolicy p₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicy.compile is inconsistent
  -- with the behavior of wellTypedPolicy on the same policy
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cp₁ cp₂ wp₁ wp₂ =>
    exact matchesImpliesOpt?_eqv_matchesImplies?_ok hwf hcp₁ hcp₂ hwp₁ hwp₂
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₁] at hcp₁
    simp [hcp₁]
  case ok.error.ok.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₂] at hcp₂
    simp [hcp₂]

/--
Full equivalence for `matchesDisjoint?` and `matchesDisjointOpt?`, including both the
`.ok` and `.error` cases
-/
theorem matchesDisjointOpt?_eqv_matchesDisjoint? {p₁ p₂ : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp₁ ← CompiledPolicy.compile p₁ Γ
    let cp₂ ← CompiledPolicy.compile p₂ Γ
    pure $ matchesDisjointOpt? cp₁ cp₂
  ) =
  (do
    let wp₁ ← wellTypedPolicy p₁ Γ |>.mapError .validationError
    let wp₂ ← wellTypedPolicy p₂ Γ |>.mapError .validationError
    pure $ matchesDisjoint? wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₁)
  have h₂ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₂)
  cases hcp₁ : CompiledPolicy.compile p₁ Γ
  <;> cases hcp₂ : CompiledPolicy.compile p₂ Γ
  <;> cases hwp₁ : wellTypedPolicy p₁ Γ
  <;> cases hwp₂ : wellTypedPolicy p₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicy.compile is inconsistent
  -- with the behavior of wellTypedPolicy on the same policy
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cp₁ cp₂ wp₁ wp₂ =>
    exact matchesDisjointOpt?_eqv_matchesDisjoint?_ok hwf hcp₁ hcp₂ hwp₁ hwp₂
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₁] at hcp₁
    simp [hcp₁]
  case ok.error.ok.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₂] at hcp₂
    simp [hcp₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `implies?` and
`impliesOpt?` are equivalent.
-/
theorem impliesOpt?_eqv_implies?_ok {ps₁ ps₂ : Policies} {cpset₁ cpset₂ : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps₁ Γ = .ok cpset₁ →
  CompiledPolicySet.compile ps₂ Γ = .ok cpset₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    impliesOpt? cpset₁ cpset₂ = implies? wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [implies?, impliesOpt?]
  simp [sat?]
  intro hwf hcpset₁ hcpset₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcpset₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcpset₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyImplies_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  have := cpset_satAssertsOpt?_eqv_satAsserts?_ok (pss := [ps₁, ps₂]) (wpss := [wps₁, wps₂]) (cpsets := [cpset₁, cpset₂]) (asserts := asserts) (Γ := Γ) (by simp) (by simp)
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons, List.map_nil] at this
  rw [this] ; clear this
  · have := verifyImpliesOpt_eqv_verifyImplies_ok hcpset₁ hcpset₂ hwps₁ hwps₂
    simp [h₁, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.pset cpset₁, .pset cpset₂] (Asserts.Equiv.symm this)
  · simp [hcpset₁, hcpset₂]
  · simp [hwps₁, hwps₂]

/--
Full equivalence for `implies?` and `impliesOpt?`, including both the
`.ok` and `.error` cases
-/
theorem impliesOpt?_eqv_implies? {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cpset₁ ← CompiledPolicySet.compile ps₁ Γ
    let cpset₂ ← CompiledPolicySet.compile ps₂ Γ
    pure $ impliesOpt? cpset₁ cpset₂
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
  cases hcpset₁ : CompiledPolicySet.compile ps₁ Γ
  <;> cases hcpset₂ : CompiledPolicySet.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicySet.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cpset₁ cpset₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := impliesOpt?_eqv_implies?_ok hwf hcpset₁ hcpset₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₁] at hcpset₁
    simp [hcpset₁]
  case ok.error.ok.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₂] at hcpset₂
    simp [hcpset₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `alwaysAllows?` and
`alwaysAllowsOpt?` are equivalent.
-/
theorem alwaysAllowsOpt?_eqv_alwaysAllows?_ok {ps : Policies} {cpset : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps Γ = .ok cpset →
  ∃ wps,
    wellTypedPolicies ps Γ = .ok wps ∧
    alwaysAllowsOpt? cpset = alwaysAllows? wps (SymEnv.ofTypeEnv Γ)
:= by
  simp [alwaysAllows?, alwaysAllowsOpt?]
  simp [sat?]
  intro hwf hcpset
  have ⟨wps, hwps⟩ := compile_ok_then_exists_wtps hwf hcpset
  exists wps ; apply And.intro hwps
  have ⟨asserts, h₁⟩ := verifyAlwaysAllows_is_ok hwf hwps
  simp [h₁]
  have := cpset_satAssertsOpt?_eqv_satAsserts?_ok (pss := [ps]) (wpss := [wps]) (cpsets := [cpset]) (asserts := asserts) (Γ := Γ) (by simp) (by simp)
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons, List.map_nil] at this
  rw [this] ; clear this
  · have := verifyAlwaysAllowsOpt_eqv_verifyAlwaysAllows_ok hcpset hwps
    simp [h₁, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.pset cpset] (Asserts.Equiv.symm this)
  · simp [hcpset]
  · simp [hwps]

/--
Full equivalence for `alwaysAllows?` and `alwaysAllowsOpt?`, including both the
`.ok` and `.error` cases
-/
theorem alwaysAllowsOpt?_eqv_alwaysAllows? {ps : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cpset ← CompiledPolicySet.compile ps Γ
    pure $ alwaysAllowsOpt? cpset
  ) =
  (do
    let wps ← wellTypedPolicies ps Γ |>.mapError .validationError
    pure $ alwaysAllows? wps (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps)
  cases hcpset : CompiledPolicySet.compile ps Γ
  <;> cases hwps : wellTypedPolicies ps Γ
  -- this eliminates all the cases where the behavior of CompiledPolicySet.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok cpset wps =>
    have ⟨wps', hwps', h⟩ := alwaysAllowsOpt?_eqv_alwaysAllows?_ok hwf hcpset
    simp_all
  case error.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps] at hcpset
    simp [hcpset]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `alwaysDenies?` and
`alwaysDeniesOpt?` are equivalent.
-/
theorem alwaysDeniesOpt?_eqv_alwaysDenies?_ok {ps : Policies} {cpset : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps Γ = .ok cpset →
  ∃ wps,
    wellTypedPolicies ps Γ = .ok wps ∧
    alwaysDeniesOpt? cpset = alwaysDenies? wps (SymEnv.ofTypeEnv Γ)
:= by
  simp [alwaysDenies?, alwaysDeniesOpt?]
  simp [sat?]
  intro hwf hcpset
  have ⟨wps, hwps⟩ := compile_ok_then_exists_wtps hwf hcpset
  exists wps ; apply And.intro hwps
  have ⟨asserts, h₁⟩ := verifyAlwaysDenies_is_ok hwf hwps
  simp [h₁]
  have := cpset_satAssertsOpt?_eqv_satAsserts?_ok (pss := [ps]) (wpss := [wps]) (cpsets := [cpset]) (asserts := asserts) (Γ := Γ) (by simp) (by simp)
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons, List.map_nil] at this
  rw [this] ; clear this
  · have := verifyAlwaysDeniesOpt_eqv_verifyAlwaysDenies_ok hcpset hwps
    simp [h₁, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.pset cpset] (Asserts.Equiv.symm this)
  · simp [hcpset]
  · simp [hwps]

/--
Full equivalence for `alwaysDenies?` and `alwaysDeniesOpt?`, including both the
`.ok` and `.error` cases
-/
theorem alwaysDeniesOpt?_eqv_alwaysDenies? {ps : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cpset ← CompiledPolicySet.compile ps Γ
    pure $ alwaysDeniesOpt? cpset
  ) =
  (do
    let wps ← wellTypedPolicies ps Γ |>.mapError .validationError
    pure $ alwaysDenies? wps (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps)
  cases hcpset : CompiledPolicySet.compile ps Γ
  <;> cases hwps : wellTypedPolicies ps Γ
  -- this eliminates all the cases where the behavior of CompiledPolicySet.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok cpset wps =>
    have ⟨wps', hwps', h⟩ := alwaysDeniesOpt?_eqv_alwaysDenies?_ok hwf hcpset
    simp_all
  case error.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps] at hcpset
    simp [hcpset]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `equivalent?` and
`equivalentOpt?` are equivalent.
-/
theorem equivalentOpt?_eqv_equivalent?_ok {ps₁ ps₂ : Policies} {cpset₁ cpset₂ : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps₁ Γ = .ok cpset₁ →
  CompiledPolicySet.compile ps₂ Γ = .ok cpset₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    equivalentOpt? cpset₁ cpset₂ = equivalent? wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [equivalent?, equivalentOpt?]
  simp [sat?]
  intro hwf hcpset₁ hcpset₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcpset₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcpset₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyEquivalent_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  have := cpset_satAssertsOpt?_eqv_satAsserts?_ok (pss := [ps₁, ps₂]) (wpss := [wps₁, wps₂]) (cpsets := [cpset₁, cpset₂]) (asserts := asserts) (Γ := Γ) (by simp) (by simp)
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons, List.map_nil] at this
  rw [this] ; clear this
  · have := verifyEquivalentOpt_eqv_verifyEquivalent_ok hcpset₁ hcpset₂ hwps₁ hwps₂
    simp [h₁, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.pset cpset₁, .pset cpset₂] (Asserts.Equiv.symm this)
  · simp [hcpset₁, hcpset₂]
  · simp [hwps₁, hwps₂]

/--
Full equivalence for `equivalent?` and `equivalentOpt?`, including both the
`.ok` and `.error` cases
-/
theorem equivalentOpt?_eqv_equivalent? {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cpset₁ ← CompiledPolicySet.compile ps₁ Γ
    let cpset₂ ← CompiledPolicySet.compile ps₂ Γ
    pure $ equivalentOpt? cpset₁ cpset₂
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
  cases hcpset₁ : CompiledPolicySet.compile ps₁ Γ
  <;> cases hcpset₂ : CompiledPolicySet.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicySet.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cpset₁ cpset₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := equivalentOpt?_eqv_equivalent?_ok hwf hcpset₁ hcpset₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₁] at hcpset₁
    simp [hcpset₁]
  case ok.error.ok.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₂] at hcpset₂
    simp [hcpset₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `disjoint?` and
`disjointOpt?` are equivalent.
-/
theorem disjointOpt?_eqv_disjoint?_ok {ps₁ ps₂ : Policies} {cpset₁ cpset₂ : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps₁ Γ = .ok cpset₁ →
  CompiledPolicySet.compile ps₂ Γ = .ok cpset₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    disjointOpt? cpset₁ cpset₂ = disjoint? wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [disjoint?, disjointOpt?]
  simp [sat?]
  intro hwf hcpset₁ hcpset₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcpset₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcpset₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyDisjoint_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  have := cpset_satAssertsOpt?_eqv_satAsserts?_ok (pss := [ps₁, ps₂]) (wpss := [wps₁, wps₂]) (cpsets := [cpset₁, cpset₂]) (asserts := asserts) (Γ := Γ) (by simp) (by simp)
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons, List.map_nil] at this
  rw [this] ; clear this
  · have := verifyDisjointOpt_eqv_verifyDisjoint_ok hcpset₁ hcpset₂ hwps₁ hwps₂
    simp [h₁, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAssertsOpt? [.pset cpset₁, .pset cpset₂] (Asserts.Equiv.symm this)
  · simp [hcpset₁, hcpset₂]
  · simp [hwps₁, hwps₂]

/--
Full equivalence for `disjoint?` and `disjointOpt?`, including both the
`.ok` and `.error` cases
-/
theorem disjointOpt?_eqv_disjoint? {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cpset₁ ← CompiledPolicySet.compile ps₁ Γ
    let cpset₂ ← CompiledPolicySet.compile ps₂ Γ
    pure $ disjointOpt? cpset₁ cpset₂
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
  cases hcpset₁ : CompiledPolicySet.compile ps₁ Γ
  <;> cases hcpset₂ : CompiledPolicySet.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicySet.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cpset₁ cpset₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := disjointOpt?_eqv_disjoint?_ok hwf hcpset₁ hcpset₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₁] at hcpset₁
    simp [hcpset₁]
  case ok.error.ok.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₂] at hcpset₂
    simp [hcpset₂]

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
  have := verifyNeverErrorsOpt_eqv_verifyNeverErrors_ok h₀ h₁
  simp [h₂, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

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
  simp [checkAlwaysMatches, checkAlwaysMatchesOpt]
  simp [checkUnsat]
  intro hwf h₀
  have ⟨wp, h₁⟩ := compile_ok_then_exists_wtp hwf h₀
  exists wp ; apply And.intro h₁
  have ⟨asserts, h₂⟩ := verifyAlwaysMatches_is_ok hwf h₁
  simp [h₂]
  simp [cp_compile_produces_the_right_env h₀]
  have := verifyAlwaysMatchesOpt_eqv_verifyAlwaysMatches_ok h₀ h₁
  simp [h₂, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

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
  simp [checkNeverMatches, checkNeverMatchesOpt]
  simp [checkUnsat]
  intro hwf h₀
  have ⟨wp, h₁⟩ := compile_ok_then_exists_wtp hwf h₀
  exists wp ; apply And.intro h₁
  have ⟨asserts, h₂⟩ := verifyNeverMatches_is_ok hwf h₁
  simp [h₂]
  simp [cp_compile_produces_the_right_env h₀]
  have := verifyNeverMatchesOpt_eqv_verifyNeverMatches_ok h₀ h₁
  simp [h₂, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `checkMatchesEquivalent` and
`checkMatchesEquivalentOpt` are equivalent.
-/
theorem checkMatchesEquivalentOpt_eqv_checkMatchesEquivalent_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  checkMatchesEquivalentOpt cp₁ cp₂ = checkMatchesEquivalent wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkMatchesEquivalent, checkMatchesEquivalentOpt]
  simp [checkUnsat]
  intro hwf h₀ h₁ h₂ h₃
  have ⟨asserts, h₄⟩ := verifyMatchesEquivalent_is_ok hwf h₂ h₃
  simp [h₄]
  simp [cp_compile_produces_the_right_env h₀]
  have := verifyMatchesEquivalentOpt_eqv_verifyMatchesEquivalent_ok h₀ h₁ h₂ h₃
  simp [h₄, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `checkMatchesImplies` and
`checkMatchesImpliesOpt` are equivalent.
-/
theorem checkMatchesImpliesOpt_eqv_checkMatchesImplies_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  checkMatchesImpliesOpt cp₁ cp₂ = checkMatchesImplies wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkMatchesImplies, checkMatchesImpliesOpt]
  simp [checkUnsat]
  intro hwf h₀ h₁ h₂ h₃
  have ⟨asserts, h₄⟩ := verifyMatchesImplies_is_ok hwf h₂ h₃
  simp [h₄]
  simp [cp_compile_produces_the_right_env h₀]
  have := verifyMatchesImpliesOpt_eqv_verifyMatchesImplies_ok h₀ h₁ h₂ h₃
  simp [h₄, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicy` succeeds and `checkMatchesDisjoint` and
`checkMatchesDisjointOpt` are equivalent.
-/
theorem checkMatchesDisjointOpt_eqv_checkMatchesDisjoint_ok {p₁ p₂ wp₁ wp₂ : Policy} {cp₁ cp₂ : CompiledPolicy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicy.compile p₁ Γ = .ok cp₁ →
  CompiledPolicy.compile p₂ Γ = .ok cp₂ →
  wellTypedPolicy p₁ Γ = .ok wp₁ →
  wellTypedPolicy p₂ Γ = .ok wp₂ →
  checkMatchesDisjointOpt cp₁ cp₂ = checkMatchesDisjoint wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkMatchesDisjoint, checkMatchesDisjointOpt]
  simp [checkUnsat]
  intro hwf h₀ h₁ h₂ h₃
  have ⟨asserts, h₄⟩ := verifyMatchesDisjoint_is_ok hwf h₂ h₃
  simp [h₄]
  simp [cp_compile_produces_the_right_env h₀]
  have := verifyMatchesDisjointOpt_eqv_verifyMatchesDisjoint_ok h₀ h₁ h₂ h₃
  simp [h₄, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

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
  cases hcp : CompiledPolicy.compile p Γ
  case ok cp =>
    intro hwf
    have ⟨wp, hwp, h⟩ := checkAlwaysMatchesOpt_eqv_checkAlwaysMatches_ok hwf hcp
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
  cases hcp : CompiledPolicy.compile p Γ
  case ok cp =>
    intro hwf
    have ⟨wp, hwp, h⟩ := checkNeverMatchesOpt_eqv_checkNeverMatches_ok hwf hcp
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
Full equivalence for `checkMatchesEquivalent` and `checkMatchesEquivalentOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkMatchesEquivalentOpt_eqv_checkMatchesEquivalent {p₁ p₂ : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp₁ ← CompiledPolicy.compile p₁ Γ
    let cp₂ ← CompiledPolicy.compile p₂ Γ
    pure $ checkMatchesEquivalentOpt cp₁ cp₂
  ) =
  (do
    let wp₁ ← wellTypedPolicy p₁ Γ |>.mapError .validationError
    let wp₂ ← wellTypedPolicy p₂ Γ |>.mapError .validationError
    pure $ checkMatchesEquivalent wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₁)
  have h₂ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₂)
  cases hcp₁ : CompiledPolicy.compile p₁ Γ
  <;> cases hcp₂ : CompiledPolicy.compile p₂ Γ
  <;> cases hwp₁ : wellTypedPolicy p₁ Γ
  <;> cases hwp₂ : wellTypedPolicy p₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicy.compile is inconsistent
  -- with the behavior of wellTypedPolicy on the same policy
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cp₁ cp₂ wp₁ wp₂ =>
    exact checkMatchesEquivalentOpt_eqv_checkMatchesEquivalent_ok hwf hcp₁ hcp₂ hwp₁ hwp₂
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₁] at hcp₁
    simp [hcp₁]
  case ok.error.ok.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₂] at hcp₂
    simp [hcp₂]

/--
Full equivalence for `checkMatchesImplies` and `checkMatchesImpliesOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkMatchesImpliesOpt_eqv_checkMatchesImplies {p₁ p₂ : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp₁ ← CompiledPolicy.compile p₁ Γ
    let cp₂ ← CompiledPolicy.compile p₂ Γ
    pure $ checkMatchesImpliesOpt cp₁ cp₂
  ) =
  (do
    let wp₁ ← wellTypedPolicy p₁ Γ |>.mapError .validationError
    let wp₂ ← wellTypedPolicy p₂ Γ |>.mapError .validationError
    pure $ checkMatchesImplies wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₁)
  have h₂ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₂)
  cases hcp₁ : CompiledPolicy.compile p₁ Γ
  <;> cases hcp₂ : CompiledPolicy.compile p₂ Γ
  <;> cases hwp₁ : wellTypedPolicy p₁ Γ
  <;> cases hwp₂ : wellTypedPolicy p₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicy.compile is inconsistent
  -- with the behavior of wellTypedPolicy on the same policy
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cp₁ cp₂ wp₁ wp₂ =>
    exact checkMatchesImpliesOpt_eqv_checkMatchesImplies_ok hwf hcp₁ hcp₂ hwp₁ hwp₂
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₁] at hcp₁
    simp [hcp₁]
  case ok.error.ok.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₂] at hcp₂
    simp [hcp₂]

/--
Full equivalence for `checkMatchesDisjoint` and `checkMatchesDisjointOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkMatchesDisjointOpt_eqv_checkMatchesDisjoint {p₁ p₂ : Policy} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cp₁ ← CompiledPolicy.compile p₁ Γ
    let cp₂ ← CompiledPolicy.compile p₂ Γ
    pure $ checkMatchesDisjointOpt cp₁ cp₂
  ) =
  (do
    let wp₁ ← wellTypedPolicy p₁ Γ |>.mapError .validationError
    let wp₂ ← wellTypedPolicy p₂ Γ |>.mapError .validationError
    pure $ checkMatchesDisjoint wp₁ wp₂ (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₁)
  have h₂ := compile_ok_iff_welltypedpolicy_ok hwf (p := p₂)
  cases hcp₁ : CompiledPolicy.compile p₁ Γ
  <;> cases hcp₂ : CompiledPolicy.compile p₂ Γ
  <;> cases hwp₁ : wellTypedPolicy p₁ Γ
  <;> cases hwp₂ : wellTypedPolicy p₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicy.compile is inconsistent
  -- with the behavior of wellTypedPolicy on the same policy
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cp₁ cp₂ wp₁ wp₂ =>
    exact checkMatchesDisjointOpt_eqv_checkMatchesDisjoint_ok hwf hcp₁ hcp₂ hwp₁ hwp₂
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₁] at hcp₁
    simp [hcp₁]
  case ok.error.ok.error =>
    simp [CompiledPolicy.compile, Except.mapError, hwp₂] at hcp₂
    simp [hcp₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkImplies` and
`checkImpliesOpt` are equivalent.
-/
theorem checkImpliesOpt_eqv_checkImplies_ok {ps₁ ps₂ : Policies} {cpset₁ cpset₂ : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps₁ Γ = .ok cpset₁ →
  CompiledPolicySet.compile ps₂ Γ = .ok cpset₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    checkImpliesOpt cpset₁ cpset₂ = checkImplies wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkImplies, checkImpliesOpt]
  simp [checkUnsat]
  intro hwf hcpset₁ hcpset₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcpset₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcpset₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyImplies_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  simp [cpset_compile_produces_the_right_env hcpset₁]
  have := verifyImpliesOpt_eqv_verifyImplies_ok hcpset₁ hcpset₂ hwps₁ hwps₂
  simp [h₁, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

/--
Full equivalence for `checkImplies` and `checkImpliesOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkImpliesOpt_eqv_checkImplies {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cpset₁ ← CompiledPolicySet.compile ps₁ Γ
    let cpset₂ ← CompiledPolicySet.compile ps₂ Γ
    pure $ checkImpliesOpt cpset₁ cpset₂
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
  cases hcpset₁ : CompiledPolicySet.compile ps₁ Γ
  <;> cases hcpset₂ : CompiledPolicySet.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicySet.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cpset₁ cpset₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := checkImpliesOpt_eqv_checkImplies_ok hwf hcpset₁ hcpset₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₁] at hcpset₁
    simp [hcpset₁]
  case ok.error.ok.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₂] at hcpset₂
    simp [hcpset₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkAlwaysAllows` and
`checkAlwaysAllowsOpt` are equivalent.
-/
theorem checkAlwaysAllowsOpt_eqv_checkAlwaysAllows_ok {ps : Policies} {cpset : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps Γ = .ok cpset →
  ∃ wps,
    wellTypedPolicies ps Γ = .ok wps ∧
    checkAlwaysAllowsOpt cpset = checkAlwaysAllows wps (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkAlwaysAllows, checkAlwaysAllowsOpt]
  simp [checkUnsat]
  intro hwf hcpset
  have ⟨wps, hwps⟩ := compile_ok_then_exists_wtps hwf hcpset
  exists wps ; apply And.intro hwps
  have ⟨asserts, h₁⟩ := verifyAlwaysAllows_is_ok hwf hwps
  simp [h₁]
  simp [cpset_compile_produces_the_right_env hcpset]
  have := verifyAlwaysAllowsOpt_eqv_verifyAlwaysAllows_ok hcpset hwps
  simp [h₁, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

/--
Full equivalence for `checkAlwaysAllows` and `checkAlwaysAllowsOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkAlwaysAllowsOpt_eqv_checkAlwaysAllows {ps : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cpset ← CompiledPolicySet.compile ps Γ
    pure $ checkAlwaysAllowsOpt cpset
  ) =
  (do
    let wps ← wellTypedPolicies ps Γ |>.mapError .validationError
    pure $ checkAlwaysAllows wps (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps)
  cases hcpset : CompiledPolicySet.compile ps Γ
  <;> cases hwps : wellTypedPolicies ps Γ
  -- this eliminates all the cases where the behavior of CompiledPolicySet.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok cpset wps =>
    have ⟨wps', hwps', h⟩ := checkAlwaysAllowsOpt_eqv_checkAlwaysAllows_ok hwf hcpset
    simp_all
  case error.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps] at hcpset
    simp [hcpset]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkAlwaysDenies` and
`checkAlwaysDeniesOpt` are equivalent.
-/
theorem checkAlwaysDeniesOpt_eqv_checkAlwaysDenies_ok {ps : Policies} {cpset : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps Γ = .ok cpset →
  ∃ wps,
    wellTypedPolicies ps Γ = .ok wps ∧
    checkAlwaysDeniesOpt cpset = checkAlwaysDenies wps (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkAlwaysDenies, checkAlwaysDeniesOpt]
  simp [checkUnsat]
  intro hwf hcpset
  have ⟨wps, hwps⟩ := compile_ok_then_exists_wtps hwf hcpset
  exists wps ; apply And.intro hwps
  have ⟨asserts, h₁⟩ := verifyAlwaysDenies_is_ok hwf hwps
  simp [h₁]
  simp [cpset_compile_produces_the_right_env hcpset]
  have := verifyAlwaysDeniesOpt_eqv_verifyAlwaysDenies_ok hcpset hwps
  simp [h₁, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

/--
Full equivalence for `checkAlwaysDenies` and `checkAlwaysDeniesOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkAlwaysDeniesOpt_eqv_checkAlwaysDenies {ps : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cpset ← CompiledPolicySet.compile ps Γ
    pure $ checkAlwaysDeniesOpt cpset
  ) =
  (do
    let wps ← wellTypedPolicies ps Γ |>.mapError .validationError
    pure $ checkAlwaysDenies wps (SymEnv.ofTypeEnv Γ)
  )
:= by
  intro hwf
  have h₁ := compile_ok_iff_welltypedpolicies_ok hwf (ps := ps)
  cases hcpset : CompiledPolicySet.compile ps Γ
  <;> cases hwps : wellTypedPolicies ps Γ
  -- this eliminates all the cases where the behavior of CompiledPolicySet.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok cpset wps =>
    have ⟨wps', hwps', h⟩ := checkAlwaysDeniesOpt_eqv_checkAlwaysDenies_ok hwf hcpset
    simp_all
  case error.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps] at hcpset
    simp [hcpset]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkEquivalent` and
`checkEquivalentOpt` are equivalent.
-/
theorem checkEquivalentOpt_eqv_checkEquivalent_ok {ps₁ ps₂ : Policies} {cpset₁ cpset₂ : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps₁ Γ = .ok cpset₁ →
  CompiledPolicySet.compile ps₂ Γ = .ok cpset₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    checkEquivalentOpt cpset₁ cpset₂ = checkEquivalent wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkEquivalent, checkEquivalentOpt]
  simp [checkUnsat]
  intro hwf hcpset₁ hcpset₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcpset₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcpset₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyEquivalent_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  simp [cpset_compile_produces_the_right_env hcpset₁]
  have := verifyEquivalentOpt_eqv_verifyEquivalent_ok hcpset₁ hcpset₂ hwps₁ hwps₂
  simp [h₁, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

/--
Full equivalence for `checkEquivalent` and `checkEquivalentOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkEquivalentOpt_eqv_checkEquivalent {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cpset₁ ← CompiledPolicySet.compile ps₁ Γ
    let cpset₂ ← CompiledPolicySet.compile ps₂ Γ
    pure $ checkEquivalentOpt cpset₁ cpset₂
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
  cases hcpset₁ : CompiledPolicySet.compile ps₁ Γ
  <;> cases hcpset₂ : CompiledPolicySet.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicySet.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cpset₁ cpset₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := checkEquivalentOpt_eqv_checkEquivalent_ok hwf hcpset₁ hcpset₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₁] at hcpset₁
    simp [hcpset₁]
  case ok.error.ok.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₂] at hcpset₂
    simp [hcpset₂]

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `wellTypedPolicies` succeeds and `checkDisjoint` and
`checkDisjointOpt` are equivalent.
-/
theorem checkDisjointOpt_eqv_checkDisjoint_ok {ps₁ ps₂ : Policies} {cpset₁ cpset₂ : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  CompiledPolicySet.compile ps₁ Γ = .ok cpset₁ →
  CompiledPolicySet.compile ps₂ Γ = .ok cpset₂ →
  ∃ wps₁ wps₂,
    wellTypedPolicies ps₁ Γ = .ok wps₁ ∧
    wellTypedPolicies ps₂ Γ = .ok wps₂ ∧
    checkDisjointOpt cpset₁ cpset₂ = checkDisjoint wps₁ wps₂ (SymEnv.ofTypeEnv Γ)
:= by
  simp [checkDisjoint, checkDisjointOpt]
  simp [checkUnsat]
  intro hwf hcpset₁ hcpset₂
  have ⟨wps₁, hwps₁⟩ := compile_ok_then_exists_wtps hwf hcpset₁
  exists wps₁ ; apply And.intro hwps₁
  have ⟨wps₂, hwps₂⟩ := compile_ok_then_exists_wtps hwf hcpset₂
  exists wps₂ ; apply And.intro hwps₂
  have ⟨asserts, h₁⟩ := verifyDisjoint_is_ok hwf hwps₁ hwps₂
  simp [h₁]
  simp [cpset_compile_produces_the_right_env hcpset₁]
  have := verifyDisjointOpt_eqv_verifyDisjoint_ok hcpset₁ hcpset₂ hwps₁ hwps₂
  simp [h₁, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

/--
Full equivalence for `checkDisjoint` and `checkDisjointOpt`, including both the
`.ok` and `.error` cases
-/
theorem checkDisjointOpt_eqv_checkDisjoint {ps₁ ps₂ : Policies} {Γ : Validation.TypeEnv} :
  Γ.WellFormed →
  (do
    let cpset₁ ← CompiledPolicySet.compile ps₁ Γ
    let cpset₂ ← CompiledPolicySet.compile ps₂ Γ
    pure $ checkDisjointOpt cpset₁ cpset₂
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
  cases hcpset₁ : CompiledPolicySet.compile ps₁ Γ
  <;> cases hcpset₂ : CompiledPolicySet.compile ps₂ Γ
  <;> cases hwps₁ : wellTypedPolicies ps₁ Γ
  <;> cases hwps₂ : wellTypedPolicies ps₂ Γ
  -- this eliminates all the cases where the behavior of CompiledPolicySet.compile is inconsistent
  -- with the behavior of wellTypedPolicies on the same policyset
  <;> simp_all [Except.mapError, Except.isOk, Except.toBool]
  case ok.ok.ok.ok cpset₁ cpset₂ wps₁ wps₂ =>
    have ⟨wps₁', wps₂', hwps₁', hwps₂', h⟩ := checkDisjointOpt_eqv_checkDisjoint_ok hwf hcpset₁ hcpset₂
    simp_all
  case error.ok.error.ok | error.error.error.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₁] at hcpset₁
    simp [hcpset₁]
  case ok.error.ok.error =>
    simp [CompiledPolicySet.compile, Except.mapError, hwps₂] at hcpset₂
    simp [hcpset₂]

end Cedar.Thm
