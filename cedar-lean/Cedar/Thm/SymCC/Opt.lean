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
compilation succeeds, then `satAsserts?` and `satAssertsOpt?'` are equivalent.
-/
theorem satAssertsOpt?'_eqv_satAsserts?_ok {ps wps : Policies} {cps : List CompiledPolicy} {Γ : Validation.TypeEnv} :
  ps.length = cps.length →
  cps ≠ [] →
  ps.mapM (CompiledPolicy.compile · Γ) = .ok cps →
  ps.mapM (wellTypedPolicy · Γ) = .ok wps →
  satAsserts? wps asserts (SymEnv.ofTypeEnv Γ) = satAssertsOpt?' cps asserts
:= by
  intro hlen
  simp [satAsserts?, satAssertsOpt?']
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
  rw [cp_compile_produces_the_right_env hcp]
  congr
  funext I
  cases I <;> simp only
  case some I =>
  suffices SymEnv.extract? ((wp :: wps).map Policy.toExpr) I (SymEnv.ofTypeEnv Γ) = CompiledPolicy.extractOpt? (cp :: cps) I by rw [this] ; rfl
  rw [cp_extractOpt?_eqv_extract? (εnv := cp.εnv) (by simp)]
  · congr 1
    · simp only [List.map_cons, Function.comp_apply, List.cons.injEq]
      simp only [compiled_policy_eq_wtp hcp hwp, true_and]
      rw [← List.forall₂_iff_map_eq]
      apply List.Forall₂.imp (R := λ a b => a = CompiledPolicy.policy b)
      · intro a b h ; subst h ; simp
      · rw [List.mapM_ok_iff_forall₂] at hcps hwps
        apply List.forall₂_trans_ish hwps hcps
        intro p wp cp hwp hcp
        exact (compiled_policy_eq_wtp hcp hwp).symm
    · simp [cp_compile_produces_the_right_env hcp]
  · intro cp' hcp'
    cases hcp'
    · rfl
    · rename_i hcp'
      replace ⟨hεnv, hεnv'⟩ := hεnv
      simp [hεnv, hεnv' cp' hcp']
  · intro cp' hcp'
    cases hcp'
    · exists p, Γ
    · rename_i hcp'
      replace ⟨p', hp', hcps⟩ := List.mapM_ok_implies_all_from_ok hcps cp' hcp'
      exists p', Γ

/--
This theorem covers the "happy path" -- showing that if optimized policy
compilation succeeds, then `satAsserts?` and `satAssertsOpt?` are equivalent.
-/
theorem satAssertsOpt?_eqv_satAsserts?_ok {pss wpss : List Policies} {cpss : List CompiledPolicies} {Γ : Validation.TypeEnv} :
  pss.length = cpss.length →
  cpss ≠ [] →
  pss.mapM (CompiledPolicies.compile · Γ) = .ok cpss →
  pss.mapM (wellTypedPolicies · Γ) = .ok wpss →
  satAsserts? wpss.flatten asserts (SymEnv.ofTypeEnv Γ) = satAssertsOpt? cpss asserts
:= by
  intro hlen
  simp [satAsserts?, satAssertsOpt?]
  intro hnil hcpss hwpss
  have hεnv : ∀ cps ∈ cpss, cps.εnv = SymEnv.ofTypeEnv Γ := by
    intro cps hcps
    replace ⟨ps, hps, hcpss⟩ := List.mapM_ok_implies_all_from_ok hcpss cps hcps
    exact cps_compile_produces_the_right_env hcpss
  revert hnil
  cases cpss <;> simp
  case cons cps cpss =>
  cases pss <;> simp at *
  case cons ps pss =>
  simp [do_eq_ok] at hwpss hcpss
  replace ⟨wps, hwps, hwpss⟩ := hwpss
  simp [Functor.map, Except.map] at hwpss
  split at hwpss <;> simp at hwpss
  subst wpss ; rename_i wpss hwpss
  replace ⟨cps', hcps', hcpss⟩ := hcpss
  simp [Functor.map, Except.map] at hcpss
  split at hcpss <;> simp at hcpss
  replace ⟨hcpss, htemp⟩ := hcpss ; subst cps' htemp ; rename_i cpss hcpss ; have hcps := hcps' ; clear hcps'
  rw [cps_compile_produces_the_right_env hcps]
  congr
  funext I
  cases I <;> simp only
  case some I =>
  suffices SymEnv.extract? (List.map (List.map Policy.toExpr) (wps :: wpss)).flatten I (SymEnv.ofTypeEnv Γ) = CompiledPolicies.extractOpt? (cps :: cpss) I by rw [this] ; rfl
  rw [cps_extractOpt?_eqv_extract? (εnv := cps.εnv) (by simp)]
  · congr 1
    · simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, List.map_append]
      congr 2
      · simp [compiled_policies_eq_wtps hcps hwps]
      · simp [List.flatMap]
        congr 1
        rw [← List.forall₂_iff_map_eq]
        apply List.Forall₂.imp (R := λ a b => a = CompiledPolicies.policies b)
        · intro a b h ; subst h ; simp
        · rw [List.mapM_ok_iff_forall₂] at hcpss hwpss
          apply List.forall₂_trans_ish hwpss hcpss
          intro ps wps cps hwps hcps
          exact (compiled_policies_eq_wtps hcps hwps).symm
    · simp [cps_compile_produces_the_right_env hcps]
  · intro cps' hcps'
    cases hcps'
    · rfl
    · rename_i hcps'
      replace ⟨hεnv, hεnv'⟩ := hεnv
      simp [hεnv, hεnv' cps' hcps']
  · intro cps' hcps'
    cases hcps'
    · exists ps, Γ
    · rename_i hcps'
      replace ⟨ps', hps', hcpss⟩ := List.mapM_ok_implies_all_from_ok hcpss cps' hcps'
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
  rw [← satAssertsOpt?'_eqv_satAsserts?_ok (ps := [p]) (cps := [cp]) (by simp) (by simp)]
  · have := verifyNeverErrorsOpt_eqv_verifyNeverErrors_ok h₀ h₁
    simp [h₂, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAsserts? [wp] _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, h₀]
  · simp [pure, Except.pure, h₁]

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
  rw [← satAssertsOpt?'_eqv_satAsserts?_ok (ps := [p]) (cps := [cp]) (by simp) (by simp)]
  · have := verifyAlwaysMatchesOpt_eqv_verifyAlwaysMatches_ok h₀ h₁
    simp [h₂, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAsserts? [wp] _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, h₀]
  · simp [pure, Except.pure, h₁]

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
  rw [← satAssertsOpt?'_eqv_satAsserts?_ok (ps := [p]) (cps := [cp]) (by simp) (by simp)]
  · have := verifyNeverMatchesOpt_eqv_verifyNeverMatches_ok h₀ h₁
    simp [h₂, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAsserts? [wp] _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, h₀]
  · simp [pure, Except.pure, h₁]

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
  rw [← satAssertsOpt?'_eqv_satAsserts?_ok (ps := [p₁, p₂]) (cps := [cp₁, cp₂]) (by simp) (by simp)]
  · have := verifyMatchesEquivalentOpt_eqv_verifyMatchesEquivalent_ok h₀ h₁ h₂ h₃
    simp [h₄, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAsserts? [wp₁, wp₂] _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, h₀, h₁]
  · simp [pure, Except.pure, h₂, h₃]

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
  rw [← satAssertsOpt?'_eqv_satAsserts?_ok (ps := [p₁, p₂]) (cps := [cp₁, cp₂]) (by simp) (by simp)]
  · have := verifyMatchesImpliesOpt_eqv_verifyMatchesImplies_ok h₀ h₁ h₂ h₃
    simp [h₄, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAsserts? [wp₁, wp₂] _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, h₀, h₁]
  · simp [pure, Except.pure, h₂, h₃]

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
  rw [← satAssertsOpt?'_eqv_satAsserts?_ok (ps := [p₁, p₂]) (cps := [cp₁, cp₂]) (by simp) (by simp)]
  · have := verifyMatchesDisjointOpt_eqv_verifyMatchesDisjoint_ok h₀ h₁ h₂ h₃
    simp [h₄, ResultAssertsEquiv] at this
    exact Asserts.Equiv.satAsserts? [wp₁, wp₂] _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, h₀, h₁]
  · simp [pure, Except.pure, h₂, h₃]

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
  rw [← satAssertsOpt?_eqv_satAsserts?_ok (pss := [ps₁, ps₂]) (wpss := [wps₁, wps₂]) (cpss := [cps₁, cps₂]) (by simp) (by simp)]
  · have := verifyImpliesOpt_eqv_verifyImplies_ok hcps₁ hcps₂ hwps₁ hwps₂
    simp [h₁, ResultAssertsEquiv] at this
    simp only [List.flatten, List.append_eq, List.append_nil]
    exact Asserts.Equiv.satAsserts? (wps₁ ++ wps₂) _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, hcps₁, hcps₂]
  · simp [pure, Except.pure, hwps₁, hwps₂]

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
  rw [← satAssertsOpt?_eqv_satAsserts?_ok (pss := [ps]) (wpss := [wps]) (cpss := [cps]) (Γ := Γ) (by simp) (by simp)]
  · have := verifyAlwaysAllowsOpt_eqv_verifyAlwaysAllows_ok hcps hwps
    simp [h₁, ResultAssertsEquiv] at this
    simp only [List.flatten, List.append_eq, List.append_nil]
    exact Asserts.Equiv.satAsserts? wps _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, hcps]
  · simp [pure, Except.pure, hwps]

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
  rw [← satAssertsOpt?_eqv_satAsserts?_ok (pss := [ps]) (wpss := [wps]) (cpss := [cps]) (Γ := Γ) (by simp) (by simp)]
  · have := verifyAlwaysDeniesOpt_eqv_verifyAlwaysDenies_ok hcps hwps
    simp [h₁, ResultAssertsEquiv] at this
    simp only [List.flatten, List.append_eq, List.append_nil]
    exact Asserts.Equiv.satAsserts? wps _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, hcps]
  · simp [pure, Except.pure, hwps]

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
  rw [← satAssertsOpt?_eqv_satAsserts?_ok (pss := [ps₁, ps₂]) (wpss := [wps₁, wps₂]) (cpss := [cps₁, cps₂]) (by simp) (by simp)]
  · have := verifyEquivalentOpt_eqv_verifyEquivalent_ok hcps₁ hcps₂ hwps₁ hwps₂
    simp [h₁, ResultAssertsEquiv] at this
    simp only [List.flatten, List.append_eq, List.append_nil]
    exact Asserts.Equiv.satAsserts? (wps₁ ++ wps₂) _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, hcps₁, hcps₂]
  · simp [pure, Except.pure, hwps₁, hwps₂]

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
  rw [← satAssertsOpt?_eqv_satAsserts?_ok (pss := [ps₁, ps₂]) (wpss := [wps₁, wps₂]) (cpss := [cps₁, cps₂]) (by simp) (by simp)]
  · have := verifyDisjointOpt_eqv_verifyDisjoint_ok hcps₁ hcps₂ hwps₁ hwps₂
    simp [h₁, ResultAssertsEquiv] at this
    simp only [List.flatten, List.append_eq, List.append_nil]
    exact Asserts.Equiv.satAsserts? (wps₁ ++ wps₂) _ (Asserts.Equiv.symm this)
  · simp [pure, Except.pure, hcps₁, hcps₂]
  · simp [pure, Except.pure, hwps₁, hwps₂]

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
  have := verifyImpliesOpt_eqv_verifyImplies_ok hcps₁ hcps₂ hwps₁ hwps₂
  simp [h₁, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

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
  have := verifyAlwaysAllowsOpt_eqv_verifyAlwaysAllows_ok hcps hwps
  simp [h₁, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

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
  have := verifyAlwaysDeniesOpt_eqv_verifyAlwaysDenies_ok hcps hwps
  simp [h₁, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

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
  have := verifyEquivalentOpt_eqv_verifyEquivalent_ok hcps₁ hcps₂ hwps₁ hwps₂
  simp [h₁, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

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
  have := verifyDisjointOpt_eqv_verifyDisjoint_ok hcps₁ hcps₂ hwps₁ hwps₂
  simp [h₁, ResultAssertsEquiv] at this
  exact Asserts.Equiv.checkUnsatAsserts (Asserts.Equiv.symm this)

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

end Cedar.Thm
