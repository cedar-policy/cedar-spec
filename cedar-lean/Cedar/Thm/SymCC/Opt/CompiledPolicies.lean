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
import Cedar.Thm.WellTypedVerification

/-!
Some lemmas about `CompiledPolicy` and `CompiledPolicies`.
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.SymCC

/--
The `.policy` of a `CompiledPolicy` is exactly the policy produced by `wellTypedPolicy`
-/
theorem compiled_policy_eq_wtp {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  cp.policy = wp
:= by
  simp [CompiledPolicy.compile, do_eq_ok, Except.mapError]
  intro p' h₀ t h₁ h₂ ; subst cp ; simp
  split at h₀ <;> simp_all

/--
The `.policies` of a `CompiledPolicies` is exactly the policies produced by `wellTypedPolicies`
-/
theorem compiled_policies_eq_wtps {ps wps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps Γ = .ok cps →
  wellTypedPolicies ps Γ = .ok wps →
  cps.policies = wps
:= by
  simp [CompiledPolicies.compile, do_eq_ok, Except.mapError]
  intro ps' h₀ t h₁ h₂ ; subst cps ; simp
  split at h₀ <;> simp_all

theorem cp_compile_produces_the_right_env {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  cp.εnv = SymEnv.ofTypeEnv Γ
:= by
  simp only [CompiledPolicy.compile, Except.mapError, do_eq_ok, Except.ok.injEq, forall_exists_index, and_imp]
  intro p' h₀ t h₁ h₂ ; subst h₂
  simp

theorem cps_compile_produces_the_right_env {ps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps Γ = .ok cps →
  cps.εnv = SymEnv.ofTypeEnv Γ
:= by
  simp only [CompiledPolicies.compile, Except.mapError, do_eq_ok, Except.ok.injEq, forall_exists_index, and_imp]
  intro ps' h₀ t h₁ h₂ ; subst h₂
  simp

theorem cp_compile_produces_the_right_term {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  cp.term = SymCC.compile wp.toExpr (SymEnv.ofTypeEnv Γ)
:= by
  simp [CompiledPolicy.compile, do_eq_ok, Except.mapError]
  intro p' h₀ t h₁ h₂ h₃ ; subst cp ; simp only
  split at h₀ <;> simp at h₀
  subst p' ; rename_i wp' h₂
  simp [h₂] at h₃ ; subst wp'
  split at h₁ <;> simp_all

theorem cps_compile_produces_the_right_term {ps wps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps Γ = .ok cps →
  wellTypedPolicies ps Γ = .ok wps →
  cps.term = SymCC.isAuthorized wps (SymEnv.ofTypeEnv Γ)
:= by
  simp [CompiledPolicies.compile, do_eq_ok, Except.mapError]
  intro ps' h₀ t h₁ h₂ h₃ ; subst cps ; simp only
  split at h₀ <;> simp at h₀
  subst ps' ; rename_i wps' h₂
  simp [h₂] at h₃ ; subst wps'
  split at h₁ <;> simp_all

theorem cp_compile_produces_the_right_footprint {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  cp.footprint = footprint cp.policy.toExpr cp.εnv
:= by
  simp [CompiledPolicy.compile, do_eq_ok]
  intro p h₀ t h₁ h₂ ; subst cp
  simp

theorem cps_compile_produces_the_right_footprint {ps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps Γ = .ok cps →
  cps.footprint = footprints (cps.policies.map Policy.toExpr) cps.εnv
:= by
  simp [CompiledPolicies.compile, do_eq_ok]
  intro ps h₀ t h₁ h₂ ; subst cps
  simp

theorem cp_compile_produces_the_right_acyclicity {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  cp.acyclicity = cp.footprint.map (SymCC.acyclicity · cp.εnv.entities)
:= by
  intro temp ; have hf := cp_compile_produces_the_right_footprint temp ; revert temp
  simp [CompiledPolicy.compile]
  simp [do_eq_ok, hf]
  intro p h₀ t h₁ h₂ ; subst cp
  simp

theorem cps_compile_produces_the_right_acyclicity {ps : Policies} {cps : CompiledPolicies} {Γ : Validation.TypeEnv} :
  CompiledPolicies.compile ps Γ = .ok cps →
  cps.acyclicity = cps.footprint.map (SymCC.acyclicity · cps.εnv.entities)
:= by
  intro temp ; have hf := cps_compile_produces_the_right_footprint temp ; revert temp
  simp [CompiledPolicies.compile]
  simp [do_eq_ok, hf]
  intro ps h₀ t h₁ h₂ ; subst cps
  simp
