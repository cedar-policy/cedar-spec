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
import Cedar.Thm.SymCC.Opt.Authorizer
import Cedar.Thm.SymCC.Opt.Compiler
import Cedar.Thm.WellTypedVerification

/-!
Some lemmas about `CompiledPolicy`, `CompiledPolicySet`, and `CompiledPolicies`.
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.SymCC

/--
Lemma about the behavior of `wellTypedPolicy` vs `wellTypedPolicies`
-/
private theorem wellTypedPolicy_wellTypedPolicies {p : Policy} {Γ : Validation.TypeEnv} :
  wellTypedPolicies [p] Γ = (wellTypedPolicy p Γ).map λ x => [x]
:= by
  simp [wellTypedPolicies, Except.map, pure, Except.pure]
  cases wellTypedPolicy p Γ <;> simp

/--
Toplevel theorem about the correctness of `CompiledPolicy.intoCompiledPolicySet`

Compiling to a `CompiledPolicy` and then using `intoCompiledPolicySet` should give
exactly the same result as compiling with `CompiledPolicySet.compile` directly
-/
theorem intoCompiledPolicySet_correctness {p : Policy} {Γ : Validation.TypeEnv} :
  (do
    let cp ← CompiledPolicy.compile p Γ
    pure cp.intoCompiledPolicySet
  ) = CompiledPolicySet.compile [p] Γ
:= by
  simp [CompiledPolicy.compile, CompiledPolicySet.compile, CompiledPolicy.intoCompiledPolicySet, wellTypedPolicy_wellTypedPolicies, Except.mapError, Except.map]
  cases wellTypedPolicy p Γ <;> simp
  case ok p' =>
  simp [Opt.isAuthorized, Opt.satisfiedPolicies, Opt.compileWithEffect]
  cases p'.effect <;> simp [Factory.anyTrue, Factory.or, Factory.not, Factory.and]
  all_goals {
    cases h : Opt.compile p'.toExpr (SymEnv.ofEnv Γ) <;> simp [List.mapUnion_nil]
    have hwf := Opt.compile_footprint_wf h
    simp [EmptyCollection.emptyCollection, Data.Set.union_empty_right List.mapUnion_wf, Data.Set.union_empty_left List.mapUnion_wf]
    rw [List.mapUnion_cons (by simp [hwf])]
    simp [List.mapUnion_nil, EmptyCollection.emptyCollection, Data.Set.union_empty_right hwf]
  }

/--
The `.policy` of a `CompiledPolicy` is exactly the policy produced by `wellTypedPolicy`
-/
theorem cp_compile_produces_the_right_policy {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  cp.policy = wp
:= by
  simp [CompiledPolicy.compile, do_eq_ok, Except.mapError]
  intro p' h₀ t h₁ h₂ ; subst cp ; simp
  split at h₀ <;> simp_all

/--
The `.policies` of a `CompiledPolicySet` is exactly the policies produced by `wellTypedPolicies`
-/
theorem cpset_compile_produces_the_right_policies {ps wps : Policies} {cpset : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  CompiledPolicySet.compile ps Γ = .ok cpset →
  wellTypedPolicies ps Γ = .ok wps →
  cpset.policies = wps
:= by
  simp [CompiledPolicySet.compile, do_eq_ok, Except.mapError]
  intro ps' h₀ t h₁ h₂ ; subst cpset ; simp
  split at h₀ <;> simp_all

theorem cp_compile_produces_the_right_env {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  cp.εnv = SymEnv.ofTypeEnv Γ
:= by
  simp only [CompiledPolicy.compile, Except.mapError, do_eq_ok, Except.ok.injEq, forall_exists_index, and_imp]
  intro p' h₀ t h₁ h₂ ; subst h₂
  simp

theorem cpset_compile_produces_the_right_env {ps : Policies} {cpset : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  CompiledPolicySet.compile ps Γ = .ok cpset →
  cpset.εnv = SymEnv.ofTypeEnv Γ
:= by
  simp only [CompiledPolicySet.compile, Except.mapError, do_eq_ok, Except.ok.injEq, forall_exists_index, and_imp]
  intro ps' h₀ t h₁ h₂ ; subst h₂
  simp

theorem cp_compile_produces_the_right_term {p wp : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  wellTypedPolicy p Γ = .ok wp →
  cp.term = SymCC.compile wp.toExpr (SymEnv.ofTypeEnv Γ)
:= by
  simp [CompiledPolicy.compile, do_eq_ok, Except.mapError]
  intro p' h₀ res h₁ h₂ h₃ ; subst cp ; simp only
  rw [Opt.compile.correctness] at h₁
  split at h₀ <;> simp at h₀
  subst p' ; rename_i wp' h₂
  simp [h₂] at h₃ ; subst wp'
  cases hcomp : SymCC.compile wp.toExpr (SymEnv.ofTypeEnv Γ) <;> simp [hcomp] at h₁ ⊢
  case ok t => subst res ; simp

theorem cpset_compile_produces_the_right_term {ps wps : Policies} {cpset : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  CompiledPolicySet.compile ps Γ = .ok cpset →
  wellTypedPolicies ps Γ = .ok wps →
  cpset.term = SymCC.isAuthorized wps (SymEnv.ofTypeEnv Γ)
:= by
  simp [CompiledPolicySet.compile, do_eq_ok, Except.mapError]
  intro ps' h₀ res h₁ h₂ h₃ ; subst cpset ; simp only
  rw [Opt.isAuthorized.correctness] at h₁
  split at h₀ <;> simp at h₀
  subst ps' ; rename_i wps' h₂
  simp [h₂] at h₃ ; subst wps'
  simp_do_let SymCC.isAuthorized wps _ at h₁
  simp only [Except.ok.injEq] at h₁ ; subst res
  simp

theorem cp_compile_produces_the_right_footprint {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  cp.footprint = footprint cp.policy.toExpr cp.εnv
:= by
  simp [CompiledPolicy.compile, do_eq_ok]
  intro p h₀ t h₁ h₂ ; subst cp
  simp_all only [Except.mapError]
  rw [Opt.compile.correctness] at h₁
  split at h₁ <;> simp at h₁
  subst t ; rename_i res h₁
  simp_do_let SymCC.compile p.toExpr (SymEnv.ofEnv Γ) at h₁
  simp only [Except.ok.injEq] at h₁ ; subst res
  simp

theorem cpset_compile_produces_the_right_footprint {ps : Policies} {cpset : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  CompiledPolicySet.compile ps Γ = .ok cpset →
  cpset.footprint = footprints (cpset.policies.map Policy.toExpr) cpset.εnv
:= by
  simp [CompiledPolicySet.compile, do_eq_ok]
  intro ps h₀ t h₁ h₂ ; subst cpset
  simp_all only [Except.mapError]
  rw [Opt.isAuthorized.correctness] at h₁
  split at h₁ <;> simp at h₁
  subst t ; rename_i res h₁
  simp_do_let SymCC.isAuthorized ps (SymEnv.ofEnv Γ) at h₁
  simp only [Except.ok.injEq] at h₁ ; subst res
  simp

theorem cp_compile_produces_the_right_acyclicity {p : Policy} {cp : CompiledPolicy} {Γ : Validation.TypeEnv} :
  CompiledPolicy.compile p Γ = .ok cp →
  cp.acyclicity = cp.footprint.map (SymCC.acyclicity · cp.εnv.entities)
:= by
  intro temp ; have hf := cp_compile_produces_the_right_footprint temp ; revert temp
  simp [CompiledPolicy.compile]
  simp [do_eq_ok, hf]
  intro p h₀ t h₁ h₂ ; subst cp
  simp only at *
  congr

theorem cpset_compile_produces_the_right_acyclicity {ps : Policies} {cpset : CompiledPolicySet} {Γ : Validation.TypeEnv} :
  CompiledPolicySet.compile ps Γ = .ok cpset →
  cpset.acyclicity = cpset.footprint.map (SymCC.acyclicity · cpset.εnv.entities)
:= by
  intro temp ; have hf := cpset_compile_produces_the_right_footprint temp ; revert temp
  simp [CompiledPolicySet.compile]
  simp [do_eq_ok, hf]
  intro ps h₀ t h₁ h₂ ; subst cpset
  simp only at *
  congr

theorem flatMap_allPolicies_policy {cps : List CompiledPolicy} :
  List.flatMap CompiledPolicies.allPolicies (cps.map CompiledPolicies.policy) = cps.map CompiledPolicy.policy
:= by
  simp only [List.flatMap_map]
  simp [CompiledPolicies.allPolicies, List.map_eq_flatMap]

theorem flatMap_allPolicies_policies {cpsets : List CompiledPolicySet} :
  List.flatMap CompiledPolicies.allPolicies (cpsets.map CompiledPolicies.pset) = cpsets.flatMap CompiledPolicySet.policies
:= by
  simp [List.flatMap_map, CompiledPolicies.allPolicies]
