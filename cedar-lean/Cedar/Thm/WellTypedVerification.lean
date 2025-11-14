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

import Cedar.Thm.SymCC.Verifier.WellTypedOk
import Cedar.Thm.SymCC.WellTyped
import Cedar.Thm.Verification
import Cedar.Thm.SymCC.Env.Soundness
import Cedar.Thm.SymCC.Env.Completeness

/-!
This file connects soundness theorems in `Cedar.Thm.Verification`
with policy validation.

We prove that if validation of a policy (set) succeeds in the sense of
`wellTypedPolicy`/`wellTypedPolicies`), then various verification tasks
would produce a symbolic encoding *without errors*, and is sound with
respect to concrete `Env`s.
-/

namespace Cedar.Thm

open Spec SymCC Validation

/--
Concrete version of `verifyNeverErrors_is_sound`.

NOTE: This theorem and many of the following soundness theorems
use `env.StronglyWellFormedForPolicy p'` in the conclusion
rather than `env.StronglyWellFormedForPolicy p`.

One can obtain a weaker version with `env.StronglyWellFormedForPolicy p`,
using the lemma `wellTypedPolicy_preserves_StronglyWellFormedForPolicy`.
-/
theorem verifyNeverErrors_is_ok_and_sound {p p' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p Γ = .ok p' →
  ∃ asserts,
    verifyNeverErrors p' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicy p' →
        (evaluate p.toExpr env.request env.entities).isOk)
:= by
  intros hwf hwt
  have hwf_εnv := ofEnv_swf_for_policy hwf hwt
  have ⟨asserts, hok⟩ := verifyNeverErrors_is_ok hwf hwt
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_env
  simp only [wellTypedPolicy_preserves_evaluation hinst hwt]
  apply verifyNeverErrors_is_sound hwf_εnv hok hunsat env
  · exact ofEnv_soundness hwf_env.1 hinst
  · exact hwf_env

/-- Concrete version of `verifyNeverErrors_is_complete`. -/
theorem verifyNeverErrors_is_ok_and_complete {p p' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p Γ = .ok p' →
  ∃ asserts,
    verifyNeverErrors p' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicy p' ∧
        ¬ (evaluate p.toExpr env.request env.entities).isOk)
:= by
  intros hwf hwt
  have hwf_εnv := ofEnv_swf_for_policy hwf hwt
  have ⟨asserts, hok⟩ := verifyNeverErrors_is_ok hwf hwt
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env, henum_comp, hres⟩ := verifyNeverErrors_is_complete hwf_εnv hok hsat
  have hinst := ofEnv_completeness hwf hswf_env.1 henum_comp hmodel
  have := wellTypedPolicy_preserves_evaluation hinst hwt
  simp only [←wellTypedPolicy_preserves_evaluation hinst hwt] at hres
  exists env

/-- Concrete version of `verifyEquivalent_is_sound`. -/
theorem verifyEquivalent_is_ok_and_sound {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .ok ps₁' →
  wellTypedPolicies ps₂ Γ = .ok ps₂' →
  ∃ asserts,
    verifyEquivalent ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicies ps₁' →
        env.StronglyWellFormedForPolicies ps₂' →
        bothAllowOrBothDeny
          (Spec.isAuthorized env.request env.entities ps₁)
          (Spec.isAuthorized env.request env.entities ps₂))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policies hwf hwt₂
  have ⟨asserts, hok⟩ := verifyEquivalent_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_ps₁ hwf_ps₂
  simp only [
    wellTypedPolicies_preserves_isAuthorized hinst hwt₁,
    wellTypedPolicies_preserves_isAuthorized hinst hwt₂,
  ]
  apply verifyEquivalent_is_sound hwf_εnv₁ hwf_εnv₂ hok hunsat env _ hwf_ps₁ hwf_ps₂
  exact ofEnv_soundness hwf_ps₁.1 hinst

/-- Concrete version of `verifyEquivalent_is_complete`. -/
theorem verifyEquivalent_is_ok_and_complete {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .ok ps₁' →
  wellTypedPolicies ps₂ Γ = .ok ps₂' →
  ∃ asserts,
    verifyEquivalent ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicies ps₁' ∧
        env.StronglyWellFormedForPolicies ps₂' ∧
        ¬ bothAllowOrBothDeny
          (Spec.isAuthorized env.request env.entities ps₁)
          (Spec.isAuthorized env.request env.entities ps₂))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policies hwf hwt₂
  have ⟨asserts, hok⟩ := verifyEquivalent_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env₁, hswf_env₂, henum_comp, hres⟩ := verifyEquivalent_is_complete hwf_εnv₁ hwf_εnv₂ hok hsat
  have hinst := ofEnv_completeness hwf hswf_env₁.1 henum_comp hmodel
  simp only [
    ←wellTypedPolicies_preserves_isAuthorized hinst hwt₁,
    ←wellTypedPolicies_preserves_isAuthorized hinst hwt₂,
  ] at hres
  exists env

/-- Concrete version of `verifyDisjoint_is_sound`. -/
theorem verifyDisjoint_is_ok_and_sound {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .ok ps₁' →
  wellTypedPolicies ps₂ Γ = .ok ps₂' →
  ∃ asserts,
    verifyDisjoint ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicies ps₁' →
        env.StronglyWellFormedForPolicies ps₂' →
        atLeastOneDenies
          (Spec.isAuthorized env.request env.entities ps₁)
          (Spec.isAuthorized env.request env.entities ps₂))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policies hwf hwt₂
  have ⟨asserts, hok⟩ := verifyDisjoint_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_ps₁ hwf_ps₂
  simp only [
    wellTypedPolicies_preserves_isAuthorized hinst hwt₁,
    wellTypedPolicies_preserves_isAuthorized hinst hwt₂,
  ]
  apply verifyDisjoint_is_sound hwf_εnv₁ hwf_εnv₂ hok hunsat env _ hwf_ps₁ hwf_ps₂
  exact ofEnv_soundness hwf_ps₁.1 hinst

/-- Concrete version of `verifyDisjoint_is_complete`. -/
theorem verifyDisjoint_is_ok_and_complete {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .ok ps₁' →
  wellTypedPolicies ps₂ Γ = .ok ps₂' →
  ∃ asserts,
    verifyDisjoint ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicies ps₁' ∧
        env.StronglyWellFormedForPolicies ps₂' ∧
        ¬ atLeastOneDenies
          (Spec.isAuthorized env.request env.entities ps₁)
          (Spec.isAuthorized env.request env.entities ps₂))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policies hwf hwt₂
  have ⟨asserts, hok⟩ := verifyDisjoint_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env₁, hswf_env₂, henum_comp, hres⟩ := verifyDisjoint_is_complete hwf_εnv₁ hwf_εnv₂ hok hsat
  have hinst := ofEnv_completeness hwf hswf_env₁.1 henum_comp hmodel
  simp only [
    ←wellTypedPolicies_preserves_isAuthorized hinst hwt₁,
    ←wellTypedPolicies_preserves_isAuthorized hinst hwt₂,
  ] at hres
  exists env

/-- Concrete version of `verifyImplies_is_sound`. -/
theorem verifyImplies_is_ok_and_sound {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .ok ps₁' →
  wellTypedPolicies ps₂ Γ = .ok ps₂' →
  ∃ asserts,
    verifyImplies ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicies ps₁' →
        env.StronglyWellFormedForPolicies ps₂' →
        ifFirstAllowsSoDoesSecond
          (Spec.isAuthorized env.request env.entities ps₁)
          (Spec.isAuthorized env.request env.entities ps₂))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policies hwf hwt₂
  have ⟨asserts, hok⟩ := verifyImplies_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_ps₁ hwf_ps₂
  simp only [
    wellTypedPolicies_preserves_isAuthorized hinst hwt₁,
    wellTypedPolicies_preserves_isAuthorized hinst hwt₂,
  ]
  apply verifyImplies_is_sound hwf_εnv₁ hwf_εnv₂ hok hunsat env _ hwf_ps₁ hwf_ps₂
  exact ofEnv_soundness hwf_ps₁.1 hinst

/-- Concrete version of `verifyImplies_is_complete`. -/
theorem verifyImplies_is_ok_and_complete {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .ok ps₁' →
  wellTypedPolicies ps₂ Γ = .ok ps₂' →
  ∃ asserts,
    verifyImplies ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicies ps₁' ∧
        env.StronglyWellFormedForPolicies ps₂' ∧
        ¬ ifFirstAllowsSoDoesSecond
          (Spec.isAuthorized env.request env.entities ps₁)
          (Spec.isAuthorized env.request env.entities ps₂))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policies hwf hwt₂
  have ⟨asserts, hok⟩ := verifyImplies_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env₁, hswf_env₂, henum_comp, hres⟩ := verifyImplies_is_complete hwf_εnv₁ hwf_εnv₂ hok hsat
  have hinst := ofEnv_completeness hwf hswf_env₁.1 henum_comp hmodel
  simp only [
    ←wellTypedPolicies_preserves_isAuthorized hinst hwt₁,
    ←wellTypedPolicies_preserves_isAuthorized hinst hwt₂,
  ] at hres
  exists env

/-- Concrete version of `verifyAlwaysDenies_is_sound`. -/
theorem verifyAlwaysDenies_is_ok_and_sound {ps₁ ps₁' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .ok ps₁' →
  ∃ asserts,
    verifyAlwaysDenies ps₁' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicies ps₁' →
        denies (Spec.isAuthorized env.request env.entities ps₁))
:= by
  intros hwf hwt₁
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have ⟨asserts, hok⟩ := verifyAlwaysDenies_is_ok hwf hwt₁
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_ps₁
  simp only [
    wellTypedPolicies_preserves_isAuthorized hinst hwt₁,
  ]
  apply verifyAlwaysDenies_is_sound hwf_εnv₁ hok hunsat env _ hwf_ps₁
  exact ofEnv_soundness hwf_ps₁.1 hinst

/-- Concrete version of `verifyAlwaysDenies_is_complete`. -/
theorem verifyAlwaysDenies_is_ok_and_complete {ps₁ ps₁' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .ok ps₁' →
  ∃ asserts,
    verifyAlwaysDenies ps₁' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicies ps₁' ∧
        ¬ denies (Spec.isAuthorized env.request env.entities ps₁))
:= by
  intros hwf hwt₁
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have ⟨asserts, hok⟩ := verifyAlwaysDenies_is_ok hwf hwt₁
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env₁, henum_comp, hres⟩ := verifyAlwaysDenies_is_complete hwf_εnv₁ hok hsat
  have hinst := ofEnv_completeness hwf hswf_env₁.1 henum_comp hmodel
  simp only [
    ←wellTypedPolicies_preserves_isAuthorized hinst hwt₁,
  ] at hres
  exists env

/-- Concrete version of `verifyAlwaysAllows_is_sound`. -/
theorem verifyAlwaysAllows_is_ok_and_sound {ps₁ ps₁' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .ok ps₁' →
  ∃ asserts,
    verifyAlwaysAllows ps₁' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicies ps₁' →
        allows (Spec.isAuthorized env.request env.entities ps₁))
:= by
  intros hwf hwt₁
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have ⟨asserts, hok⟩ := verifyAlwaysAllows_is_ok hwf hwt₁
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_ps₁
  simp only [
    wellTypedPolicies_preserves_isAuthorized hinst hwt₁,
  ]
  apply verifyAlwaysAllows_is_sound hwf_εnv₁ hok hunsat env _ hwf_ps₁
  exact ofEnv_soundness hwf_ps₁.1 hinst

/-- Concrete version of `verifyAlwaysAllows_is_complete`. -/
theorem verifyAlwaysAllows_is_ok_and_complete {ps₁ ps₁' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .ok ps₁' →
  ∃ asserts,
    verifyAlwaysAllows ps₁' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicies ps₁' ∧
        ¬ allows (Spec.isAuthorized env.request env.entities ps₁))
:= by
  intros hwf hwt₁
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have ⟨asserts, hok⟩ := verifyAlwaysAllows_is_ok hwf hwt₁
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env₁, henum_comp, hres⟩ := verifyAlwaysAllows_is_complete hwf_εnv₁ hok hsat
  have hinst := ofEnv_completeness hwf hswf_env₁.1 henum_comp hmodel
  simp only [
    ←wellTypedPolicies_preserves_isAuthorized hinst hwt₁,
  ] at hres
  exists env

end Cedar.Thm
