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

/-- Concrete version of `verifyAlwaysMatches_is_sound`. -/
theorem verifyAlwaysMatches_is_ok_and_sound {p p' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p Γ = .ok p' →
  ∃ asserts,
    verifyAlwaysMatches p' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicy p' →
        evaluate p.toExpr env.request env.entities = .ok (.prim (.bool true)))
:= by
  intros hwf hwt
  have hwf_εnv := ofEnv_swf_for_policy hwf hwt
  have ⟨asserts, hok⟩ := verifyAlwaysMatches_is_ok hwf hwt
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_env
  simp only [wellTypedPolicy_preserves_evaluation hinst hwt]
  have := verifyEvaluate_is_sound verifyAlwaysMatches_wbeq hwf_εnv hok hunsat env
  simp [beq_iff_eq] at this
  apply this _ hwf_env
  exact ofEnv_soundness hwf_env.1 hinst

/-- Concrete version of `verifyAlwaysMatches_is_complete`. -/
theorem verifyAlwaysMatches_is_ok_and_complete {p p' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p Γ = .ok p' →
  ∃ asserts,
    verifyAlwaysMatches p' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicy p' ∧
        evaluate p.toExpr env.request env.entities ≠ .ok (.prim (.bool true)))
:= by
  intros hwf hwt
  have hwf_εnv := ofEnv_swf_for_policy hwf hwt
  have ⟨asserts, hok⟩ := verifyAlwaysMatches_is_ok hwf hwt
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env, henum_comp, hres⟩ := verifyEvaluate_is_complete verifyAlwaysMatches_wbeq hwf_εnv hok hsat
  have hinst := ofEnv_completeness hwf hswf_env.1 henum_comp hmodel
  have := wellTypedPolicy_preserves_evaluation hinst hwt
  simp only [←wellTypedPolicy_preserves_evaluation hinst hwt] at hres
  exists env
  simp [this] at hres
  simp [*]

/-- Concrete version of `verifyNeverMatches_is_sound`. -/
theorem verifyNeverMatches_is_ok_and_sound {p p' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p Γ = .ok p' →
  ∃ asserts,
    verifyNeverMatches p' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicy p' →
        evaluate p.toExpr env.request env.entities ≠ .ok (.prim (.bool true)))
:= by
  intros hwf hwt
  have hwf_εnv := ofEnv_swf_for_policy hwf hwt
  have ⟨asserts, hok⟩ := verifyNeverMatches_is_ok hwf hwt
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_env
  simp only [wellTypedPolicy_preserves_evaluation hinst hwt]
  have := verifyEvaluate_is_sound verifyNeverMatches_wbeq hwf_εnv hok hunsat env
  simp only [bne_iff_ne] at this
  apply this _ hwf_env
  exact ofEnv_soundness hwf_env.1 hinst

/-- Concrete version of `verifyNeverMatches_is_complete`. -/
theorem verifyNeverMatches_is_ok_and_complete {p p' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p Γ = .ok p' →
  ∃ asserts,
    verifyNeverMatches p' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicy p' ∧
        evaluate p.toExpr env.request env.entities = .ok (.prim (.bool true)))
:= by
  intros hwf hwt
  have hwf_εnv := ofEnv_swf_for_policy hwf hwt
  have ⟨asserts, hok⟩ := verifyNeverMatches_is_ok hwf hwt
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env, henum_comp, hres⟩ := verifyEvaluate_is_complete verifyNeverMatches_wbeq hwf_εnv hok hsat
  have hinst := ofEnv_completeness hwf hswf_env.1 henum_comp hmodel
  have := wellTypedPolicy_preserves_evaluation hinst hwt
  simp only [←wellTypedPolicy_preserves_evaluation hinst hwt] at hres
  exists env
  simp [this] at hres
  simp [*]

/-- Concrete version of `verifyMatchesEquivalent_is_sound`. -/
theorem verifyMatchesEquivalent_is_ok_and_sound {p₁ p₁' p₂ p₂' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p₁ Γ = .ok p₁' →
  wellTypedPolicy p₂ Γ = .ok p₂' →
  ∃ asserts,
    verifyMatchesEquivalent p₁' p₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicy p₁' →
        env.StronglyWellFormedForPolicy p₂' →
        (evaluate p₁.toExpr env.request env.entities = .ok (.prim (.bool true))) =
        (evaluate p₂.toExpr env.request env.entities = .ok (.prim (.bool true))))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policy hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policy hwf hwt₂
  have ⟨asserts, hok⟩ := verifyMatchesEquivalent_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_env₁ hwf_env₂
  simp only [
    wellTypedPolicy_preserves_evaluation hinst hwt₁,
    wellTypedPolicy_preserves_evaluation hinst hwt₂,
  ]
  apply verifyMatchesEquivalent_is_sound hwf_εnv₁ hwf_εnv₂ hok hunsat env _ hwf_env₁ hwf_env₂
  exact ofEnv_soundness hwf_env₁.1 hinst

/-- Concrete version of `verifyMatchesEquivalent_is_complete`. -/
theorem verifyMatchesEquivalent_is_ok_and_complete {p₁ p₁' p₂ p₂' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p₁ Γ = .ok p₁' →
  wellTypedPolicy p₂ Γ = .ok p₂' →
  ∃ asserts,
    verifyMatchesEquivalent p₁' p₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicy p₁' ∧
        env.StronglyWellFormedForPolicy p₂' ∧
        (evaluate p₁.toExpr env.request env.entities = .ok (.prim (.bool true))) ≠
        (evaluate p₂.toExpr env.request env.entities = .ok (.prim (.bool true))))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policy hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policy hwf hwt₂
  have ⟨asserts, hok⟩ := verifyMatchesEquivalent_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env₁, hswf_env₂, henum_comp, hres⟩ := verifyMatchesEquivalent_is_complete hwf_εnv₁ hwf_εnv₂ hok hsat
  have hinst := ofEnv_completeness hwf hswf_env₁.1 henum_comp hmodel
  simp only [
    ←wellTypedPolicy_preserves_evaluation hinst hwt₁,
    ←wellTypedPolicy_preserves_evaluation hinst hwt₂,
  ] at hres
  exists env

/-- Concrete version of `verifyMatchesImplies_is_sound`. -/
theorem verifyMatchesImplies_is_ok_and_sound {p₁ p₁' p₂ p₂' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p₁ Γ = .ok p₁' →
  wellTypedPolicy p₂ Γ = .ok p₂' →
  ∃ asserts,
    verifyMatchesImplies p₁' p₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicy p₁' →
        env.StronglyWellFormedForPolicy p₂' →
        evaluate p₁.toExpr env.request env.entities = .ok (.prim (.bool true)) →
        evaluate p₂.toExpr env.request env.entities = .ok (.prim (.bool true)))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policy hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policy hwf hwt₂
  have ⟨asserts, hok⟩ := verifyMatchesImplies_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_env₁ hwf_env₂ h₁
  simp only [
    wellTypedPolicy_preserves_evaluation hinst hwt₁,
    wellTypedPolicy_preserves_evaluation hinst hwt₂,
  ] at h₁ ⊢
  apply verifyMatchesImplies_is_sound hwf_εnv₁ hwf_εnv₂ hok hunsat env _ hwf_env₁ hwf_env₂ h₁
  exact ofEnv_soundness hwf_env₁.1 hinst

/-- Concrete version of `verifyMatchesImplies_is_complete`. -/
theorem verifyMatchesImplies_is_ok_and_complete {p₁ p₁' p₂ p₂' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p₁ Γ = .ok p₁' →
  wellTypedPolicy p₂ Γ = .ok p₂' →
  ∃ asserts,
    verifyMatchesImplies p₁' p₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicy p₁' ∧
        env.StronglyWellFormedForPolicy p₂' ∧
        evaluate p₁.toExpr env.request env.entities = .ok (.prim (.bool true)) ∧
        evaluate p₂.toExpr env.request env.entities ≠ .ok (.prim (.bool true)))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policy hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policy hwf hwt₂
  have ⟨asserts, hok⟩ := verifyMatchesImplies_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env₁, hswf_env₂, henum_comp, hres⟩ := verifyMatchesImplies_is_complete hwf_εnv₁ hwf_εnv₂ hok hsat
  have hinst := ofEnv_completeness hwf hswf_env₁.1 henum_comp hmodel
  simp only [
    ←wellTypedPolicy_preserves_evaluation hinst hwt₁,
    ←wellTypedPolicy_preserves_evaluation hinst hwt₂,
  ] at hres
  exists env

/-- Concrete version of `verifyMatchesDisjoint_is_sound`. -/
theorem verifyMatchesDisjoint_is_ok_and_sound {p₁ p₁' p₂ p₂' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p₁ Γ = .ok p₁' →
  wellTypedPolicy p₂ Γ = .ok p₂' →
  ∃ asserts,
    verifyMatchesDisjoint p₁' p₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        env.StronglyWellFormedForPolicy p₁' →
        env.StronglyWellFormedForPolicy p₂' →
        ¬ (evaluate p₁.toExpr env.request env.entities = .ok (.prim (.bool true)) ∧
           evaluate p₂.toExpr env.request env.entities = .ok (.prim (.bool true))))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policy hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policy hwf hwt₂
  have ⟨asserts, hok⟩ := verifyMatchesDisjoint_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_env₁ hwf_env₂
  simp only [
    wellTypedPolicy_preserves_evaluation hinst hwt₁,
    wellTypedPolicy_preserves_evaluation hinst hwt₂,
  ]
  apply verifyMatchesDisjoint_is_sound hwf_εnv₁ hwf_εnv₂ hok hunsat env _ hwf_env₁ hwf_env₂
  exact ofEnv_soundness hwf_env₁.1 hinst

/-- Concrete version of `verifyMatchesDisjoint_is_complete`. -/
theorem verifyMatchesDisjoint_is_ok_and_complete {p₁ p₁' p₂ p₂' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p₁ Γ = .ok p₁' →
  wellTypedPolicy p₂ Γ = .ok p₂' →
  ∃ asserts,
    verifyMatchesDisjoint p₁' p₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    (SymEnv.ofEnv Γ ⊧ asserts →
      ∃ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ ∧
        env.StronglyWellFormedForPolicy p₁' ∧
        env.StronglyWellFormedForPolicy p₂' ∧
        evaluate p₁.toExpr env.request env.entities = .ok (.prim (.bool true)) ∧
        evaluate p₂.toExpr env.request env.entities = .ok (.prim (.bool true)))
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policy hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policy hwf hwt₂
  have ⟨asserts, hok⟩ := verifyMatchesDisjoint_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hsat
  have ⟨env, hmodel, hswf_env₁, hswf_env₂, henum_comp, hres⟩ := verifyMatchesDisjoint_is_complete hwf_εnv₁ hwf_εnv₂ hok hsat
  have hinst := ofEnv_completeness hwf hswf_env₁.1 henum_comp hmodel
  simp only [
    ←wellTypedPolicy_preserves_evaluation hinst hwt₁,
    ←wellTypedPolicy_preserves_evaluation hinst hwt₂,
  ] at hres
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
