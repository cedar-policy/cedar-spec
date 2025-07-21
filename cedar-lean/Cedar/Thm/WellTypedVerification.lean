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

import Cedar.Thm.SymCC.Verifier.Basic
import Cedar.Thm.SymCC.WellTyped
import Cedar.Thm.Verification

/-!
This file strengthens theorems in `Cedar.Thm.Verification` to
reduce some assumptions on `SymEnv` to `TypeEnv`.
--/

namespace Cedar.Thm

open Spec SymCC Validation

theorem verifyNeverErrors_is_ok_and_sound {p p' : Policy} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicy p Γ = .some p' →
  ∃ asserts,
    verifyNeverErrors p' (SymEnv.ofEnv Γ) = .ok asserts ∧
    SymEnv.ofEnv Γ ⊭ asserts →
      ∀ env : Env,
        InstanceOfWellFormedEnvironment env.request env.entities Γ →
        -- TODO: Ideally, use `p` instead of `p'` here.
        env.StronglyWellFormedForPolicy p' →
        (evaluate p'.toExpr env.request env.entities).isOk
:= by
  intros hwf hwt
  have hwf_εnv := ofEnv_swf_for_policy hwf hwt
  have ⟨asserts, hok⟩ := verifyNeverErrors_is_ok hwf hwt
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_env
  apply verifyNeverErrors_is_sound hwf_εnv hok hunsat env
  · exact ofEnv_soundness hwf_env.1 hinst
  · exact hwf_env

theorem verifyEquivalent_is_ok_and_sound {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv} :
  Γ.WellFormed →
  wellTypedPolicies ps₁ Γ = .some ps₁' →
  wellTypedPolicies ps₂ Γ = .some ps₂' →
  ∃ asserts,
    verifyEquivalent ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts ∧
    SymEnv.ofEnv Γ ⊭ asserts →
    ∀ env : Env,
      InstanceOfWellFormedEnvironment env.request env.entities Γ →
      -- TODO: Ideally, use `p₁`/`p₂` instead of `p₁'`/`p₂'` here.
      env.StronglyWellFormedForPolicies ps₁' →
      env.StronglyWellFormedForPolicies ps₂' →
      bothAllowOrBothDeny
        (Spec.isAuthorized env.request env.entities ps₁')
        (Spec.isAuthorized env.request env.entities ps₂')
:= by
  intros hwf hwt₁ hwt₂
  have hwf_εnv₁ := ofEnv_swf_for_policies hwf hwt₁
  have hwf_εnv₂ := ofEnv_swf_for_policies hwf hwt₂
  have ⟨asserts, hok⟩ := verifyEquivalent_is_ok hwf hwt₁ hwt₂
  exists asserts
  simp only [hok, true_and]
  intros hunsat env hinst hwf_ps₁ hwf_ps₂
  apply verifyEquivalent_is_sound hwf_εnv₁ hwf_εnv₂ hok hunsat env _ hwf_ps₁ hwf_ps₂
  exact ofEnv_soundness hwf_ps₁.1 hinst

end Cedar.Thm
