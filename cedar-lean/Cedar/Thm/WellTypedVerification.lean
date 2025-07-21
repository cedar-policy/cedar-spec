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

import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.SymCC.Verifier
import Cedar.Thm.SymCC.Env.Soundness
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymbolicCompilation
import Cedar.Thm.Verification

/-!
This file strengthens theorems in `Cedar.Thm.Verification` to
reduce some assumptions on `SymEnv` to `TypeEnv`.
--/

namespace Cedar.Thm

open Spec SymCC Validation

/--
If inputs are sufficiently well-formed, then `verifyEvaluate` always succeeds.
-/
theorem verifyEvaluate_is_ok {φ : Term → Term} {p p' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicy p Γ = .some p') :
  ∃ asserts, verifyEvaluate φ p' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  have ⟨tx, hwt_tx, heq_tx⟩ := wellTypedPolicy_some_implies_well_typed_expr hwt
  simp only [verifyEvaluate]
  have ⟨_, hok, _⟩ := compile_well_typed hwf hwt_tx
  simp only [heq_tx] at hok
  simp [hok]

theorem verifyNeverErrors_is_ok {p p' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicy p Γ = .some p') :
  ∃ asserts, verifyNeverErrors p' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyEvaluate_is_ok hwf hwt

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
  have ⟨asserts, hok⟩ := verifyNeverErrors_is_ok hwf hwt
  exists asserts
  simp only [hok, true_and]
  have hwf_εnv := ofEnv_swf_for_policy hwf hwt
  intros hunsat env hinst hwf_env
  apply verifyNeverErrors_is_sound hwf_εnv hok hunsat env
  · exact ofEnv_soundness hwf_env.1 hinst
  · exact hwf_env

end Cedar.Thm
