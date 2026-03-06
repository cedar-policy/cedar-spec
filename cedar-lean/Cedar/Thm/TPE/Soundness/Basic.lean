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


import Cedar.TPE
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.ErrorFree
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped
import Cedar.Thm.Data.Control

/-!
This file contains basic utility theorems used in the TPE soundness proof.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

theorem asValue_some {r : Residual} {v : Value} :
  r.asValue = .some v ↔ (∃ ty, r = .val v ty)
:= by
  simp only [Residual.asValue]
  split
  · simp
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact not_exists.mpr (h v)

theorem asValue_evaluate_val {r : Residual} {v : Value} :
  r.asValue = .some v → ∀ req es, r.evaluate req es = Except.ok v
:= by
  simp only [asValue_some, forall_exists_index]
  intro _ hv
  simp [hv, Residual.evaluate]

theorem isError_evaluate_err {r : Spec.Residual} :
  r.isError → ∀ req es, ∃ e, r.evaluate req es = .error e
:= by
  intro h
  simp only [Residual.isError] at h
  split at h <;> cases h
  simp [Spec.Residual.evaluate]

end Cedar.Thm
