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
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

import Cedar.Thm.TPE.WellTyped.Basic

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

theorem partial_eval_well_typed_and {env : TypeEnv} {a b : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate a preq pes) →
  Residual.WellTyped env (TPE.evaluate b preq pes) →
  PEWellTyped env (Residual.and a b ty) (TPE.evaluate (Residual.and a b ty) preq pes) req preq es pes
:= by
  intros h_a_wt h_b_wt h_wf h_ref h_wt
  simp only [TPE.evaluate]
  cases h_wt with
  | and h_a h_b h_ty_a h_ty_b =>
    unfold TPE.and
    split
    . exact h_b_wt
    . exact well_typed_bool
    . apply Residual.WellTyped.error
    . exact h_a_wt
    · split
      · exact well_typed_bool
      · rename_i bty h_eval_b _ _ _ _
        replace h_ty_b : bty = CedarType.bool BoolType.anyBool := by
          replace h_ty_b' := partial_eval_preserves_typeof _ h_b preq pes
          simp only [h_eval_b, h_ty_b] at h_ty_b'
          simpa [Residual.typeOf] using h_ty_b'
        apply Residual.WellTyped.and
        · exact h_a_wt
        · rw [h_ty_b]
          exact well_typed_bool
        · rw [partial_eval_preserves_typeof _ h_a]
          exact h_ty_a
        · simp [h_ty_b, Residual.typeOf]
    . apply Residual.WellTyped.and
      · exact h_a_wt
      · exact h_b_wt
      · rw [partial_eval_preserves_typeof _ h_a]
        exact h_ty_a
      · rw [partial_eval_preserves_typeof _ h_b]
        exact h_ty_b
