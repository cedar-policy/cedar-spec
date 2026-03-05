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

theorem partial_eval_well_typed_ite {env : TypeEnv} {c t e : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate c preq pes) →
  Residual.WellTyped env (TPE.evaluate t preq pes) →
  Residual.WellTyped env (TPE.evaluate e preq pes) →
  PEWellTyped env (Residual.ite c t e ty) (TPE.evaluate (Residual.ite c t e ty) preq pes) req preq es pes
:= by
  intros h_c_wt h_t_wt h_e_wt h_wf h_ref h_wt
  simp only [TPE.evaluate]
  cases h_wt with
  | ite h_c h_t h_e h_ty_c h_ty_t =>
    unfold TPE.ite
    split
    . split
      · exact h_t_wt
      · exact h_e_wt
    . apply Residual.WellTyped.error
    . have h_t_type_eq := partial_eval_preserves_typeof _ h_t preq pes
      rw [←h_t_type_eq]
      apply Residual.WellTyped.ite
      · exact h_c_wt
      · exact h_t_wt
      · exact h_e_wt
      · rw [partial_eval_preserves_typeof _ h_c]
        exact h_ty_c
      · rw [partial_eval_preserves_typeof _ h_t]
        rw [partial_eval_preserves_typeof _ h_e]
        exact h_ty_t
