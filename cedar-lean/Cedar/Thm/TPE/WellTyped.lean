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
import Cedar.Thm.Validation.WellTyped.ResidualDefinition

/-!
This file contains theorems about partial evaluation preserving well-typedness of residuals.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

/--
Theorem: Partial evaluation preserves well-typedness of residuals.

If a residual is well-typed in some type environment, then partially evaluating it
with a partial request and partial entities produces another well-typed residual
in the same type environment.

This is a fundamental property ensuring that the partial evaluation process
maintains type safety throughout the computation.
-/
theorem partial_evaluation_preserves_residual_well_typedness
  {env : TypeEnv}
  {res : Residual}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  {pes : PartialEntities} :
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env res →
  Residual.WellTyped env (TPE.evaluate res preq pes) := by
  intro h_wf h_ref h_wt
  unfold RequestAndEntitiesRefine at h_ref
  rcases h_ref with ⟨h_rref, h_eref⟩
  -- Proof by cases on the structure of the residual
  cases res with
  | val v ty =>
    -- Case: .val v ty
    -- TPE.evaluate (.val v ty) req es = .val v ty
    simp [TPE.evaluate]
    exact h_wt
  | var v ty =>
    simp [TPE.evaluate]
    unfold varₚ
    cases v with
    | principal =>
      simp
      unfold RequestRefines at h_rref
      rcases h_rref with ⟨h_pv, h_rest⟩
      cases preq.principal.asEntityUID with
      | some id =>
        sorry
      | none =>
        dsimp [varₚ.varₒ, someOrSelf]
        exact h_wt
    | _ => sorry
  | error ty =>
    -- Case: .error ty
    -- TPE.evaluate (.error ty) req es = .error ty
    simp [TPE.evaluate]
    exact h_wt
  | _ => sorry
end Cedar.Thm
