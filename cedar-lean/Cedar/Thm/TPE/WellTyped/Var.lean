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

theorem partial_eval_well_typed_var {env : TypeEnv} {v : Var} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  PEWellTyped env (Residual.var v ty) (TPE.evaluate (Residual.var v ty) preq pes) req preq es pes
:= by
  unfold PEWellTyped
  intro h_wf h_ref h_wt
  rcases h_ref with ⟨h_rref, h_eref⟩
  simp only [TPE.evaluate]
  unfold varₚ
  cases v
  case principal =>
    simp only [Option.pure_def, Option.bind_eq_bind]
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, _⟩
    cases h : preq.principal.asEntityUID
    case none =>
      assumption
    case some =>
      simp only [Option.bind_some, varₚ.varₒ, someOrSelf]
      rw [h] at h_pv
      cases h_pv with | some _ h₃ =>
      cases h_wt with | var h₄ =>
      cases h₄ with | principal =>
      rcases h_wf with ⟨_, ⟨h_principal, _, _, _⟩, _⟩
      rw [h₃]
      simp only [someOrSelf, Value.asResidualValue]
      exact well_typed_entity h_principal
  case resource =>
    simp only [Option.pure_def, Option.bind_eq_bind]
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨_, ⟨_, h_rv, _⟩⟩
    cases h : preq.resource.asEntityUID
    . dsimp only [Option.bind_none, varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp only [Option.bind_some, varₚ.varₒ, someOrSelf]
      rw [h] at h_rv
      cases h_rv with | some _ h₃ =>
      cases h_wt with | var h₄ =>
      cases h₄ with | resource =>
      rcases h_wf with ⟨_, ⟨_, _, h_resource, _⟩, _⟩
      rw [h₃]
      simp only [someOrSelf, Value.asResidualValue]
      exact well_typed_entity h_resource
  case action =>
    simp only [varₚ.varₒ, someOrSelf]
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    -- Action is always concrete in partial requests
    cases h_wt with | var h₄ =>
    cases h₄ with | action =>
    rcases h_wf with ⟨hwf, ⟨_, h_action, _, _⟩, _⟩
    have : InstanceOfEntityType env.reqty.action env.reqty.action.ty env := by
      have ⟨_, _, _, hwf_act, _⟩ := hwf
      simp [InstanceOfEntityType, EntityUID.WellFormed, ActionSchema.contains, hwf_act]
    rw [←h_av, h_action]
    simp only [someOrSelf, Value.asResidualValue]
    exact well_typed_entity this
  case context =>
    simp only
    cases h : preq.context
    · -- none: varₚ returns .var .context ty (the default)
      simp [varₚ, Option.bind, Option.getD]
      exact h_wt
    · -- some attrs: varₚ returns PartialValue.asResidual (.record attrs) (.var .context ty) ty
      simp [varₚ, Option.bind, Option.getD, PartialValue.asResidual]
      -- Need: WellTyped env (.val (toResidualValue (.var .context ty) (.record attrs) ty) ty)
      -- This requires showing toResidualValue produces a well-typed ResidualValue
      -- which needs the ValueRefines from h_cv and the type information from h_wt
      sorry
