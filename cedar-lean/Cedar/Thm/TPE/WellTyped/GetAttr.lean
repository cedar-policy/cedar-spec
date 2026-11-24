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
import Cedar.Thm.TPE.State

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

/-- The residual `getAttr` produces when it cannot decide the attribute is
well typed, since partial evaluation preserves the operand's type. -/
theorem get_attr_residual_well_typed
  {env : TypeEnv} {expr : Residual} {attr : Attr} {ty : CedarType}
  {preq : PartialRequest} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate env expr preq pes) →
  Residual.WellTyped env (Residual.getAttr expr attr ty) →
  Residual.WellTyped env (Residual.getAttr (TPE.evaluate env expr preq pes) attr ty)
:= by
  intros h_expr_wt h_wt
  cases h_wt
  case getAttr_entity ety rty h₅ h₆ h₇ h₈ =>
    apply Residual.WellTyped.getAttr_entity
    case h₁ => exact h_expr_wt
    case h₂ =>
      have h₉ := partial_eval_preserves_typeof _ h₆
      rw [h₉, h₇]
    case h₃ => rw [h₅]
    case h₄ => exact h₈
  case getAttr_record rty h₆ h₇ h₈ =>
    apply Residual.WellTyped.getAttr_record
    case h₁ => exact h_expr_wt
    case h₂ =>
      have h₁₀ := partial_eval_preserves_typeof _ h₆
      rw [h₁₀, h₇]
    case h₃ => rw [h₈]

theorem partial_eval_well_typed_getAttr {env : TypeEnv} {expr : Residual} {attr : Attr} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate env expr preq pes) →
  PEWellTyped env (Residual.getAttr expr attr ty) (TPE.evaluate env (Residual.getAttr expr attr ty) preq pes) req preq es pes
:= by
  intros h_expr_wt h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.getAttr]
  split
  case h_1 => exact .error
  case h_2 =>
    -- reducing the access to what TPE knows about the attribute preserves
    -- well-typedness, since that knowledge describes the value the access
    -- itself would produce
    have hself := get_attr_residual_well_typed h_expr_wt h_wt
    refine stateToResidual_well_typed h_wf ?_ hself rfl
    simpa only [Residual.evaluate, bind, Except.bind] using
      attrStateAt_sound (a := attr) h_wf h_ref h_expr_wt
