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

/-- The reductions only ever decide a boolean. -/
theorem try_decide_has_residual_is_bool
  {env : TypeEnv} {r : Residual} {a : Attr} {v : Value}
  (hdec : TPE.tryDecideHasResidual env r a = .some v) :
  ∃ b : Bool, v = .prim (.bool b)
:= by
  unfold TPE.tryDecideHasResidual at hdec
  repeat' split at hdec
  all_goals simp only [Option.some.injEq, reduceCtorEq] at hdec
  all_goals exact ⟨_, hdec.symm⟩

/-- The residual `has` produces when it cannot decide the attribute is well
typed, since partial evaluation preserves the operand's type. -/
private theorem has_attr_residual_well_typed
  {env : TypeEnv} {expr : Residual} {attr : Attr} {ty : CedarType}
  {preq : PartialRequest} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate env expr preq pes) →
  Residual.WellTyped env (Residual.hasAttr expr attr ty) →
  Residual.WellTyped env (Residual.hasAttr (TPE.evaluate env expr preq pes) attr ty)
:= by
  intros h_expr_wt h_wt
  cases h_wt
  case hasAttr_entity ety h₅ h₆ =>
    apply Residual.WellTyped.hasAttr_entity
    case h₁ => exact h_expr_wt
    case h₂ =>
      have h₁₀ := partial_eval_preserves_typeof _ h₅
      rw [h₁₀, h₆]
  case hasAttr_record rty h₆ h₇ =>
    apply Residual.WellTyped.hasAttr_record
    case h₁ => exact h_expr_wt
    case h₂ =>
      have h₁₀ := partial_eval_preserves_typeof _ h₆
      rw [h₁₀, h₇]

theorem partial_eval_well_typed_hasAttr {env : TypeEnv} {expr : Residual} {attr : Attr} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate env expr preq pes) →
  PEWellTyped env (Residual.hasAttr expr attr ty) (TPE.evaluate env (Residual.hasAttr expr attr ty) preq pes) req preq es pes
:= by
  intros h_expr_wt h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.hasAttr]
  split
  case h_1 =>
    apply Residual.WellTyped.error
  case h_2 r₁ h₁ =>
    split
    case h_1 hdec =>
      have ⟨_, hb⟩ := try_decide_has_residual_is_bool hdec
      subst hb
      cases h_wt <;> exact well_typed_bool
    case h_2 =>
    split
    case h_1 | h_2 | h_3 | h_4 => cases h_wt <;> exact well_typed_bool
    case h_5 => exact has_attr_residual_well_typed h_expr_wt h_wt
