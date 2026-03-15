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

import Cedar.Thm.TPE.Soundness.Basic

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

theorem partial_evaluate_is_sound_has_attr
{x₁ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
{attr : Attr}
(h₄ : RequestAndEntitiesRefine env req es preq pes)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(htc : rTargetCorrect (TPE.evaluate x₁ preq pes) req es) :
  Except.toOption ((x₁.hasAttr attr (CedarType.bool BoolType.anyBool)).evaluate req es) =
  Except.toOption ((TPE.evaluate (x₁.hasAttr attr (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
:= by
  simp only [TPE.evaluate]
  cases hr : TPE.evaluate x₁ preq pes with
  | error ty' =>
    rw [hr] at hᵢ₁; simp only [Residual.evaluate_error] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨e, he⟩
    simp only [TPE.hasAttr, hr, Residual.evaluate_error, Except.toOption,
               Residual.evaluate_hasAttr, he, Except.bind_err]
  | val rv rty =>
    rw [hr] at hᵢ₁ htc; rw [rTargetCorrect_val] at htc
    obtain ⟨v_tpe, hv_tpe⟩ := htc
    simp only [Residual.evaluate_val, hv_tpe, Except.toOption] at hᵢ₁
    have hx₁ : x₁.evaluate req es = .ok v_tpe := by
      cases hx : x₁.evaluate req es <;> simp_all [Except.toOption]
    simp only [TPE.hasAttr]
    cases rv with
    | record m =>
      simp only []
      split
      next hfind =>
        have h := record_evaluate_hasAttr_present hv_tpe hfind
        simp only [Residual.evaluate_val, Residual.evaluate_hasAttr, hx₁, Except.bind_ok, Except.toOption, h, ResidualValue.evaluate_prim]
      next hfind =>
        have h := record_evaluate_hasAttr_unknown hv_tpe hfind
        simp only [Residual.evaluate_hasAttr, Except.toOption, hx₁, Except.bind_ok, h]
      next hfind =>
        have h := record_evaluate_hasAttr_none hv_tpe hfind
        simp only [Residual.evaluate_val, Residual.evaluate_hasAttr, hx₁, Except.bind_ok, Except.toOption, h, ResidualValue.evaluate_prim]
    | prim p =>
      cases p with
      | entityUID uid => sorry -- entity case
      | _ => grind [Residual.evaluate_hasAttr, Residual.evaluate_val, Except.bind_ok]
    | _ => grind [Residual.evaluate_hasAttr, Residual.evaluate_val, Except.bind_ok]
  | _ =>
    rw [hr] at hᵢ₁
    simp only [TPE.hasAttr, hr]
    exact hasAttr_sound_of_sound hᵢ₁

end Cedar.Thm
