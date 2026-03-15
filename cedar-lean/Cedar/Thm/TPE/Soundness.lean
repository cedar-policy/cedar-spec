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
import Cedar.Thm.TPE.Soundness.Var
import Cedar.Thm.TPE.Soundness.And
import Cedar.Thm.TPE.Soundness.Or
import Cedar.Thm.TPE.Soundness.IfThenElse
import Cedar.Thm.TPE.Soundness.Unary
import Cedar.Thm.TPE.Soundness.Binary
import Cedar.Thm.TPE.Soundness.HasAttr
import Cedar.Thm.TPE.Soundness.GetAttr
import Cedar.Thm.TPE.Soundness.Set
import Cedar.Thm.TPE.Soundness.Record
import Cedar.Thm.TPE.Soundness.Call

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

theorem partial_evaluate_is_sound_error
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{ty : CedarType} :
  Except.toOption ((Residual.error ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.error ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, Residual.evaluate]

/-- The main lemma: Evaluating a residual derived from partially evaluating
a well-typed expression is equivalent to that of evaluating the original
expression, provided that requests and entities are consistent. The equivalency
is defined using `Except.toOption`.
-/
theorem partial_evaluate_is_sound
  {x : Residual}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {env : TypeEnv} :
  Residual.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine env req es preq pes →
  rTargetCorrect x req es →
  (x.evaluate req es).toOption = ((Cedar.TPE.evaluate x preq pes).evaluate req es).toOption
:= by
  intro h₁ h₂ h₃ htc
  induction h₁ with
  | val => exact partial_evaluate_is_sound_val
  | var => exact partial_evaluate_is_sound_var h₃
  | unaryApp _ _ hᵢ₁ =>
    cases htc with | unaryApp hx =>
    exact partial_evaluate_is_sound_unary_app (hᵢ₁ hx)
  | error => exact partial_evaluate_is_sound_error
  | ite hwt₁ _ _ hₜ _ hᵢ₁ hᵢ₂ hᵢ₃ =>
    cases htc with | ite hc ht he =>
    exact partial_evaluate_is_sound_ite h₂ hwt₁ hₜ (hᵢ₁ hc) (hᵢ₂ ht) (hᵢ₃ he)
  | and hwt₁ hwt₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    cases htc with | and ha hb =>
    exact partial_evaluate_is_sound_and h₂ h₃ hwt₁ hwt₂ hᵢ₃ hᵢ₄ (hᵢ₅ ha) (hᵢ₆ hb) sorry sorry
  | or hwt₁ hwt₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    cases htc with | or ha hb =>
    exact partial_evaluate_is_sound_or h₂ h₃ hwt₁ hwt₂ hᵢ₃ hᵢ₄ (hᵢ₅ ha) (hᵢ₆ hb) sorry sorry
  | binaryApp _ hwt howt hᵢ₁ hᵢ₂ =>
    cases htc with | binaryApp hx hy =>
    exact partial_evaluate_is_sound_binary_app h₂ h₃ hwt howt (hᵢ₁ hx) (hᵢ₂ hy)
  | hasAttr_entity _ _ hᵢ₁ =>
    cases htc with | hasAttr hx =>
    exact partial_evaluate_is_sound_has_attr h₃ (hᵢ₁ hx)
  | hasAttr_record _ _ hᵢ₁ =>
    cases htc with | hasAttr hx =>
    exact partial_evaluate_is_sound_has_attr h₃ (hᵢ₁ hx)
  | getAttr_entity _ _ _ _ ih =>
    cases htc with | getAttr hx =>
    exact partial_evaluate_is_sound_get_attr h₃ (ih hx)
  | getAttr_record _ _ _ ih =>
    cases htc with | getAttr hx =>
    exact partial_evaluate_is_sound_get_attr h₃ (ih hx)
  | set _ _ _ ih =>
    cases htc with | set hxs =>
    exact partial_evaluate_is_sound_set (fun x hx => ih x hx (hxs x hx))
  | record _ _ ih =>
    cases htc with | record htcm =>
    exact partial_evaluate_is_sound_record (fun k v hkv => ih k v hkv (htcm k v hkv))
  | call _ _ ih =>
    cases htc with | call hargs =>
    exact partial_evaluate_is_sound_call (fun x hx => ih x hx (hargs x hx))

end Cedar.Thm
