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
  (x.evaluate req es).toOption = ((Cedar.TPE.evaluate x preq pes).evaluate req es).toOption
:= by
  intro h₁ h₂ h₃
  induction h₁
  case val =>
    exact partial_evaluate_is_sound_val
  case var =>
    exact partial_evaluate_is_sound_var h₃
  case ite x₁ x₂ x₃ hwt _ _ hₜ _ hᵢ₁ hᵢ₂ hᵢ₃ =>
    exact partial_evaluate_is_sound_ite h₂ hwt hₜ hᵢ₁ hᵢ₂ hᵢ₃
  case and x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    exact partial_evaluate_is_sound_and h₂ h₃ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆
  case or x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    exact partial_evaluate_is_sound_or h₂ h₃ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆
  case unaryApp op₁ x₁ ty hᵢ₁ =>
    exact partial_evaluate_is_sound_unary_app hᵢ₁
  case binaryApp op₂ x₁ x₂ ty _ hwt howt hᵢ₁ hᵢ₂ =>
    exact partial_evaluate_is_sound_binary_app h₂ h₃ hwt howt hᵢ₁ hᵢ₂
  case hasAttr_entity ety x₁ attr hᵢ₁ =>
    exact partial_evaluate_is_sound_has_attr h₃ hᵢ₁
  case hasAttr_record rty x₁ attr hᵢ₁ =>
    exact partial_evaluate_is_sound_has_attr h₃ hᵢ₁
  case getAttr_entity ety rty x₁ attr ty hᵢ₁ =>
    exact partial_evaluate_is_sound_get_attr h₃ hᵢ₁
  case getAttr_record rty x₁ attr ty hᵢ₁ =>
    exact partial_evaluate_is_sound_get_attr h₃ hᵢ₁
  case set ls ty hᵢ₁ =>
    exact partial_evaluate_is_sound_set hᵢ₁
  case record rty m hᵢ₁ hᵢ₁ =>
    exact partial_evaluate_is_sound_record hᵢ₁
  case call xfn args ty hᵢ₁ =>
    exact partial_evaluate_is_sound_call hᵢ₁
  case error ty =>
    exact partial_evaluate_is_sound_error

end Cedar.Thm
