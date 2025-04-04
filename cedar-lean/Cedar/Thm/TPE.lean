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
import Cedar.Thm.TPE.Evaluator
import Cedar.Thm.TPE.Soundness
import Cedar.Thm.Validation

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

theorem partial_evaluate_is_sound
  {x : TypedExpr}
  {req₁ : Request}
  {es₁ : Entities}
  {req₂ : PartialRequest}
  {es₂ : PartialEntities}
  {env : Environment} :
  TypedExpr.WellTyped env x →
  RequestAndEntitiesMatchEnvironment env req₁ es₁ →
  -- Do we need this hypothesis?
  -- I doubt that because `RequestAndEntitiesMatchEnvironment` ∧ `IsConsistent` → `PartialRequestAndEntitiesMatchEnvironment`
  -- not the other way around, unless we make `IsConsistent` stronger to consider the types of request/entities.
  -- Nevertheless, we should only need one of them.
  PartialRequestAndEntitiesMatchEnvironment env req₂ es₂ →
  IsConsistent req₁ es₁ req₂ es₂ →
  (Spec.evaluate x.toExpr req₁ es₁).toOption = (Residual.evaluate (Cedar.TPE.evaluate x req₂ es₂) req₁ es₁).toOption
:= by
  intro h₁ h₂ h₃ h₄
  induction h₁
  case lit =>
    exact partial_evaluate_is_sound_lit
  case var =>
    exact partial_evaluate_is_sound_var h₄
  case ite x₁ x₂ x₃ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ hᵢ₇ hᵢ₈ =>
    exact partial_evaluate_is_sound_ite h₂ hᵢ₁ hᵢ₄ hᵢ₆ hᵢ₇ hᵢ₈
  case and x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    exact partial_evaluate_is_sound_and h₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆
  case or x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    exact partial_evaluate_is_sound_or h₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆
  case unaryApp op₁ x₁ ty hᵢ₁ hᵢ₂ hᵢ₃ =>
    exact partial_evaluate_is_sound_unary_app hᵢ₃
  case binaryApp op₂ x₁ x₂ ty hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ =>
    exact partial_evaluate_is_sound_binary_app h₂ h₄ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅
  case hasAttr_entity ety rty x₁ attr hᵢ₁ hᵢ₂ => sorry
  case hasAttr_record rty x₁ attr hᵢ₁ hᵢ₂ => sorry
  case getAttr_entity ety rty x₁ attr ty hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ => sorry
  case getAttr_record rty x₁ attr ty hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ => sorry
  case set ls ty hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ => sorry
  case record rty m hᵢ₁ hᵢ₂ hᵢ₃ => sorry
  case call xfn args ty hᵢ₁ hᵢ₂ hᵢ₃ => sorry

end Cedar.Thm
