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
  IsConsistent req₁ es₁ req₂ es₂ →
  (Spec.evaluate x.toExpr req₁ es₁).toOption = (Residual.evaluate (Cedar.TPE.evaluate x req₂ es₂) req₁ es₁).toOption
:= by
  intro h₁ h₂ h₃
  induction h₁
  case lit =>
    exact partial_evaluate_is_sound_lit
  case var =>
    exact partial_evaluate_is_sound_var h₃
  case ite x₁ x₂ x₃ hwt _ _ hₜ _ hᵢ₁ hᵢ₂ hᵢ₃ =>
    exact partial_evaluate_is_sound_ite h₂ hwt hₜ hᵢ₁ hᵢ₂ hᵢ₃
  case and x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    exact partial_evaluate_is_sound_and h₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆
  case or x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    exact partial_evaluate_is_sound_or h₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆
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

theorem partial_evaluate_policy_is_sound
  {schema : Schema}
  {residual : Residual}
  {env : Environment}
  {policy : Policy}
  {req₁ : Request}
  {es₁ : Entities}
  {req₂ : PartialRequest}
  {es₂ : PartialEntities} :
  evaluatePolicy schema policy req₂ es₂ = .ok residual   →
  isConsistent env req₁ es₁ req₂ es₂ = .ok () →
  (Spec.evaluate policy.toExpr req₁ es₁).toOption = (Residual.evaluate residual req₁ es₁).toOption
:= by
  intro h₁ h₂
  simp [evaluatePolicy] at h₁
  split at h₁ <;> try cases h₁
  split at h₁ <;> try cases h₁
  simp [do_ok] at h₁
  rcases h₁ with ⟨_, ⟨_, h₁₁⟩, h₁₂⟩
  simp [Except.mapError] at h₁₁
  split at h₁₁ <;> try cases h₁₁
  rename_i env _ _ ty _ _ heq
  have : RequestAndEntitiesMatchEnvironment env req₁ es₁ := by sorry
  have h₃ := typechecked_is_well_typed_after_lifting this heq
  have h₄ : (Spec.evaluate ty.liftBoolTypes.toExpr req₁ es₁).toOption = (Residual.evaluate (Cedar.TPE.evaluate ty.liftBoolTypes req₂ es₂) req₁ es₁).toOption := by sorry
  rw [←type_lifting_preserves_evaluation_results, ←type_lifting_preserves_tpe_results, h₁₂] at h₄
  /- missing pieces:
  * type lifting preserves TPE results (see unproven theorem: type_lifting_preserves_tpe_results)
  * connection between result of `typeOf` and its input in terms of evaluation
  -/
  sorry
end Cedar.Thm
