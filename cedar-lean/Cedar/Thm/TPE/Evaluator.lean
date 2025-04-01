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
import Cedar.Thm

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

theorem partial_evaluate_value
  {x : TypedExpr}
  {req₁ : Request}
  {es₁ : Entities}
  {req₂ : PartialRequest}
  {es₂ : PartialEntities}
  {env : Environment}
  {v : Value}
  {ty : CedarType} :
  RequestAndEntitiesMatchEnvironment env req₁ es₁ →
  TypedExpr.WellTyped env x →
  IsConsistent req₁ es₁ req₂ es₂ →
  TPE.evaluate x req₂ es₂ = .val v ty →
  Spec.evaluate x.toExpr req₁ es₁ = .ok v
:= by
  intro h₀ h₁ h₂ h₃
  induction h₁ generalizing v ty
  case ite x₁ x₂ x₃ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ hᵢ₇ hᵢ₈ =>
    simp [TypedExpr.toExpr]
    simp [TPE.evaluate, TPE.ite] at h₃
    generalize h₁ᵢ : TPE.evaluate x₁ req₂ es₂ = res₁
    split at h₃ <;> try simp at h₃
    rename_i b _ heq
    cases b <;> simp at h₃ <;> simp [Spec.evaluate, hᵢ₆ heq, Result.as, Coe.coe, Value.asBool]
    · exact hᵢ₈ h₃
    · exact hᵢ₇ h₃
  case and x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    simp [TypedExpr.toExpr]
    simp [TPE.evaluate, TPE.and] at h₃
    generalize h₁ᵢ : TPE.evaluate x₁ req₂ es₂ = res₁
    split at h₃ <;> try simp at h₃
    case _ heq =>
      specialize hᵢ₅ heq
      specialize hᵢ₆ h₃
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool, hᵢ₆]
      replace hᵢ₆ := well_typed_is_sound h₀ hᵢ₂ hᵢ₆
      simp [hᵢ₄] at hᵢ₆
      rcases instance_of_anyBool_is_bool hᵢ₆ with ⟨b, hᵢ₆⟩
      simp only [hᵢ₆, Except.map_ok]
    case _ heq =>
      specialize hᵢ₅ heq
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool]
      exact h₃.left
    case _ heq _ _ _ =>
      specialize hᵢ₅ h₃
      have h₄ := well_typed_is_sound h₀ hᵢ₁ hᵢ₅
      simp [hᵢ₃] at h₄
      rcases instance_of_anyBool_is_bool h₄ with ⟨b, h₄⟩
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, h₄, Value.asBool]
      specialize hᵢ₆ heq
      simp only [hᵢ₆, Except.map_ok, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq,
        Bool.true_eq, imp_self]
  case or x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

end Cedar.Thm
