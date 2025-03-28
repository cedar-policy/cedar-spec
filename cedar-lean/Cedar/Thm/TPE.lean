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
  TypedExpr.WellTyped env x →
  IsConsistent env req₁ es₁ req₂ es₂ →
  TPE.evaluate x req₂ es₂ = .val v ty →
  Spec.evaluate x.toExpr req₁ es₁ = .ok v
:= by
  intro h₁ h₂ h₃
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
  case _ => sorry
  case _ => sorry

theorem partial_evaluate_is_sound
  {x : TypedExpr}
  {req₁ : Request}
  {es₁ : Entities}
  {req₂ : PartialRequest}
  {es₂ : PartialEntities}
  {env : Environment} :
  TypedExpr.WellTyped env x →
  RequestAndEntitiesMatchEnvironment env req₁ es₁ →
  PartialRequestAndEntitiesMatchEnvironment env req₂ es₂ →
  IsConsistent env req₁ es₁ req₂ es₂ →
  (Spec.evaluate x.toExpr req₁ es₁).toOption = (Residual.evaluate (Cedar.TPE.evaluate x req₂ es₂) req₁ es₁).toOption
:= by
  sorry

end Cedar.Thm
