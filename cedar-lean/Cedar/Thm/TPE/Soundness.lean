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
import Cedar.Thm.Validation
import Cedar.Thm.TPE.Evaluator

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

theorem partial_evaluate_is_sound_lit
{p : Prim}
{req₁ : Request}
{es₁ : Entities}
{req₂ : PartialRequest}
{es₂ : PartialEntities}
{ty : CedarType} :
  Except.toOption (Spec.evaluate (TypedExpr.lit p ty).toExpr req₁ es₁) =
  Except.toOption ((TPE.evaluate (TypedExpr.lit p ty) req₂ es₂).evaluate req₁ es₁)
:= by
  simp [TypedExpr.toExpr, Spec.evaluate, TPE.evaluate, Residual.evaluate]

theorem partial_evaluate_is_sound_var
{req₁ : Request}
{es₁ : Entities}
{req₂ : PartialRequest}
{es₂ : PartialEntities}
{v : Var}
{ty : CedarType}
(h₄ : IsConsistent req₁ es₁ req₂ es₂) :
  Except.toOption (Spec.evaluate (TypedExpr.var v ty).toExpr req₁ es₁) =
  Except.toOption ((TPE.evaluate (TypedExpr.var v ty) req₂ es₂).evaluate req₁ es₁)
:= by
  simp [TPE.evaluate, varₚ, TypedExpr.toExpr]
  split <;>
  simp [Spec.evaluate, varₚ.varₒ, someOrSelf]
  case _ =>
    split
    case _ heq =>
      simp [Option.bind_eq_some] at heq
      rcases heq with ⟨_, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      simp [IsConsistent, RequestIsConsistent] at h₄
      rcases h₄ with ⟨⟨h₄, _⟩, _⟩
      rw [heq₁] at h₄
      cases h₄
      rename_i heq₂
      subst heq₂
      rfl
    case _ heq =>
      simp only [Residual.evaluate]
  case _ =>
    split
    case _ heq =>
      simp [Option.bind_eq_some] at heq
      rcases heq with ⟨_, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      simp [IsConsistent, RequestIsConsistent] at h₄
      rcases h₄ with ⟨⟨_, ⟨_, ⟨h₄, _⟩⟩⟩, _⟩
      rw [heq₁] at h₄
      cases h₄
      rename_i heq₂
      subst heq₂
      rfl
    case _ heq =>
      simp only [Residual.evaluate]
  case _ =>
    simp [Residual.evaluate]
    simp [IsConsistent, RequestIsConsistent] at h₄
    rcases h₄ with ⟨⟨_, ⟨h₄, _⟩⟩, _⟩
    rw [h₄]
  case _ =>
    split
    case _ heq =>
      simp at heq
      rcases heq with ⟨_, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      simp [IsConsistent, RequestIsConsistent] at h₄
      rcases h₄ with ⟨⟨_, ⟨_, ⟨_, h₄⟩⟩⟩, _⟩
      rw [heq₁] at h₄
      cases h₄
      rename_i heq₂
      subst heq₂
      rfl
    case _ =>
      simp only [Residual.evaluate]

theorem partial_evaluate_is_sound_and
{x₁ x₂ : TypedExpr}
{req₁ : Request}
{es₁ : Entities}
{req₂ : PartialRequest}
{es₂ : PartialEntities}
{env : Environment}
(h₂ : RequestAndEntitiesMatchEnvironment env req₁ es₁)
(hᵢ₁ : TypedExpr.WellTyped env x₁)
(hᵢ₂ : TypedExpr.WellTyped env x₂)
(hᵢ₃ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₄ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₅ : Except.toOption (Spec.evaluate x₁.toExpr req₁ es₁) = Except.toOption ((TPE.evaluate x₁ req₂ es₂).evaluate req₁ es₁))
(hᵢ₆ : Except.toOption (Spec.evaluate x₂.toExpr req₁ es₁) = Except.toOption ((TPE.evaluate x₂ req₂ es₂).evaluate req₁ es₁)) :
  Except.toOption (Spec.evaluate (x₁.and x₂ (CedarType.bool BoolType.anyBool)).toExpr req₁ es₁) =
  Except.toOption ((TPE.evaluate (x₁.and x₂ (CedarType.bool BoolType.anyBool)) req₂ es₂).evaluate req₁ es₁)
:= by
  simp [TPE.evaluate, TPE.and]
  split
  case _ ty heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [TypedExpr.toExpr, Spec.evaluate, h₅, Result.as, Coe.coe, Value.asBool]
    split
    case _ heq₁ =>
      have h₆ := well_typed_is_sound h₂ hᵢ₂ heq₁
      rw [hᵢ₄] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      replace hᵢ₆ := to_option_left_ok hᵢ₆ heq₁
      simp only [h₆, Except.map_ok, hᵢ₆]
    case _ heq₁ =>
      simp only [Except.map_error]
      rw [heq₁] at hᵢ₆
      rcases to_option_left_err hᵢ₆ with ⟨_, hᵢ₆⟩
      simp only [hᵢ₆, Except.toOption]
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [TypedExpr.toExpr, Spec.evaluate, h₅, Result.as, Coe.coe, Value.asBool, Residual.evaluate]
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    rcases to_option_right_err hᵢ₅ with ⟨_, hᵢ₅⟩
    simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₅, Result.as, Residual.evaluate, Except.toOption]
  case _ heq _ _ _ =>
    simp [heq, Residual.evaluate] at hᵢ₆
    have h₅ := to_option_right_ok' hᵢ₆
    simp [TypedExpr.toExpr, Spec.evaluate]
    generalize h₆ : Spec.evaluate x₁.toExpr req₁ es₁ = res₁
    cases res₁
    case ok =>
      have h₇ := well_typed_is_sound h₂ hᵢ₁ h₆
      rw [hᵢ₃] at h₇
      rcases instance_of_anyBool_is_bool h₇ with ⟨_, h₇⟩
      simp [h₇, Result.as, Coe.coe, Value.asBool]
      split
      case _ heq₁ =>
        subst heq₁
        rw [h₇] at h₆
        rw [←h₆]
        exact hᵢ₅
      case _ heq₁ =>
        simp [h₅]
        simp at heq₁
        subst heq₁
        subst h₇
        rw [←h₆]
        exact hᵢ₅
    case error =>
      simp [h₆] at hᵢ₅
      rcases to_option_left_err hᵢ₅ with ⟨_, hᵢ₅⟩
      simp [h₆, Result.as, hᵢ₅, Except.toOption]
  case _ =>
    simp [TypedExpr.toExpr, Spec.evaluate]
    generalize h₅ : Spec.evaluate x₁.toExpr req₁ es₁ = res₁
    cases res₁
    case ok =>
      have h₆ := well_typed_is_sound h₂ hᵢ₁ h₅
      rw [hᵢ₃] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      subst h₆
      replace h₅ := to_option_left_ok hᵢ₅ h₅
      simp [Result.as, Coe.coe, Residual.evaluate, h₅, Value.asBool]
      -- TODO: maybe we can use something like
      -- Except.toOption a = Except.toOption b → Except.toOption (f a) = Except.toOption (f b)
      generalize h₇ : Spec.evaluate x₂.toExpr req₁ es₁ = res₂
      cases res₂
      case _ =>
        rw [h₇] at hᵢ₆
        rcases to_option_left_err hᵢ₆ with ⟨_, hᵢ₆⟩
        simp [hᵢ₆]
        split <;> simp [Except.toOption]
      case _ =>
        replace h₇ := to_option_left_ok hᵢ₆ h₇
        rw [h₇]
    case error =>
      rw [h₅] at hᵢ₅
      rcases to_option_left_err hᵢ₅ with ⟨_, hᵢ₅⟩
      simp [Result.as, Residual.evaluate, hᵢ₅, Except.toOption]

theorem partial_evaluate_is_sound_ite
{x₁ x₂ x₃ : TypedExpr}
{req₁ : Request}
{es₁ : Entities}
{req₂ : PartialRequest}
{es₂ : PartialEntities}
{env : Environment}
(h₂ : RequestAndEntitiesMatchEnvironment env req₁ es₁)
(hᵢ₁ : TypedExpr.WellTyped env x₁)
(hᵢ₄ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₆ : Except.toOption (Spec.evaluate x₁.toExpr req₁ es₁) = Except.toOption ((TPE.evaluate x₁ req₂ es₂).evaluate req₁ es₁))
(hᵢ₇ : Except.toOption (Spec.evaluate x₂.toExpr req₁ es₁) = Except.toOption ((TPE.evaluate x₂ req₂ es₂).evaluate req₁ es₁))
(hᵢ₈ : Except.toOption (Spec.evaluate x₃.toExpr req₁ es₁) = Except.toOption ((TPE.evaluate x₃ req₂ es₂).evaluate req₁ es₁)) :
  Except.toOption (Spec.evaluate (x₁.ite x₂ x₃ x₂.typeOf).toExpr req₁ es₁) =
  Except.toOption ((TPE.evaluate (x₁.ite x₂ x₃ x₂.typeOf) req₂ es₂).evaluate req₁ es₁) := by
  simp [TypedExpr.toExpr, TPE.evaluate, TPE.ite]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₆
    have h₆ := to_option_right_ok' hᵢ₆
    split
    case isTrue heq =>
      simp [Spec.evaluate, h₆, Result.as, Coe.coe, Value.asBool, heq]
      exact hᵢ₇
    case isFalse heq =>
      simp [Spec.evaluate, h₆, Result.as, Coe.coe, Value.asBool, heq]
      exact hᵢ₈
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₆
    rcases to_option_right_err hᵢ₆ with ⟨_, h₆⟩
    simp [Spec.evaluate, h₆, Result.as, Residual.evaluate, Except.toOption]
  case _ =>
    simp [Spec.evaluate]
    generalize h₅ : Spec.evaluate x₁.toExpr req₁ es₁ = res₁
    cases res₁
    case ok =>
      simp [Result.as, Coe.coe]
      have h₆ := well_typed_is_sound h₂ hᵢ₁ h₅
      simp [hᵢ₄] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      subst h₆
      simp [Value.asBool]
      replace hᵢ₆ := to_option_left_ok hᵢ₆ h₅
      simp [Residual.evaluate, hᵢ₆, Value.asBool]
      split
      case _ => exact hᵢ₇
      case _ => exact hᵢ₈
    case error =>
      simp [Result.as, Except.toOption]
      simp [h₅] at hᵢ₆
      rcases to_option_left_err hᵢ₆ with ⟨_, hᵢ₆⟩
      simp only [Residual.evaluate, hᵢ₆, Except.bind_err]

theorem partial_evaluate_is_sound_or
{x₁ x₂ : TypedExpr}
{req₁ : Request}
{es₁ : Entities}
{req₂ : PartialRequest}
{es₂ : PartialEntities}
{env : Environment}
(h₂ : RequestAndEntitiesMatchEnvironment env req₁ es₁)
(hᵢ₁ : TypedExpr.WellTyped env x₁)
(hᵢ₂ : TypedExpr.WellTyped env x₂)
(hᵢ₃ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₄ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₅ : Except.toOption (Spec.evaluate x₁.toExpr req₁ es₁) = Except.toOption ((TPE.evaluate x₁ req₂ es₂).evaluate req₁ es₁))
(hᵢ₆ : Except.toOption (Spec.evaluate x₂.toExpr req₁ es₁) = Except.toOption ((TPE.evaluate x₂ req₂ es₂).evaluate req₁ es₁)) :
  Except.toOption (Spec.evaluate (x₁.or x₂ (CedarType.bool BoolType.anyBool)).toExpr req₁ es₁) =
  Except.toOption ((TPE.evaluate (x₁.or x₂ (CedarType.bool BoolType.anyBool)) req₂ es₂).evaluate req₁ es₁)
:= by
  simp [TPE.evaluate, TPE.or]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [TypedExpr.toExpr, Spec.evaluate, h₅, Result.as, Coe.coe, Value.asBool, Residual.evaluate]
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [TypedExpr.toExpr, Spec.evaluate, h₅, Result.as, Coe.coe, Value.asBool]
    generalize h₆ : Spec.evaluate x₂.toExpr req₁ es₁ = res₂
    cases res₂
    case error =>
      simp [←h₆]
      exact hᵢ₆
    case ok =>
      have h₇ := well_typed_is_sound h₂ hᵢ₂ h₆
      rw [hᵢ₄] at h₇
      rcases instance_of_anyBool_is_bool h₇ with ⟨_, h₇⟩
      subst h₇
      simp [←h₆]
      exact hᵢ₆
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    rcases to_option_right_err hᵢ₅ with ⟨_, hᵢ₅⟩
    simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₅, Result.as, Residual.evaluate, Except.toOption]
  case _ heq _ _ _ =>
    simp [heq, Residual.evaluate] at hᵢ₆
    have hᵢ₇ := to_option_right_ok' hᵢ₆
    generalize h₅ : Spec.evaluate x₁.toExpr req₁ es₁ = res₁
    cases res₁
    case error =>
      simp [TypedExpr.toExpr, Spec.evaluate, h₅, Result.as]
      rw [←h₅]
      exact hᵢ₅
    case ok =>
      have h₆ := well_typed_is_sound h₂ hᵢ₁ h₅
      rw [hᵢ₃] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      simp [TypedExpr.toExpr, Spec.evaluate, h₅, h₆, Result.as, Coe.coe, Value.asBool, hᵢ₇]
      split
      case _ heq₁ =>
        subst heq₁
        rw [h₆] at h₅
        rw [←h₅]
        exact hᵢ₅
      case _ heq₁ =>
        simp only [Bool.not_eq_true] at heq₁
        subst heq₁
        rw [h₆] at h₅
        rw [←h₅]
        exact hᵢ₅
  case _ =>
    simp [TypedExpr.toExpr, Spec.evaluate]
    generalize h₅ : Spec.evaluate x₁.toExpr req₁ es₁ = res₁
    cases res₁
    case ok =>
      simp [Result.as, Coe.coe]
      have h₆ := well_typed_is_sound h₂ hᵢ₁ h₅
      simp [hᵢ₃] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      subst h₆
      simp [Value.asBool]
      have hᵢ₇ := to_option_left_ok hᵢ₅ h₅
      simp [Residual.evaluate, hᵢ₇, Result.as, Coe.coe, Value.asBool]
      split
      case _ => rfl
      case _ =>
        generalize h₇ : Spec.evaluate x₂.toExpr req₁ es₁ = res₂
        cases res₂
        case _ =>
          rw [h₇] at hᵢ₆
          rcases to_option_left_err hᵢ₆ with ⟨_, hᵢ₆⟩
          simp [hᵢ₆]
          simp [Except.toOption]
        case _ =>
          replace hᵢ₆ := to_option_left_ok hᵢ₆ h₇
          rw [hᵢ₆]
    case error =>
      simp [Result.as, Except.toOption]
      simp [h₅] at hᵢ₅
      rcases to_option_left_err hᵢ₅ with ⟨_, hᵢ₅⟩
      simp [Residual.evaluate, hᵢ₅, Result.as]

theorem partial_evaluate_is_sound_unary_app
{x₁ : TypedExpr}
{req₁ : Request}
{es₁ : Entities}
{req₂ : PartialRequest}
{es₂ : PartialEntities}
{op₁ : UnaryOp}
{ty : CedarType}
(hᵢ₃ : Except.toOption (Spec.evaluate x₁.toExpr req₁ es₁) = Except.toOption ((TPE.evaluate x₁ req₂ es₂).evaluate req₁ es₁)) :
  Except.toOption (Spec.evaluate (TypedExpr.unaryApp op₁ x₁ ty).toExpr req₁ es₁) =
  Except.toOption ((TPE.evaluate (TypedExpr.unaryApp op₁ x₁ ty) req₂ es₂).evaluate req₁ es₁)
:= by
  simp [TPE.evaluate, TPE.apply₁]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₃
    rcases to_option_right_err hᵢ₃ with ⟨_, hᵢ₃⟩
    simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₃, Residual.evaluate, Except.toOption]
  case _ =>
    split <;>
    (rename_i heq; simp [Residual.asValue] at heq; split at heq) <;>
    simp at heq
    case _ heq₁ =>
      subst heq
      simp [heq₁, Residual.evaluate] at hᵢ₃
      replace hᵢ₃ := to_option_right_ok' hᵢ₃
      simp [someOrError, TypedExpr.toExpr, Spec.evaluate, hᵢ₃]
      split
      case _ heq₂ =>
        replace heq₂ := to_option_some heq₂
        simp [heq₂, Residual.evaluate]
      case _ heq₂ =>
        rcases to_option_none heq₂ with ⟨_, heq₂⟩
        simp [heq₂, Residual.evaluate, Except.toOption]
    case _ =>
      simp [Residual.evaluate, TypedExpr.toExpr, Spec.evaluate]
      generalize h₅ : Spec.evaluate x₁.toExpr req₁ es₁ = res₁
      cases res₁
      case error =>
        simp [h₅] at hᵢ₃
        rcases to_option_left_err hᵢ₃ with ⟨_, hᵢ₃⟩
        simp [hᵢ₃, Except.toOption]
      case ok =>
        simp [h₅] at hᵢ₃
        replace hᵢ₃ := to_option_left_ok' hᵢ₃
        simp [hᵢ₃]
end Cedar.Thm
