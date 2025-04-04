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

theorem to_option_eq_f {α ε} {res₁ res₂ res₃ res₄: Except ε α} (f : α → α → Except ε α):
  Except.toOption res₁ = Except.toOption res₃ →
  Except.toOption res₂ = Except.toOption res₄ →
  Except.toOption (do let x ← res₁; let y ← res₂; f x y) = Except.toOption (do let x ← res₃; let y ← res₄; f x y)
:= by
  intro h₁ h₂
  simp [Except.toOption] at *
  split at h₁ <;>
  split at h₁ <;>
  split at h₂ <;>
  split at h₂ <;>
  simp at h₁ <;>
  simp at h₂
  case _ => subst h₁; subst h₂; simp only [Except.bind_ok]
  case _ => simp only [Except.bind_err, Except.bind_ok]
  case _ => simp only [Except.bind_ok, Except.bind_err]
  case _ => simp only [Except.bind_err]

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

theorem partial_evaluate_is_sound_binary_app
{op₂ : BinaryOp}
{ty : CedarType}
{x₁ x₂ : TypedExpr}
{req₁ : Request}
{es₁ : Entities}
{req₂ : PartialRequest}
{es₂ : PartialEntities}
{env : Environment}
(h₂ : RequestAndEntitiesMatchEnvironment env req₁ es₁)
(h₄ : IsConsistent req₁ es₁ req₂ es₂)
(hᵢ₂ : TypedExpr.WellTyped env x₂)
(hᵢ₃ : BinaryOp.WellTyped env op₂ x₁ x₂ ty)
(hᵢ₄ : Except.toOption (Spec.evaluate x₁.toExpr req₁ es₁) = Except.toOption ((TPE.evaluate x₁ req₂ es₂).evaluate req₁ es₁))
(hᵢ₅ : Except.toOption (Spec.evaluate x₂.toExpr req₁ es₁) = Except.toOption ((TPE.evaluate x₂ req₂ es₂).evaluate req₁ es₁)) :
  Except.toOption (Spec.evaluate (TypedExpr.binaryApp op₂ x₁ x₂ ty).toExpr req₁ es₁) =
  Except.toOption ((TPE.evaluate (TypedExpr.binaryApp op₂ x₁ x₂ ty) req₂ es₂).evaluate req₁ es₁)
:= by
  simp [TPE.evaluate, TPE.apply₂]
  split
  case _ heq₁ heq₂ =>
    -- TODO: rewrite `Residual.asValue` using standard lib so that we can use theorems to unwrap it
    simp [Residual.asValue] at heq₁
    simp [Residual.asValue] at heq₂
    split at heq₁ <;> cases heq₁
    split at heq₂ <;> cases heq₂
    rename_i heq₁ _ _ heq₂
    simp [heq₁, Residual.evaluate] at hᵢ₄
    simp [heq₂, Residual.evaluate] at hᵢ₅
    replace hᵢ₄ := to_option_right_ok' hᵢ₄
    replace hᵢ₅ := to_option_right_ok' hᵢ₅
    simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
    -- TODO: rewrite one of the two binary app evaluation function so that we don't need this amount of case splits.
    split <;> simp [Residual.evaluate]
    case _ =>
      simp [intOrErr, someOrError]
      split <;> split
      case _ heq₃ _ _ _ _ heq₄ =>
        simp [Option.bind_eq_some] at heq₄
        rcases heq₄ with ⟨_, heq₄₁, heq₄₂⟩
        subst heq₄₂
        simp [heq₃] at heq₄₁
        subst heq₄₁
        simp [Residual.evaluate]
      case _ heq₃ _ _ _ heq₄ =>
        simp only [heq₃, Option.some_bind, reduceCtorEq] at heq₄
      case _ heq₃ _ _ _ _ heq₄ =>
        simp only [heq₃, Option.none_bind, reduceCtorEq] at heq₄
      case _ =>
        simp only [Except.toOption, Residual.evaluate]
    case _ =>
      simp [intOrErr, someOrError]
      split <;> split
      case _ heq₃ _ _ _ _ heq₄ =>
        simp [Option.bind_eq_some] at heq₄
        rcases heq₄ with ⟨_, heq₄₁, heq₄₂⟩
        subst heq₄₂
        simp [heq₃] at heq₄₁
        subst heq₄₁
        simp [Residual.evaluate]
      case _ heq₃ _ _ _ heq₄ =>
        simp only [heq₃, Option.some_bind, reduceCtorEq] at heq₄
      case _ heq₃ _ _ _ _ heq₄ =>
        simp only [heq₃, Option.none_bind, reduceCtorEq] at heq₄
      case _ =>
        simp only [Except.toOption, Residual.evaluate]
    case _ =>
      simp [intOrErr, someOrError]
      split <;> split
      case _ heq₃ _ _ _ _ heq₄ =>
        simp [Option.bind_eq_some] at heq₄
        rcases heq₄ with ⟨_, heq₄₁, heq₄₂⟩
        subst heq₄₂
        simp [heq₃] at heq₄₁
        subst heq₄₁
        simp [Residual.evaluate]
      case _ heq₃ _ _ _ heq₄ =>
        simp only [heq₃, Option.some_bind, reduceCtorEq] at heq₄
      case _ heq₃ _ _ _ _ heq₄ =>
        simp only [heq₃, Option.none_bind, reduceCtorEq] at heq₄
      case _ =>
        simp only [Except.toOption, Residual.evaluate]
    case _ uid₁ uid₂ =>
      simp [apply₂.self, heq₁, heq₂, someOrSelf]
      split
      case _ heq₃ =>
        simp only [Option.bind_eq_some] at heq₃
        rcases heq₃ with ⟨_, heq₃₁, heq₃₂⟩
        simp only [Option.some.injEq] at heq₃₂
        subst heq₃₂
        simp [Residual.evaluate]
        simp [TPE.inₑ] at heq₃₁
        split at heq₃₁
        case _ heq₄ =>
          simp at heq₃₁
          subst heq₃₁
          simp [Spec.inₑ, heq₄]
        case _ heq₄ =>
          simp [Option.map] at heq₃₁
          split at heq₃₁ <;> cases heq₃₁
          rename_i heq₅
          simp [PartialEntities.ancestors, PartialEntities.get, Option.bind_eq_some] at heq₅
          rcases heq₅ with ⟨data, heq₅₁, heq₅₂⟩
          simp [IsConsistent, EntitiesAreConsistent] at h₄
          rcases h₄ with ⟨_, h₄⟩
          specialize h₄ uid₁ data heq₅₁
          rcases h₄ with ⟨_, h₄₁, _, h₄₂, _⟩
          rw [heq₅₂] at h₄₂
          cases h₄₂
          rename_i h₄₂
          simp [Spec.inₑ, Entities.ancestorsOrEmpty, h₄₁, ←h₄₂]
          have : (uid₁ == uid₂) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq, heq₄, not_false_eq_true]
          simp only [this, Bool.false_or]
      case _ heq₃ =>
        simp only [Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ =>
      simp [apply₂.self, heq₁, heq₂, someOrSelf]
      split
      case _ vs _ _ _ _ _ heq₃ =>
        simp only [Option.bind_eq_some] at heq₃
        rcases heq₃ with ⟨_, heq₃₁, heq₃₂⟩
        simp only [Option.some.injEq] at heq₃₂
        subst heq₃₂
        simp [Spec.inₛ]
        cases hᵢ₃ <;>
        (rename_i h₅; have h₆ := well_typed_is_sound h₂ hᵢ₂ hᵢ₅; rw [h₅] at h₆; cases h₆)
        rename_i h₆
        simp [Data.Set.mapOrErr]
        generalize h₇ : List.mapM Value.asEntityUID vs.elts = res
        cases res
        case _ =>
          rcases List.mapM_error_implies_exists_error h₇ with ⟨v, h₇₁, h₇₂⟩
          specialize h₆ v h₇₁
          rcases instance_of_entity_type_is_entity h₆ with ⟨_, _, h₆⟩
          simp only [Value.asEntityUID, h₆, reduceCtorEq] at h₇₂
        case _ =>
          simp [Data.Set.make_any_iff_any]
          simp [TPE.inₛ, Option.bind_eq_some, Data.Set.toList] at heq₃₁
          rcases heq₃₁ with ⟨vs', heq₃₁, heq₃₂⟩
          rw [List.mapM_some_iff_forall₂] at heq₃₁
          have heq₄ : List.Forall₂ (fun x y => x.asEntityUID = .ok y) vs.elts vs' := by
            have : ∀ x y, (Except.toOption ∘ Value.asEntityUID) x = some y → x.asEntityUID = .ok y := by
              intro x y h
              simp [Except.toOption] at h
              split at h <;> cases h
              rename_i heq
              exact heq
            exact List.Forall₂.imp this heq₃₁
          rw [←List.mapM_ok_iff_forall₂] at heq₄
          simp [heq₄] at h₇
          subst h₇
          simp [Spec.inₑ]
          simp [TPE.inₑ] at heq₃₂
          simp [IsConsistent] at h₄
          replace heq₃₂ := anyM_any h₄.right heq₃₂
          subst heq₃₂
          simp only [Residual.evaluate]
      case _ =>
        simp only [Spec.inₛ, Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ uid _ =>
      simp [someOrSelf, apply₂.self]
      split
      case _ heq =>
        rw [Option.bind_eq_some] at heq
        rcases heq with ⟨_, heq₁, heq₂⟩
        simp at heq₂
        subst heq₂
        simp [TPE.hasTag] at heq₁
        rcases heq₁ with ⟨_, heq₁, heq₂⟩
        simp [PartialEntities.tags, PartialEntities.get] at heq₁
        rw [Option.bind_eq_some] at heq₁
        rcases heq₁ with ⟨data, heq₃, heq₄⟩
        subst heq₂
        simp [IsConsistent, EntitiesAreConsistent] at h₄
        rcases h₄ with ⟨_, h₄⟩
        specialize h₄ uid data heq₃
        rcases h₄ with ⟨_, h₄₁, _, _, h₄₂⟩
        rw [heq₄] at h₄₂
        cases h₄₂
        rename_i heq₅
        subst heq₅
        simp only [Spec.hasTag, Entities.tagsOrEmpty, h₄₁, Residual.evaluate]
      case _ =>
        simp only [heq₁, heq₂, Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ uid _ =>
      simp [TPE.getTag, someOrError]
      split
      case _ heq =>
        simp [PartialEntities.tags, PartialEntities.get] at heq
        rw [Option.bind_eq_some] at heq
        rcases heq with ⟨data, heq₂, heq₃⟩
        simp [IsConsistent, EntitiesAreConsistent] at h₄
        rcases h₄ with ⟨_, h₄⟩
        specialize h₄ uid data heq₂
        rcases h₄ with ⟨_, h₄₁, _, _, h₄₂⟩
        rw [heq₃] at h₄₂
        cases h₄₂
        rename_i heq₄
        subst heq₄
        simp only [Spec.getTag, Entities.tags, Data.Map.findOrErr, h₄₁]
        split <;>
        (rename_i heq₁; simp [heq₁, Residual.evaluate, Except.toOption])
      case _ =>
        simp only [Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ => simp [Except.toOption]
  case _ =>
    split
    case _ heq =>
      simp [heq, Residual.evaluate] at hᵢ₄
      rcases to_option_right_err hᵢ₄ with ⟨_, hᵢ₄⟩
      simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₄, Residual.evaluate, Except.toOption]
    case _ heq _ =>
      simp [heq, Residual.evaluate] at hᵢ₅
      rcases to_option_right_err hᵢ₅ with ⟨_, hᵢ₅⟩
      simp only [TypedExpr.toExpr, Spec.evaluate, hᵢ₅, Except.bind_err, do_error_to_option,
        Residual.evaluate]
      simp only [Except.toOption]
    case _ =>
      simp [TypedExpr.toExpr, Spec.evaluate, apply₂.self, Residual.evaluate]
      exact to_option_eq_f
        (λ x y => Spec.apply₂ op₂ x y es₁) hᵢ₄ hᵢ₅
end Cedar.Thm
