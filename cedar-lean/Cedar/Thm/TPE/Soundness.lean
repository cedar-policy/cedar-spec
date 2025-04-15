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
import Cedar.Thm.WellTyped

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

theorem as_value_some {r : Residual} {v : Value} :
  r.asValue = .some v → (∃ ty, r = .val v ty)
:= by
  intro h
  simp only [Residual.asValue] at h
  split at h <;> simp at h
  subst h
  simp only [Residual.val.injEq, true_and, exists_eq']

theorem anyM_some_implies_any {α} {xs : List α} {b : Bool}  (f : α → Option Bool) (g : α → Bool) :
(∀ x b, f x = some b → g x = b) → List.anyM f xs = some b → xs.any g = b
:= by
  intro h₁ h₂
  induction xs generalizing b
  case nil =>
    simp only [List.anyM, Option.pure_def, Option.some.injEq, Bool.false_eq] at h₂
    simp only [List.any_nil, h₂]
  case cons head tail hᵢ =>
    simp only [List.any_cons]
    simp only [List.anyM, Option.pure_def, Option.bind_eq_bind] at h₂
    generalize h₃ : f head = res
    cases res <;> simp [h₃] at h₂
    case some =>
      split at h₂
      case _ =>
        simp only [Option.some.injEq, Bool.true_eq] at h₂
        subst h₂
        specialize h₁ head true h₃
        simp only [h₁, Bool.true_or]
      case _ =>
        specialize hᵢ h₂
        simp only [hᵢ, Bool.or_iff_right_iff_imp]
        specialize h₁ head false h₃
        simp only [h₁, Bool.false_eq_true, false_implies]

theorem to_option_eq_do₁ {α β ε} {res₁ res₂: Except ε α} (f : α → Except ε β) :
  Except.toOption res₁ = Except.toOption res₂ →
  Except.toOption (do let x ← res₁; f x) = Except.toOption (do let x ← res₂; f x)
:= by
  intro h₁
  simp [Except.toOption] at *
  split at h₁ <;>
  split at h₁ <;>
  simp at h₁
  case _ => subst h₁; simp only [Except.bind_ok]
  case _ => simp only [Except.bind_err]

theorem to_option_eq_map {α β ε} {res₁ res₂: Except ε α} (f : α → β) :
  Except.toOption res₁ = Except.toOption res₂ →
  Except.toOption (f <$> res₁) = Except.toOption (f <$> res₂)
:= by
  intro h₁
  simp [Except.toOption] at *
  split at h₁ <;>
  split at h₁ <;>
  simp at h₁
  case _ => subst h₁; simp only [Except.bind_ok]
  case _ => simp only [Except.map_error]

theorem to_option_eq_do₂ {α ε} {res₁ res₂ res₃ res₄: Except ε α} (f : α → α → Except ε α) :
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

theorem to_option_eq_mapM {α β ε} {ls : List α} (f g: α → Except ε β) :
(∀ x,
  x ∈ ls →
    Except.toOption (f x) = Except.toOption (g x)) →
  Except.toOption (List.mapM f ls) =
  Except.toOption (List.mapM g ls)
:= by
  induction ls
  case nil => simp only [List.not_mem_nil, false_implies, implies_true, List.mapM_nil, imp_self]
  case cons head tail hᵢ =>
    simp only [List.mem_cons, forall_eq_or_imp, List.mapM_cons, bind_pure_comp, and_imp]
    intro h
    simp only [Except.toOption] at h
    split at h <;> split at h <;> simp at h
    case _ heq₁ _ _ heq₂ =>
      subst h
      simp only [heq₁, Except.bind_ok, heq₂]
      intro h
      specialize hᵢ h
      simp only [Except.toOption] at hᵢ
      split at hᵢ <;> split at hᵢ <;> simp at hᵢ
      case _ heq₃ _ _ heq₄ =>
        subst hᵢ
        simp only [heq₃, Except.map_ok, heq₄]
      case _ heq₃ _ _ heq₄ =>
        simp only [Except.toOption, heq₃, Except.map_error, heq₄]
    case _ heq₁ _ _ heq₂ =>
      simp only [Except.toOption, heq₁, Except.bind_err, heq₂, implies_true]

theorem partial_evaluate_is_sound_lit
{p : Prim}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{ty : CedarType} :
  Except.toOption (Spec.evaluate (TypedExpr.lit p ty).toExpr req es) =
  Except.toOption ((TPE.evaluate (TypedExpr.lit p ty) preq pes).evaluate req es)
:= by
  simp [TypedExpr.toExpr, Spec.evaluate, TPE.evaluate, Residual.evaluate]

theorem partial_evaluate_is_sound_var
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{v : Var}
{ty : CedarType}
(h₄ : RequestAndEntitiesRefine req es preq pes) :
  Except.toOption (Spec.evaluate (TypedExpr.var v ty).toExpr req es) =
  Except.toOption ((TPE.evaluate (TypedExpr.var v ty) preq pes).evaluate req es)
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
      simp [RequestAndEntitiesRefine, RequestRefines] at h₄
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
      simp [RequestAndEntitiesRefine, RequestRefines] at h₄
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
    simp [RequestAndEntitiesRefine, RequestRefines] at h₄
    rcases h₄ with ⟨⟨_, ⟨h₄, _⟩⟩, _⟩
    rw [h₄]
  case _ =>
    split
    case _ heq =>
      simp at heq
      rcases heq with ⟨_, heq₁, heq₂⟩
      subst heq₂
      simp [Residual.evaluate]
      simp [RequestAndEntitiesRefine, RequestRefines] at h₄
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
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : Environment}
(h₂ : RequestAndEntitiesMatchEnvironment env req es)
(hᵢ₁ : TypedExpr.WellTyped env x₁)
(hᵢ₂ : TypedExpr.WellTyped env x₂)
(hᵢ₃ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₄ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₅ : Except.toOption (Spec.evaluate x₁.toExpr req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₆ : Except.toOption (Spec.evaluate x₂.toExpr req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es)) :
  Except.toOption (Spec.evaluate (x₁.and x₂ (CedarType.bool BoolType.anyBool)).toExpr req es) =
  Except.toOption ((TPE.evaluate (x₁.and x₂ (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
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
    generalize h₆ : Spec.evaluate x₁.toExpr req es = res₁
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
    generalize h₅ : Spec.evaluate x₁.toExpr req es = res₁
    cases res₁
    case ok =>
      have h₆ := well_typed_is_sound h₂ hᵢ₁ h₅
      rw [hᵢ₃] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      subst h₆
      replace h₅ := to_option_left_ok hᵢ₅ h₅
      simp [Result.as, Coe.coe, Residual.evaluate, h₅, Value.asBool]
      generalize h₇ : Spec.evaluate x₂.toExpr req es = res₂
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
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : Environment}
(h₂ : RequestAndEntitiesMatchEnvironment env req es)
(hwt : TypedExpr.WellTyped env x₁)
(hₜ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₁ : Except.toOption (Spec.evaluate x₁.toExpr req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₂ : Except.toOption (Spec.evaluate x₂.toExpr req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es))
(hᵢ₃ : Except.toOption (Spec.evaluate x₃.toExpr req es) = Except.toOption ((TPE.evaluate x₃ preq pes).evaluate req es)) :
  Except.toOption (Spec.evaluate (x₁.ite x₂ x₃ x₂.typeOf).toExpr req es) =
  Except.toOption ((TPE.evaluate (x₁.ite x₂ x₃ x₂.typeOf) preq pes).evaluate req es) := by
  simp [TypedExpr.toExpr, TPE.evaluate, TPE.ite]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    have h₆ := to_option_right_ok' hᵢ₁
    split
    case isTrue heq =>
      simp [Spec.evaluate, h₆, Result.as, Coe.coe, Value.asBool, heq]
      exact hᵢ₂
    case isFalse heq =>
      simp [Spec.evaluate, h₆, Result.as, Coe.coe, Value.asBool, heq]
      exact hᵢ₃
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, h₆⟩
    simp [Spec.evaluate, h₆, Result.as, Residual.evaluate, Except.toOption]
  case _ =>
    simp [Spec.evaluate]
    generalize h₅ : Spec.evaluate x₁.toExpr req es = res₁
    cases res₁
    case ok =>
      simp [Result.as, Coe.coe]
      have h₆ := well_typed_is_sound h₂ hwt h₅
      simp [hₜ] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      subst h₆
      simp [Value.asBool]
      replace hᵢ₆ := to_option_left_ok hᵢ₁ h₅
      simp [Residual.evaluate, hᵢ₆, Value.asBool]
      split
      case _ => exact hᵢ₂
      case _ => exact hᵢ₃
    case error =>
      simp [Result.as, Except.toOption]
      simp [h₅] at hᵢ₁
      rcases to_option_left_err hᵢ₁ with ⟨_, hᵢ₁⟩
      simp only [Residual.evaluate, hᵢ₁, Except.bind_err]

theorem partial_evaluate_is_sound_or
{x₁ x₂ : TypedExpr}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : Environment}
(h₂ : RequestAndEntitiesMatchEnvironment env req es)
(hᵢ₁ : TypedExpr.WellTyped env x₁)
(hᵢ₂ : TypedExpr.WellTyped env x₂)
(hᵢ₃ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₄ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₅ : Except.toOption (Spec.evaluate x₁.toExpr req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₆ : Except.toOption (Spec.evaluate x₂.toExpr req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es)) :
  Except.toOption (Spec.evaluate (x₁.or x₂ (CedarType.bool BoolType.anyBool)).toExpr req es) =
  Except.toOption ((TPE.evaluate (x₁.or x₂ (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
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
    generalize h₆ : Spec.evaluate x₂.toExpr req es = res₂
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
    generalize h₅ : Spec.evaluate x₁.toExpr req es = res₁
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
    generalize h₅ : Spec.evaluate x₁.toExpr req es = res₁
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
        generalize h₇ : Spec.evaluate x₂.toExpr req es = res₂
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
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{op₁ : UnaryOp}
{ty : CedarType}
(hᵢ₁ : Except.toOption (Spec.evaluate x₁.toExpr req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es)) :
  Except.toOption (Spec.evaluate (TypedExpr.unaryApp op₁ x₁ ty).toExpr req es) =
  Except.toOption ((TPE.evaluate (TypedExpr.unaryApp op₁ x₁ ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.apply₁]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₁, Residual.evaluate, Except.toOption]
  case _ =>
    split <;>
    (rename_i heq; simp [Residual.asValue] at heq; split at heq) <;>
    simp at heq
    case _ heq₁ =>
      subst heq
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [someOrError, TypedExpr.toExpr, Spec.evaluate, hᵢ₁]
      split
      case _ heq₂ =>
        simp [to_option_some] at heq₂
        simp [heq₂, Residual.evaluate]
      case _ heq₂ =>
        rcases to_option_none heq₂ with ⟨_, heq₂⟩
        simp [heq₂, Residual.evaluate, Except.toOption]
    case _ =>
      simp [Residual.evaluate, TypedExpr.toExpr, Spec.evaluate]
      generalize h₅ : Spec.evaluate x₁.toExpr req es = res₁
      cases res₁ <;> simp [h₅] at hᵢ₁
      case error =>
        rcases to_option_left_err hᵢ₁ with ⟨_, hᵢ₁⟩
        simp [hᵢ₁, Except.toOption]
      case ok =>
        replace hᵢ₃ := to_option_left_ok' hᵢ₁
        simp [hᵢ₃]

theorem partial_evaluate_is_sound_binary_app
{op₂ : BinaryOp}
{ty : CedarType}
{x₁ x₂ : TypedExpr}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : Environment}
(h₂ : RequestAndEntitiesMatchEnvironment env req es)
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hwt : TypedExpr.WellTyped env x₂)
(howt : BinaryOp.WellTyped env op₂ x₁ x₂ ty)
(hᵢ₁ : Except.toOption (Spec.evaluate x₁.toExpr req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₂ : Except.toOption (Spec.evaluate x₂.toExpr req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es)) :
  Except.toOption (Spec.evaluate (TypedExpr.binaryApp op₂ x₁ x₂ ty).toExpr req es) =
  Except.toOption ((TPE.evaluate (TypedExpr.binaryApp op₂ x₁ x₂ ty) preq pes).evaluate req es)
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
    simp [heq₁, Residual.evaluate] at hᵢ₁
    simp [heq₂, Residual.evaluate] at hᵢ₂
    replace hᵢ₁ := to_option_right_ok' hᵢ₁
    replace hᵢ₅ := to_option_right_ok' hᵢ₂
    simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₁, hᵢ₅, Spec.apply₂]
    -- TODO: rewrite one of the two binary app evaluation function so that we don't need this amount of case splits.
    split <;> simp [Residual.evaluate]
    any_goals
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
          simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄
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
      case _ uid vs _ _ _ _ _ heq₃ =>
        simp only [Option.bind_eq_some] at heq₃
        rcases heq₃ with ⟨_, heq₃₁, heq₃₂⟩
        simp only [Option.some.injEq] at heq₃₂
        subst heq₃₂
        simp [Spec.inₛ]
        cases howt <;>
        (rename_i h₅; have h₆ := well_typed_is_sound h₂ hwt hᵢ₅; rw [h₅] at h₆; cases h₆)
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
          simp [RequestAndEntitiesRefine] at h₄
          rcases h₄ with ⟨_, h₄⟩
          have : ∀ x b, ((if uid = x then some true else Option.map (fun y => y.contains x) (pes.ancestors uid)) = some b) →
            (uid == x || (es.ancestorsOrEmpty uid).contains x) = b := by
            intro x b' h₁
            split at h₁
            case isTrue heq =>
              simp only [Option.some.injEq, Bool.true_eq] at h₁
              subst h₁
              simp only [heq, beq_self_eq_true, Bool.true_or]
            case isFalse heq =>
              simp [EntitiesRefine] at h₄
              simp at h₁
              rcases h₁ with ⟨ancestors₁, h₂, h₃⟩
              simp [PartialEntities.ancestors, PartialEntities.get, Option.bind] at h₂
              split at h₂ <;> try cases h₂
              rename_i data heq₁
              specialize h₄ uid data heq₁
              rcases h₄ with ⟨e, h₄, _, h₅, _⟩
              rw [h₂] at h₅
              cases h₅
              rename_i heq₂
              rw [heq₂] at h₃
              simp only [Entities.ancestorsOrEmpty, h₄, h₃, Bool.or_iff_right_iff_imp, beq_iff_eq, heq,
                false_implies]
          replace heq₃₂ := anyM_some_implies_any (fun x => if uid = x then some true else Option.map (fun y => y.contains x) (pes.ancestors uid))
            (fun x => uid == x || (es.ancestorsOrEmpty uid).contains x) this heq₃₂
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
        simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄
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
        simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄
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
      simp [heq, Residual.evaluate] at hᵢ₁
      rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
      simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₁, Residual.evaluate, Except.toOption]
    case _ heq _ =>
      simp [heq, Residual.evaluate] at hᵢ₂
      rcases to_option_right_err hᵢ₂ with ⟨_, hᵢ₂⟩
      simp only [TypedExpr.toExpr, Spec.evaluate, hᵢ₂, Except.bind_err, do_error_to_option,
        Residual.evaluate]
      simp only [Except.toOption]
    case _ =>
      simp [TypedExpr.toExpr, Spec.evaluate, apply₂.self, Residual.evaluate]
      exact to_option_eq_do₂
        (λ x y => Spec.apply₂ op₂ x y es) hᵢ₁ hᵢ₂

theorem partial_evaluate_is_sound_has_attr
{x₁ : TypedExpr}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{attr : Attr}
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hᵢ₁ : Except.toOption (Spec.evaluate x₁.toExpr req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es)) :
  Except.toOption (Spec.evaluate (x₁.hasAttr attr (CedarType.bool BoolType.anyBool)).toExpr req es) =
  Except.toOption ((TPE.evaluate (x₁.hasAttr attr (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.hasAttr]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₁, Residual.evaluate, Except.toOption]
  split
  case _ heq =>
    simp [TPE.attrsOf] at heq
    split at heq
    case _ heq₁ =>
      simp only [Option.some.injEq] at heq
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₁, Spec.hasAttr, Spec.attrsOf, Residual.evaluate, Except.toOption, heq]
    case _ uid _ heq₁ =>
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₁, Spec.hasAttr, Spec.attrsOf, Residual.evaluate, Except.toOption]
      simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some] at heq
      rcases heq with ⟨data, heq₂, heq₃⟩
      simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄
      rcases h₄ with ⟨_, h₄⟩
      specialize h₄ uid data heq₂
      rcases h₄ with ⟨_, h₄₁, h₄₂, _⟩
      rw [heq₃] at h₄₂
      rcases h₄₂
      rename_i h₄
      subst h₄
      simp [Entities.attrsOrEmpty, h₄₁]
    case _ => cases heq
  case _ =>
    simp [Residual.evaluate, TypedExpr.toExpr, Spec.evaluate]
    exact to_option_eq_do₁ (λ x => Spec.hasAttr x attr es) hᵢ₁

theorem partial_evaluate_is_sound_get_attr
{x₁ : TypedExpr}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{attr : Attr}
{ty : CedarType}
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hᵢ₁ : Except.toOption (Spec.evaluate x₁.toExpr req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es)) :
  Except.toOption (Spec.evaluate (x₁.getAttr attr ty).toExpr req es) =
  Except.toOption ((TPE.evaluate (x₁.getAttr attr ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.getAttr]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [TypedExpr.toExpr, hᵢ₁, Spec.evaluate, Residual.evaluate, Except.toOption]
  split
  case _ heq =>
    simp [TPE.attrsOf] at heq
    split at heq
    case _ heq₁ =>
      simp at heq
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₁, someOrError, Spec.getAttr, Spec.attrsOf]
      subst heq
      split <;>
      (
        rename_i heq₂
        simp [Data.Map.findOrErr, heq₂, Residual.evaluate, Except.toOption]
      )
    case _ uid _ heq₁ =>
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [TypedExpr.toExpr, Spec.evaluate, hᵢ₁, Spec.getAttr, Spec.attrsOf]
      simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some] at heq
      rcases heq with ⟨data, heq₂, heq₃⟩
      simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄
      rcases h₄ with ⟨_, h₄⟩
      specialize h₄ uid data heq₂
      rcases h₄ with ⟨_, h₄₁, h₄₂, _⟩
      rw [heq₃] at h₄₂
      rcases h₄₂
      rename_i data' _ h₄
      subst h₄
      simp [Entities.attrs, Data.Map.findOrErr, h₄₁]
      generalize h₄ : data'.attrs.find? attr = res
      cases res <;> simp [someOrError, Residual.evaluate, Except.toOption]
    case _ => cases heq
  case _ =>
    simp [TypedExpr.toExpr, Spec.evaluate, Residual.evaluate]
    exact to_option_eq_do₁ (Spec.getAttr · attr es) hᵢ₁

theorem partial_evaluate_is_sound_set
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{ls : List TypedExpr}
{ty : CedarType}
(hᵢ₁ : ∀ (x : TypedExpr),
  x ∈ ls →
    Except.toOption (Spec.evaluate x.toExpr req es) = Except.toOption ((TPE.evaluate x preq pes).evaluate req es)) :
  Except.toOption (Spec.evaluate (TypedExpr.set ls ty.set).toExpr req es) =
  Except.toOption ((TPE.evaluate (TypedExpr.set ls ty.set) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, List.map₁, TPE.set]
  split
  case _ vs heq =>
    simp [Residual.evaluate]
    have : (Except.ok (Value.set (Data.Set.make vs)) : Except Spec.Error Value).toOption = .some (Value.set (Data.Set.make vs)) := by
      simp only [Except.toOption]
    rw [this]
    clear this
    simp only [TypedExpr.toExpr, List.map₁_eq_map, Spec.evaluate,
      List.mapM₁_eq_mapM (fun x => Spec.evaluate x req es), List.mapM_map, to_option_some, do_ok_eq_ok,
      Value.set.injEq]
    exists vs
    simp only [and_true]
    simp [List.mapM_map, List.mapM_some_iff_forall₂] at heq
    have : ∀ x y, (TPE.evaluate x preq pes).asValue = some y → (TPE.evaluate x preq pes).evaluate req es = .ok y := by
      intro x y h
      rcases as_value_some h with ⟨_, h⟩
      simp [h, Residual.evaluate]
    replace heq := List.Forall₂.imp this heq
    clear this
    rw [←List.mapM_ok_iff_forall₂] at heq
    have : ∀ (x : TypedExpr),
      x ∈ ls →
      Except.toOption ((TPE.evaluate x preq pes).evaluate req es) =
      Except.toOption (Spec.evaluate x.toExpr req es) := by
      intro x h
      specialize hᵢ₁ x h
      symm
      exact hᵢ₁
    have h₅ := to_option_eq_mapM
      (λ x => (TPE.evaluate x preq pes).evaluate req es)
      (λ x => Spec.evaluate x.toExpr req es)
      this
    simp [heq] at h₅
    exact to_option_left_ok' h₅
  case _ heq =>
    split
    case isTrue heq₁ =>
      rcases heq₁ with ⟨x, heq₂, heq₃⟩
      specialize hᵢ₁ x heq₂
      simp [Residual.isError] at heq₃
      split at heq₃ <;> cases heq₃
      rename_i heq₃
      simp [heq₃, Residual.evaluate] at hᵢ₁
      rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
      simp [TypedExpr.toExpr, List.map₁, Spec.evaluate, List.mapM₁_eq_mapM (fun x => Spec.evaluate x req es), List.mapM_map]
      have heq₄ := @List.element_error_implies_mapM_error _ _ _ _ _ (λ x => Spec.evaluate x.toExpr req es) _ heq₂ hᵢ₁
      rcases heq₄ with ⟨_, heq₄⟩
      simp [heq₄, Residual.evaluate, Except.toOption]
    case isFalse =>
      simp only [TypedExpr.toExpr, List.map₁, List.map_subtype, List.unattach_attach, Spec.evaluate,
        List.mapM₁_eq_mapM (fun x => Spec.evaluate x req es), List.mapM_map, Residual.evaluate,
        List.mapM₁_eq_mapM (fun x => Residual.evaluate x req es)]
      apply to_option_eq_do₁ (λ (x : List Value) => (Except.ok (Value.set (Data.Set.make x))))
      exact to_option_eq_mapM
        (fun x => Spec.evaluate x.toExpr req es)
        (fun x => (TPE.evaluate x preq pes).evaluate req es)
        hᵢ₁

theorem partial_evaluate_is_sound_record
{m : List (Attr × TypedExpr)}
{rty : RecordType}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
(hᵢ₁ : ∀ (k : Attr) (v : TypedExpr),
  (k, v) ∈ m →
    Except.toOption (Spec.evaluate v.toExpr req es) = Except.toOption ((TPE.evaluate v preq pes).evaluate req es)) :
  Except.toOption (Spec.evaluate (TypedExpr.record m (CedarType.record rty)).toExpr req es) =
  Except.toOption ((TPE.evaluate (TypedExpr.record m (CedarType.record rty)) preq pes).evaluate req es)
:= by
  simp only [TPE.evaluate, record,
    List.map₁_eq_map (fun (x : Attr × TypedExpr) => (x.fst, TPE.evaluate x.snd preq pes)),
    List.any_map, List.any_eq_true, Function.comp_apply, Prod.exists]
  split
  case _ vs heq =>
    simp [TypedExpr.toExpr, Spec.evaluate, List.map_attach₂ (fun x : Attr × TypedExpr => (x.fst, x.snd.toExpr))]
    simp [List.mapM₂, List.attach₂, List.mapM_pmap_subtype
      (fun (x : Attr × Expr) => bindAttr x.fst (Spec.evaluate x.snd req es)), List.mapM_map, Residual.evaluate]
    have : (Except.ok (Value.record (Data.Map.make vs)) : Except Spec.Error Value).toOption = .some (Value.record (Data.Map.make vs)) := by
      simp only [Except.toOption]
    rw [this]
    clear this
    simp [to_option_some, do_ok_eq_ok]
    exists vs
    simp only [and_true]
    simp [List.mapM_map, List.mapM_some_iff_forall₂] at heq
    have : ∀ (x : Attr × TypedExpr) y, bindAttr x.fst (TPE.evaluate x.snd preq pes).asValue = some y → bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es) = .ok y := by
      intro x y h
      simp only [bindAttr] at *
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at h
      rcases h with ⟨_, h₁, h₂⟩
      rcases as_value_some h₁ with ⟨_, h₁⟩
      simp only [h₁, Residual.evaluate, bind_pure_comp, Except.map_ok, h₂]
    replace heq := List.Forall₂.imp this heq
    clear this
    rw [←List.mapM_ok_iff_forall₂] at heq
    have : ∀ x,
      x ∈ m →
      Except.toOption (bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es)) =
      Except.toOption (bindAttr x.fst (Spec.evaluate x.snd.toExpr req es)) := by
      intro x h
      have hrfl : x = (x.fst, x.snd) := by rfl
      rw [hrfl] at h
      specialize hᵢ₁ x.fst x.snd h
      simp [bindAttr]
      symm
      exact to_option_eq_map (Prod.mk x.fst ·) hᵢ₁
    have h₁ := to_option_eq_mapM
      (λ (x : Attr × TypedExpr) => bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es))
      (λ x => bindAttr x.fst (Spec.evaluate x.snd.toExpr req es))
      this
    simp [heq] at h₁
    replace h₁ := to_option_left_ok' h₁
    exact h₁
  split
  case _ h₁ =>
    simp only [List.map₁, List.any_map, List.any_eq_true, List.mem_attach, Function.comp_apply,
      true_and, Subtype.exists, exists_prop, Prod.exists] at h₁
    rcases h₁ with ⟨k, v, h₂, h₃⟩
    simp [Residual.isError] at h₃
    split at h₃ <;> simp at h₃
    rename_i heq
    specialize hᵢ₁ k v h₂
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨err, hᵢ₁⟩
    simp [TypedExpr.toExpr, Spec.evaluate, List.map_attach₂ (fun x : Attr × TypedExpr => (x.fst, x.snd.toExpr))]
    simp [List.mapM₂, List.attach₂, List.mapM_pmap_subtype
      (fun (x : Attr × Expr) => bindAttr x.fst (Spec.evaluate x.snd req es)), List.mapM_map]
    have : (fun (x: Attr × TypedExpr) => bindAttr x.fst (Spec.evaluate x.snd.toExpr req es)) (k, v) = .error err := by
      simp only [bindAttr, hᵢ₁, bind_pure_comp, Except.map_error]
    have h₄ := @List.element_error_implies_mapM_error _ _ _ _ _ (fun (x: Attr × TypedExpr) => bindAttr x.fst (Spec.evaluate x.snd.toExpr req es)) _ h₂ this
    rcases h₄ with ⟨_, h₄⟩
    simp [h₄, Residual.evaluate, Except.toOption]
  case _ =>
    simp [TypedExpr.toExpr, Spec.evaluate, List.map_attach₂ (fun x : Attr × TypedExpr => (x.fst, x.snd.toExpr))]
    simp [List.mapM₂, List.attach₂, List.mapM_pmap_subtype
      (fun (x : Attr × Expr) => bindAttr x.fst (Spec.evaluate x.snd req es)), List.mapM_map]
    simp [Residual.evaluate, List.mapM₂, List.attach₂, List.mapM_pmap_subtype
      (fun (x : Attr × Residual) => bindAttr x.fst (Residual.evaluate x.snd req es)), List.mapM_map]
    apply to_option_eq_do₁
    have : ∀ x,
      x ∈ m →
      Except.toOption (bindAttr x.fst (Spec.evaluate x.snd.toExpr req es)) =
      Except.toOption (bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es)) := by
      intro x h
      have hrfl : x = (x.fst, x.snd) := by rfl
      rw [hrfl] at h
      specialize hᵢ₁ x.fst x.snd h
      simp [bindAttr]
      exact to_option_eq_map (Prod.mk x.fst ·) hᵢ₁
    exact to_option_eq_mapM
      (fun (x : Attr × TypedExpr) => bindAttr x.fst (Spec.evaluate x.snd.toExpr req es))
      (fun x => bindAttr x.fst ((TPE.evaluate x.snd preq pes).evaluate req es))
      this

theorem partial_evaluate_is_sound_call
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{xfn : ExtFun}
{args : List TypedExpr}
{ty : CedarType}
(hᵢ₁ : ∀ (x : TypedExpr),
  x ∈ args →
    Except.toOption (Spec.evaluate x.toExpr req es) = Except.toOption ((TPE.evaluate x preq pes).evaluate req es)) :
  Except.toOption (Spec.evaluate (TypedExpr.call xfn args ty).toExpr req es) =
  Except.toOption ((TPE.evaluate (TypedExpr.call xfn args ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.call, List.map₁, List.mapM_map]
  split
  case _ vs heq =>
    simp only [TypedExpr.toExpr, List.map₁, List.map_subtype, List.unattach_attach, Spec.evaluate,
      List.mapM₁_eq_mapM (fun x => Spec.evaluate x req es), List.mapM_map, someOrError]
    simp [List.mapM_map, List.mapM_some_iff_forall₂] at heq
    have : ∀ x y, (TPE.evaluate x preq pes).asValue = some y → (TPE.evaluate x preq pes).evaluate req es = .ok y := by
      intro x y h
      rcases as_value_some h with ⟨_, h⟩
      simp [h, Residual.evaluate]
    replace heq := List.Forall₂.imp this heq
    clear this
    rw [←List.mapM_ok_iff_forall₂] at heq
    have : ∀ (x : TypedExpr),
      x ∈ args →
      Except.toOption ((TPE.evaluate x preq pes).evaluate req es) =
      Except.toOption (Spec.evaluate x.toExpr req es) := by
      intro x h
      specialize hᵢ₁ x h
      symm
      exact hᵢ₁
    have h₅ := to_option_eq_mapM
      (λ x => (TPE.evaluate x preq pes).evaluate req es)
      (λ x => Spec.evaluate x.toExpr req es)
      this
    simp [heq] at h₅
    replace h₅ := to_option_left_ok' h₅
    simp [h₅]
    split
    case _ heq₁ =>
      simp only [to_option_some] at heq₁
      simp only [heq₁, Residual.evaluate]
    case _ heq₁ =>
      rcases to_option_none heq₁ with ⟨_, heq₁⟩
      simp [heq₁, Residual.evaluate, Except.toOption]
  split
  case _ heq₁ =>
    rcases heq₁ with ⟨x, heq₂, heq₃⟩
    specialize hᵢ₁ x heq₂
    simp [Residual.isError] at heq₃
    split at heq₃ <;> cases heq₃
    rename_i heq₃
    simp [heq₃, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    have heq₄ := @List.element_error_implies_mapM_error _ _ _ _ _ (λ x => Spec.evaluate x.toExpr req es) _ heq₂ hᵢ₁
    rcases heq₄ with ⟨_, heq₄⟩
    simp only [Except.toOption, TypedExpr.toExpr, List.map₁, List.map_subtype, List.unattach_attach,
      Spec.evaluate, List.mapM₁_eq_mapM (fun x => Spec.evaluate x req es), List.mapM_map, heq₄,
      Except.bind_err, Residual.evaluate]
  case _ =>
    simp only [TypedExpr.toExpr, List.map₁, List.map_subtype, List.unattach_attach, Spec.evaluate,
      List.mapM₁_eq_mapM (fun x => Spec.evaluate x req es), List.mapM_map, Residual.evaluate,
      List.mapM₁_eq_mapM (fun (x : Residual) => x.evaluate req es)]
    apply to_option_eq_do₁ (λ (x : List Value) => Spec.call xfn x)
    exact to_option_eq_mapM
      (fun x => Spec.evaluate x.toExpr req es)
      (fun x => (TPE.evaluate x preq pes).evaluate req es)
      hᵢ₁

end Cedar.Thm
