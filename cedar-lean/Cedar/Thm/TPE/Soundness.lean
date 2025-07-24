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
import Cedar.Thm.Data.Control

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
        simp only [hᵢ, Bool.or_eq_right_iff_imp]
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

theorem partial_evaluate_is_sound_val
{v : Value}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{ty : CedarType} :
  Except.toOption ((Residual.val v ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.val v ty) preq pes).evaluate req es)
:= by
  simp [Spec.evaluate, TPE.evaluate, Residual.evaluate]


theorem partial_evaluate_is_sound_var
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{v : Var}
{ty : CedarType}
(h₄ : RequestAndEntitiesRefine req es preq pes) :
  Except.toOption ((Residual.var v ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.var v ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, varₚ]
  split <;>
  simp [Spec.evaluate, varₚ.varₒ, someOrSelf]
  case _ =>
    split
    case _ heq =>
      simp [Option.bind_eq_some_iff] at heq
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
      simp [Option.bind_eq_some_iff] at heq
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
{x₁ x₂ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(hᵢ₁ : Residual.WellTyped env x₁)
(hᵢ₂ : Residual.WellTyped env x₂)
(hᵢ₃ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₄ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₅ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₆ : Except.toOption (x₂.evaluate req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es)) :
  Except.toOption ((x₁.and x₂ (CedarType.bool BoolType.anyBool)).evaluate req es) =
  Except.toOption ((TPE.evaluate (x₁.and x₂ (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.and]
  split
  case _ ty heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [Residual.evaluate, h₅, Result.as, Coe.coe, Value.asBool]
    split
    case _ heq₁ =>
      have h₆ := residual_well_typed_is_sound h₂ hᵢ₂ heq₁
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
    simp [Residual.evaluate, h₅, Result.as, Coe.coe, Value.asBool, Residual.evaluate]
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    rcases to_option_right_err hᵢ₅ with ⟨_, hᵢ₅⟩
    simp [Residual.evaluate, hᵢ₅, Result.as, Residual.evaluate, Except.toOption]
  case _ heq _ _ _ =>
    simp [heq, Residual.evaluate] at hᵢ₆
    have h₅ := to_option_right_ok' hᵢ₆
    simp [Residual.evaluate]
    generalize h₆ : x₁.evaluate req es = res₁
    cases res₁
    case ok =>
      have h₇ := residual_well_typed_is_sound h₂ hᵢ₁ h₆
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
    simp [Residual.evaluate]
    generalize h₅ : x₁.evaluate req es = res₁
    cases res₁
    case ok =>
      have h₆ := residual_well_typed_is_sound h₂ hᵢ₁ h₅
      rw [hᵢ₃] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      subst h₆
      replace h₅ := to_option_left_ok hᵢ₅ h₅
      simp [Result.as, Coe.coe, Residual.evaluate, h₅, Value.asBool]
      generalize h₇ : x₂.evaluate req es = res₂
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
{x₁ x₂ x₃ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(hwt : Residual.WellTyped env x₁)
(hₜ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₂ : Except.toOption (x₂.evaluate req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es))
(hᵢ₃ : Except.toOption (x₃.evaluate req es) = Except.toOption ((TPE.evaluate x₃ preq pes).evaluate req es)) :
  Except.toOption ((x₁.ite x₂ x₃ x₂.typeOf).evaluate req es) =
  Except.toOption ((TPE.evaluate (x₁.ite x₂ x₃ x₂.typeOf) preq pes).evaluate req es) := by
  simp [Residual.evaluate, TPE.evaluate, TPE.ite]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    have h₆ := to_option_right_ok' hᵢ₁
    split
    case isTrue heq =>
      simp [Residual.evaluate, h₆, Result.as, Coe.coe, Value.asBool, heq]
      exact hᵢ₂
    case isFalse heq =>
      simp [Residual.evaluate, h₆, Result.as, Coe.coe, Value.asBool, heq]
      exact hᵢ₃
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, h₆⟩
    simp [Residual.evaluate, h₆, Result.as, Residual.evaluate, Except.toOption]
  case _ =>
    simp [Residual.evaluate]
    generalize h₅ : x₁.evaluate req es = res₁
    cases res₁
    case ok =>
      simp [Result.as, Coe.coe]
      have h₆ := residual_well_typed_is_sound h₂ hwt h₅
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
{x₁ x₂ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(hᵢ₁ : Residual.WellTyped env x₁)
(hᵢ₂ : Residual.WellTyped env x₂)
(hᵢ₃ : x₁.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₄ : x₂.typeOf = CedarType.bool BoolType.anyBool)
(hᵢ₅ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₆ : Except.toOption (x₂.evaluate req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es)) :
  Except.toOption ((x₁.or x₂ (CedarType.bool BoolType.anyBool)).evaluate req es) =
  Except.toOption ((TPE.evaluate (x₁.or x₂ (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.or]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [Residual.evaluate, h₅, Result.as, Coe.coe, Value.asBool, Residual.evaluate]
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    have h₅ := to_option_right_ok' hᵢ₅
    simp [Residual.evaluate, h₅, Result.as, Coe.coe, Value.asBool]
    generalize h₆ : x₂.evaluate req es = res₂
    cases res₂
    case error =>
      simp [←h₆]
      exact hᵢ₆
    case ok =>
      have h₇ := residual_well_typed_is_sound h₂ hᵢ₂ h₆
      rw [hᵢ₄] at h₇
      rcases instance_of_anyBool_is_bool h₇ with ⟨_, h₇⟩
      subst h₇
      simp [←h₆]
      exact hᵢ₆
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₅
    rcases to_option_right_err hᵢ₅ with ⟨_, hᵢ₅⟩
    simp [Residual.evaluate, hᵢ₅, Result.as, Residual.evaluate, Except.toOption]
  case _ heq _ _ _ =>
    simp [heq, Residual.evaluate] at hᵢ₆
    have hᵢ₇ := to_option_right_ok' hᵢ₆
    generalize h₅ : x₁.evaluate req es = res₁
    cases res₁
    case error =>
      simp [Residual.evaluate, h₅, Result.as]
      rw [←h₅]
      exact hᵢ₅
    case ok =>
      have h₆ := residual_well_typed_is_sound h₂ hᵢ₁ h₅
      rw [hᵢ₃] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      simp [Residual.evaluate, h₅, h₆, Result.as, Coe.coe, Value.asBool, hᵢ₇]
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
    simp [Residual.evaluate]
    generalize h₅ : x₁.evaluate req es = res₁
    cases res₁
    case ok =>
      simp [Result.as, Coe.coe]
      have h₆ := residual_well_typed_is_sound h₂ hᵢ₁ h₅
      simp [hᵢ₃] at h₆
      rcases instance_of_anyBool_is_bool h₆ with ⟨_, h₆⟩
      subst h₆
      simp [Value.asBool]
      have hᵢ₇ := to_option_left_ok hᵢ₅ h₅
      simp [Residual.evaluate, hᵢ₇, Result.as, Coe.coe, Value.asBool]
      split
      case _ => rfl
      case _ =>
        generalize h₇ : x₂.evaluate req es = res₂
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
{x₁ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{op₁ : UnaryOp}
{ty : CedarType}
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es)) :
  Except.toOption ((Residual.unaryApp op₁ x₁ ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.unaryApp op₁ x₁ ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.apply₁]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  case _ =>
    split <;>
    (rename_i heq; simp [Residual.asValue] at heq; split at heq) <;>
    simp at heq
    case _ heq₁ =>
      subst heq
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [someOrError, Residual.evaluate, hᵢ₁]
      split
      case _ heq₂ =>
        simp [to_option_some] at heq₂
        simp [heq₂, Residual.evaluate]
      case _ heq₂ =>
        rcases to_option_none heq₂ with ⟨_, heq₂⟩
        simp [heq₂, Residual.evaluate, Except.toOption]
    case _ =>
      simp [Residual.evaluate]
      generalize h₅ : x₁.evaluate req es = res₁
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
{x₁ x₂ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hwt : Residual.WellTyped env x₂)
(howt : BinaryResidualWellTyped env op₂ x₁ x₂ ty)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₂ : Except.toOption (x₂.evaluate req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es)) :
  Except.toOption ((Residual.binaryApp op₂ x₁ x₂ ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.binaryApp op₂ x₁ x₂ ty) preq pes).evaluate req es)
:= by
  sorry

theorem partial_evaluate_is_sound_has_attr
{x₁ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{attr : Attr}
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es)) :
  Except.toOption ((x₁.hasAttr attr (CedarType.bool BoolType.anyBool)).evaluate req es) =
  Except.toOption ((TPE.evaluate (x₁.hasAttr attr (CedarType.bool BoolType.anyBool)) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.hasAttr]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  split
  case _ heq =>
    simp [TPE.attrsOf] at heq
    split at heq
    case _ heq₁ =>
      simp only [Option.some.injEq] at heq
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [Residual.evaluate, hᵢ₁, Spec.hasAttr, Spec.attrsOf, Except.toOption, heq]
    case _ uid _ heq₁ =>
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [Residual.evaluate, hᵢ₁, Spec.hasAttr, Spec.attrsOf, Except.toOption]
      simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some_iff] at heq
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
    simp [Residual.evaluate]
    exact to_option_eq_do₁ (λ x => Spec.hasAttr x attr es) hᵢ₁

theorem partial_evaluate_is_sound_get_attr
{x₁ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{attr : Attr}
{ty : CedarType}
(h₄ : RequestAndEntitiesRefine req es preq pes)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es)) :
  Except.toOption ((x₁.getAttr attr ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (x₁.getAttr attr ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.getAttr]
  split
  case _ heq =>
    simp [heq, Residual.evaluate] at hᵢ₁
    rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
    simp [Residual.evaluate, hᵢ₁, Except.toOption]
  split
  case _ heq =>
    simp [TPE.attrsOf] at heq
    split at heq
    case _ heq₁ =>
      simp at heq
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [Residual.evaluate, hᵢ₁, someOrError, Spec.getAttr, Spec.attrsOf]
      subst heq
      split <;>
      (
        rename_i heq₂
        simp [Data.Map.findOrErr, heq₂, Residual.evaluate, Except.toOption]
      )
    case _ uid _ heq₁ =>
      simp [heq₁, Residual.evaluate] at hᵢ₁
      replace hᵢ₁ := to_option_right_ok' hᵢ₁
      simp [Residual.evaluate, hᵢ₁, Spec.getAttr, Spec.attrsOf]
      simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some_iff] at heq
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
    simp [Residual.evaluate]
    exact to_option_eq_do₁ (Spec.getAttr · attr es) hᵢ₁

theorem partial_evaluate_is_sound_set
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{ls : List Residual}
{ty : CedarType}
(hᵢ₁ : ∀ (x : Residual),
  x ∈ ls →
    Except.toOption (x.evaluate req es) = Except.toOption ((TPE.evaluate x preq pes).evaluate req es)) :
  Except.toOption ((Residual.set ls ty.set).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.set ls ty.set) preq pes).evaluate req es)
:= by
  sorry

theorem partial_evaluate_is_sound_record
{m : List (Attr × Residual)}
{rty : RecordType}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
(hᵢ₁ : ∀ (k : Attr) (v : Residual),
  (k, v) ∈ m →
    Except.toOption (v.evaluate req es) = Except.toOption ((TPE.evaluate v preq pes).evaluate req es)) :
  Except.toOption ((Residual.record m (CedarType.record rty)).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.record m (CedarType.record rty)) preq pes).evaluate req es)
:= by
  sorry

theorem partial_evaluate_is_sound_call
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{xfn : ExtFun}
{args : List Residual}
{ty : CedarType}
(hᵢ₁ : ∀ (x : Residual),
  x ∈ args →
    Except.toOption (x.evaluate req es) = Except.toOption ((TPE.evaluate x preq pes).evaluate req es)) :
  Except.toOption ((Residual.call xfn args ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.call xfn args ty) preq pes).evaluate req es)
:= by
  sorry

end Cedar.Thm
