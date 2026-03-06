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

/-!
This file contains basic utility theorems used in the TPE soundness proof.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

@[simp]
theorem as_value_some {r : Residual} {v : Value} :
  r.asValue = .some v ↔ (∃ ty, r = .val v ty)
:= by
  simp only [Residual.asValue]
  split
  · simp
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact not_exists.mpr (h v)

theorem as_value_evaluates_to {r : Residual} {v : Value} :
  r.asValue = .some v → r.evaluate req es = Except.ok v
:= by
  simp only [as_value_some, forall_exists_index]
  intro _ hv
  simp [hv, Residual.evaluate]

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
  case _ => subst h₁; simp only
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
  case nil => simp only [List.not_mem_nil, false_implies, implies_true, List.mapM_nil]
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

end Cedar.Thm
