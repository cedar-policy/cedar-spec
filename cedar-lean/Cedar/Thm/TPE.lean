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
import Cedar.Thm.Validation.TypedExpr
import Cedar.Thm.Data

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm.TPE
open Cedar.Thm

theorem partialEvaluate_is_sound
  (x : TypedExpr)
  (req₁ : Request)
  (es₁ : Entities)
  (req₂ : PartialRequest)
  (es₂ : PartialEntities)
  (env : Environment) :
  TypedExpr.WellTyped env x →
  RequestAndEntitiesMatchEnvironment env req₁ es₁ →
  PartialRequestAndEntitiesMatchEnvironment env req₂ es₂ →
  IsConsistent env req₁ es₁ req₂ es₂ →
  (Spec.evaluate x.toExpr req₁ es₁).toOption = (Residual.evaluate (Cedar.TPE.evaluate x req₂ es₂) req₁ es₁).toOption
:= by
  intro h₀ h₁ h₂ h₃
  cases x
  case and x₁ x₂ ty =>
    unfold TypedExpr.WellTyped AndWellTyped at h₀
    replace ⟨h₀, h₄⟩ := h₀
    split at h₄
    case _ ty₁ ty₂ heq =>
      simp only [TPE.evaluate, TPE.and]
      have h₅ := partialEvaluate_is_sound x₁ req₁ es₁ req₂ es₂ env h₀ h₁ h₂ h₃
      split
      case _ ty₃ _ _ _ _ heq₁ =>
        rw [heq₁] at h₅
        simp only [Residual.evaluate, Except.toOption] at h₅
        have h₆ := well_typed_expr_cannot_go_wrong h₁ h₀
        rw [heq] at h₆
        cases h₆
        rename_i v h₆
        replace ⟨h₆, h₇⟩ := h₆
        have h₇ := instance_of_ff_is_false h₇
        rw [h₇] at h₆
        simp only [EvaluatesTo] at h₆
        rcases h₆ with h₆₁ | h₆₂ | h₆₃ | h₆₄
        · rw [h₆₁] at h₅
          simp only [reduceCtorEq] at h₅
        · rw [h₆₂] at h₅
          simp only [reduceCtorEq] at h₅
        · rw [h₆₃] at h₅
          simp only [reduceCtorEq] at h₅
        · rw [h₆₄] at h₅
          simp only [Option.some.injEq, Value.prim.injEq, Prim.bool.injEq, Bool.false_eq_true] at h₅
      case _ ty₃ _ _ _ _ heq₁ =>
        simp only [Residual.evaluate, Except.toOption]
        split
        · rename_i v heq₂
          simp only [Option.some.injEq]
          rw [heq₁] at h₅
          simp [Residual.evaluate, Except.toOption] at h₅
          split at h₅
          have h₆ := well_typed_expr_cannot_go_wrong h₁ h₀
          rw [heq] at h₆
          cases h₆
          rename_i h₆
          replace ⟨h₆, h₇⟩ := h₆
          have h₇ := instance_of_ff_is_false h₇
          rw [h₇] at h₆
          · rename_i _ _ _ heq₃ _ _
            simp only [EvaluatesTo] at h₆
            rw [heq₃] at h₆
            simp only [reduceCtorEq, Except.ok.injEq, false_or] at h₆
            rw [h₆] at heq₃
            simp only [TypedExpr.toExpr, Spec.evaluate] at heq₂
            rw [heq₃] at heq₂
            simp only [Result.as, Coe.coe, Value.asBool, Bool.not_eq_eq_eq_not, Bool.not_true,
              bind_pure_comp, Except.bind_ok, ↓reduceIte, Except.ok.injEq] at heq₂
            symm at heq₂
            exact heq₂
          · cases h₅
        · sorry
      case _ ty₃ _ _ _ _ heq₁ =>
        rw [heq₁] at h₅
        simp only [Residual.evaluate, Except.toOption] at h₅
        split at h₅
        · cases h₅
        · rename_i heq₂
          simp only [Except.toOption, TypedExpr.toExpr, Spec.evaluate, Bool.not_eq_eq_eq_not,
            Bool.not_true, bind_pure_comp, Residual.evaluate]
          rw [heq₂]
          simp only [Result.as, Except.bind_err]
      case _ heq₁ _ _ _ =>
        sorry
      case _ =>
        sorry
    case _ _ bty₁ _ heq₁ heq₂ =>
      simp only [TPE.evaluate, TPE.and]
      split
      · have h₅ := partialEvaluate_is_sound x₁ req₁ es₁ req₂ es₂ env h₀ h₁ h₂ h₃
        rename_i heq₃
        simp only [Except.toOption, heq₃, Residual.evaluate] at h₅
        split at h₅
        · rename_i heq₄
          simp only [Option.some.injEq] at h₅
          rw [h₅] at heq₄
          simp only [TypedExpr.toExpr, Spec.evaluate, Bool.not_eq_eq_eq_not, Bool.not_true,
            bind_pure_comp]
          rw [heq₄]
          simp [Result.as, Coe.coe, Value.asBool]
          replace ⟨h₄, h₆⟩ := h₄
          have h₇ := partialEvaluate_is_sound x₂ req₁ es₁ req₂ es₂ env h₄ h₁ h₂ h₃
          have h₇ := to_option_p h₇



          sorry
        · sorry
      · sorry
      · sorry
      · sorry
      sorry
    case _ =>
      sorry
    case _ => simp only at h₄
  case lit => sorry
  case var => sorry
  case ite => sorry
  case or => sorry
  case unaryApp => sorry
  case binaryApp => sorry
  case getAttr => sorry
  case hasAttr => sorry
  case set => sorry
  case record => sorry
  case call => sorry






end Cedar.Thm
