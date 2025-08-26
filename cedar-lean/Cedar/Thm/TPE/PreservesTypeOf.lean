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
import Cedar.Thm.TPE.Input
import Cedar.Thm.Validation.WellTyped.ResidualDefinition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE


/--
Theorem: TPE.evaluate preserves the typeOf property.

If a residual has a certain type, then partially evaluating it produces
a residual with the same type.
-/
theorem partial_eval_preserves_typeof
  {env : TypeEnv}
  {res : Residual}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  {pes : PartialEntities} :
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env res →
  (TPE.evaluate res preq pes).typeOf = res.typeOf := by
  intro h_wf h_ref h_wt
  have h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩
  cases res with
  | val v ty =>
    simp [TPE.evaluate, Residual.typeOf]
  | var v ty =>
    simp [TPE.evaluate, Residual.typeOf]
    unfold varₚ
    simp only [varₚ.varₒ, someOrSelf, Option.bind]
    cases v with
    | principal =>
      cases h: preq.principal.asEntityUID <;> simp
    | resource | action =>
      cases h: preq.resource.asEntityUID <;> simp
    | context =>
      cases h: preq.context <;> simp
  | and a b ty =>
    simp [TPE.evaluate, Residual.typeOf]
    . cases h_wt with
      | and h₁ h₂ h₃ h₄ =>
        split
        all_goals
          rename Residual => x
          rename CedarType => ty
          rename_i heq
          unfold TPE.and at heq
        all_goals
          split at heq

        any_goals
          contradiction

        any_goals
          have h₅ := partial_eval_preserves_typeof h_wf h_ref h₁
          rw [h₃] at h₅
          rw [heq] at h₅
          simp only [Residual.typeOf] at h₅
          exact h₅
        any_goals
          have h₅ := partial_eval_preserves_typeof h_wf h_ref h₂
          rw [heq] at h₅
          rw [h₄] at h₅
          simp [Residual.typeOf] at h₅
          exact h₅

        case h_2 =>
          injection heq with h₅ h₆
          rw [h₆]
        case h_5 =>
          injection heq with h₅ h₆ h₇
          rw [h₇]
        case h_3 =>
          injection heq with h₅
          rw [h₅]
  | or a b ty =>
    simp [TPE.evaluate, Residual.typeOf]
    . cases h_wt with
      | or h₁ h₂ h₃ h₄ =>
        split
        any_goals
          rename Residual => x
          rename CedarType => ty
          rename_i heq
          unfold TPE.or at heq
          split at heq

        any_goals contradiction

        any_goals
          have h₅ := partial_eval_preserves_typeof h_wf h_ref h₂
          rw [heq] at h₅
          rw [h₄] at h₅
          simp [Residual.typeOf] at h₅
          exact h₅

        any_goals
          have h₅ := partial_eval_preserves_typeof h_wf h_ref h₁
          rw [heq] at h₅
          rw [h₃] at h₅
          simp [Residual.typeOf] at h₅
          exact h₅

        case h_1 | h_5 | h_3 =>
          injection heq with h₅
          rename CedarType.bool BoolType.anyBool = ty => h₅
          rw [h₅]
  | ite c t e ty =>
    simp [TPE.evaluate, Residual.typeOf]
    cases h_wt with
    | ite h_c h_t h_e h_ty_c h_ty_t =>
      split
      all_goals
        rename Residual => x
        rename CedarType => result_ty
        rename_i heq
        unfold TPE.ite at heq
        split at heq
        try split at heq

      any_goals contradiction
      any_goals
        have h_t_type := partial_eval_preserves_typeof h_wf h_ref h_t
        rw [heq] at h_t_type
        simp [Residual.typeOf] at h_t_type
        exact h_t_type

      any_goals
        have h_e_type := partial_eval_preserves_typeof h_wf h_ref h_e
        rw [heq] at h_e_type
        rw [h_ty_t]
        rw [← h_e_type]
        simp [Residual.typeOf]

      case h_2 =>
        injection heq with h₁
        rw [h₁]

      case h_3 =>
        have heq' := congr_arg (·.typeOf) heq
        simp [Residual.typeOf] at heq'
        unfold Residual.typeOf
        rw [heq']

  | error ty =>
    simp [TPE.evaluate, Residual.typeOf]
  | unaryApp op e ty =>
    simp [TPE.evaluate, TPE.apply₁]
    split
    . simp [Residual.typeOf]
    . rename CedarType => ty₂
      rename Residual => r
      rename_i h₁
      split
      . rename Option Value => x
        rename Value => v
        rename_i h₂
        unfold Spec.apply₁
        split
        any_goals simp [Residual.typeOf, Except.toOption, someOrError]
        case h_2 =>
          rename Int64 => i
          cases h₃ : i.neg?

          all_goals
            simp [intOrErr, Except.toOption, someOrError, Residual.typeOf]
      . simp [Residual.typeOf, Except.toOption, someOrError]
  | binaryApp op e ty ty₂ =>
    simp [TPE.evaluate, TPE.apply₂]
    split
    case h_1 =>
      split
      any_goals simp [Residual.typeOf, Except.toOption, someOrError]
      case h_8 =>
        rename_i i j h₁ h₂
        cases i.add? j
        all_goals simp
      case h_9 =>
        rename_i i j h₁ h₂
        cases i.sub? j
        all_goals simp
      case h_10 =>
        rename_i i j h₁ h₂
        cases i.mul? j
        all_goals simp
      case h_14 =>
        rename_i v₁ v₂ uid₁ uid₂ h₁ h₂
        cases (TPE.inₑ uid₁ uid₂ pes)
        any_goals simp [someOrSelf, apply₂.self]
      case h_15 =>
        rename_i uid₁ uid₂ vs h₃
        cases (TPE.inₛ uid₁ uid₂ pes)
        any_goals (simp [someOrSelf, apply₂.self])
      case h_16 =>
        rename_i uid₁ tag h₃ h₄
        cases (TPE.hasTag uid₁ tag pes)
        any_goals (simp [someOrSelf, apply₂.self])
      case h_17 uid₁ tag _ _ =>
        cases h_wt with
        | binaryApp h₆ h₇ h₈ =>
        have ih := partial_eval_preserves_typeof h_wf h_ref h₆
        unfold TPE.getTag
        cases pes.tags uid₁
        case binaryApp.none =>
          simp
        case binaryApp.some v =>
          simp [someOrError]
          cases v.find? tag <;> simp
    case h_2 =>
      split
      all_goals simp only [Residual.typeOf]
      split
      all_goals
        rename_i h₂
        simp [apply₂.self] at h₂
      case h_7 =>
        rcases h₂ with ⟨_, ⟨_, ⟨_, h₃⟩⟩⟩
        rw [h₃]
  | call xfn args ty =>
    unfold TPE.evaluate
    simp [Residual.typeOf]
    split <;> rename_i h₁
    
    all_goals
      simp [TPE.call] at h₁
      split at h₁
      . simp [someOrError] at h₁
        split at h₁
        all_goals
          have h₂ := congr_arg (·.typeOf) h₁
          simp [Residual.typeOf] at h₂
          rw [h₂]
      . split at h₁
        all_goals
          have h₂ := congr_arg (·.typeOf) h₁
          simp [Residual.typeOf] at h₂
          rw [h₂]
  | getAttr expr attr ty =>
    simp [TPE.evaluate, TPE.getAttr]
    split
    . simp [Residual.typeOf]
    . split
      . unfold someOrError
        split
        . simp [Residual.typeOf]
        . simp [Residual.typeOf]
      . simp [Residual.typeOf]
  | hasAttr expr attr ty =>
    simp [TPE.evaluate, TPE.hasAttr]
    split
    . simp [Residual.typeOf]
    . split
      . cases h_wt
        . simp [Residual.typeOf]
        . simp [Residual.typeOf]
      . simp [Residual.typeOf]
  | set =>
    simp [TPE.evaluate, Residual.typeOf]
    split
    all_goals
      rename_i h₁
      unfold TPE.set at h₁
      split at h₁
      case h_2 =>
        split at h₁
        all_goals
          have h₂ := congr_arg (·.typeOf) h₁
          simp only [Residual.typeOf] at h₂
          rw [h₂]
      all_goals
        have h₂ := congr_arg (·.typeOf) h₁
        simp only [Residual.typeOf] at h₂
        rw [h₂]
  | record =>
    simp [TPE.evaluate, Residual.typeOf]
    split
    all_goals
      rename_i h₁
      unfold record at h₁
      have h₂ := congr_arg (·.typeOf) h₁

    case h_1 =>
      split at h₁
      . simp at h₁
        rcases h₁ with ⟨_, h₂⟩
        rw [h₂]
      . split at h₁
        all_goals
          have h₃ := congr_arg (·.typeOf) h₁
          simp [Residual.typeOf] at h₃
          rw [h₃]

    all_goals
      split at h₁
      . simp at h₁
      . split at h₁
        all_goals
          have h₃ := congr_arg (·.typeOf) h₁
          simp [Residual.typeOf] at h₃
          rw [h₃]
