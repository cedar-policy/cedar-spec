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
import Cedar.Thm.WellTyped
import Cedar.Thm.TPE.Input

namespace Cedar.Spec

inductive Residual.ErrorFree : Residual → Prop where
  | val : Residual.ErrorFree (.val v ty)
  | var : Residual.ErrorFree (.var v ty)
  | mem : Residual.ErrorFree x₁ → Residual.ErrorFree x₂ → Residual.ErrorFree (.binaryApp .mem x₁ x₂ ty)
  | eq :  Residual.ErrorFree x₁ → Residual.ErrorFree x₂ → Residual.ErrorFree (.binaryApp .eq x₁ x₂ ty)
  | is : Residual.ErrorFree x₁ → Residual.ErrorFree (.unaryApp (.is _) x₁ ty)
  | and : Residual.ErrorFree x₁ → Residual.ErrorFree x₂ → Residual.ErrorFree (.and x₁ x₂ ty)
  -- TODO: Can extend to accept everything that doesn't do arithmetic,
  -- attribute/tag/hierarchy access, or an extension call.

end Cedar.Spec

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation

theorem error_free_spec (r : Residual) : r.errorFree = true ↔ r.ErrorFree := by
  cases r
  any_goals
    simp only [Residual.errorFree, Bool.false_eq_true, false_iff]
    intro hc
    cases hc
  case val =>
    simp only [Residual.errorFree, true_iff]
    constructor
  case var =>
    simp only [Residual.errorFree, true_iff]
    constructor
  case binaryApp op x₁ x₂ _ =>
    cases op
    all_goals
      simp only [Residual.errorFree, Bool.false_eq_true, Bool.and_eq_true, false_iff ]
    any_goals
      intro hc
      cases hc
    all_goals
      have ih₁ := error_free_spec x₁
      have ih₂ := error_free_spec x₂
      rw [ih₁, ih₂]
      constructor
      · intro ⟨h₁, h₂⟩
        constructor <;> assumption
      · intro h
        cases h
        rename_i h₁ h₂
        exact .intro h₁ h₂
  case unaryApp op x₁ _ =>
    cases op
    all_goals
      simp only [Residual.errorFree, Bool.false_eq_true, false_iff]
    any_goals
      intro hc
      cases hc
    have ih₁ := error_free_spec x₁
    rw [ih₁]
    constructor
    · intro h₁
      exact .is h₁
    · intro h
      cases h
      rename_i h
      exact h
  case and x₁ x₂ _ =>
    simp only [Residual.errorFree, Bool.and_eq_true]
    have ih₁ := error_free_spec x₁
    have ih₂ := error_free_spec x₂
    rw [ih₁, ih₂]
    constructor
    · intro ⟨h₁, h₂⟩
      exact .and h₁ h₂
    · intro h
      cases h
      rename_i h₁ h₂
      exact .intro h₁ h₂

-- I don't need this theorem ATM. Leaving not in case I think I need it again
-- later.
--
-- NOTE: This theorem isn't quite correct. There's a bit of a hang up with
-- optional attributes and tags. The `WellTyped` property of a residual doesn't
-- have enough information to conclude that these expression never error (it
-- doesn't say anything about the capabilities tracked during typechecking).
--
-- We probably could bake capabilities into the residual but TBH that doesn't
-- sound fun. Instead I'm hoping we can ignore this case because `getTag` and
-- `.` are both possibly erroring operations regardless of capabilities due to
-- the possibility of a missing entity. I'm not sure how `hasTag` and `has` fit
-- into this. They never error under any circumstance, so I can probably ignore
-- them entirely.
theorem well_typed_residual_eval {r : Residual} :
  InstanceOfWellFormedEnvironment req es env →
  Residual.WellTyped env r →
  (r.evaluate req es) = .error .entityDoesNotExist ∨
  (r.evaluate req es) = .error .extensionError ∨
  (r.evaluate req es) = .error .arithBoundsError ∨
  ∃ v, (r.evaluate req es) = .ok v
:= by sorry -- by typechecker soundness

theorem error_free_evaluate_ok {r : Residual} :
  InstanceOfWellFormedEnvironment req es env →
  Residual.WellTyped env r →
  r.ErrorFree →
  (r.evaluate req es).isOk
:= by
  intro hwf hwt h₂
  cases h₂
  · -- val case
    simp [Residual.evaluate, Except.isOk, Except.toBool]
  · -- var case
    rename_i v _
    cases v <;>
    simp [Residual.evaluate, Except.isOk, Except.toBool]
  · -- mem case
    simp [Residual.evaluate, Except.isOk, Except.toBool]
    rename_i x₁ x₂ _ he₁ he₂
    cases hwt
    rename_i hwt₁ hwt₂ hwt
    have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
    have ih₂ := error_free_evaluate_ok hwf hwt₂ he₂
    simp [Except.isOk, Except.toBool] at ih₁ ih₂
    split at ih₁ <;> try contradiction
    clear ih₁ ; rename_i ih₁
    split at ih₂ <;> try contradiction
    clear ih₂ ; rename_i ih₂
    simp [ih₁, ih₂]
    simp [apply₂]
    split
    all_goals
      rename_i heval'
      split at heval'
    any_goals
      contradiction
    any_goals
      rfl
    · sorry
    · sorry
  · simp [Residual.evaluate, Except.isOk, Except.toBool, apply₂]
    rename_i x₁ x₂ _ he₁ he₂
    cases hwt
    rename_i hwt₁ hwt₂ hwt
    have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
    have ih₂ := error_free_evaluate_ok hwf hwt₂ he₂
    simp only [Except.isOk, Except.toBool] at ih₁ ih₂
    split at ih₁ <;> try contradiction
    clear ih₁ ; rename_i ih₁
    split at ih₂ <;> try contradiction
    clear ih₂ ; rename_i ih₂
    simp [ih₁, ih₂]
  · -- is case
    simp [Residual.evaluate, Except.isOk, Except.toBool]
    rename_i x₁ _ he₁
    cases hwt
    rename_i hwt₁ hwt
    have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
    simp [Except.isOk, Except.toBool] at ih₁
    split at ih₁ <;> try contradiction
    clear ih₁ ; rename_i ih₁
    simp [ih₁, apply₁]
    split <;> try rfl
    rename_i heval'
    split at heval' <;> try contradiction
    rename_i h_not_entity
    simp at heval'
    subst heval'
    cases hwt
    rename_i hty₁
    have hty₁' := residual_well_typed_is_sound hwf hwt₁ ih₁
    rw [hty₁] at hty₁'
    have ⟨_, h_entity⟩ := instance_of_entity_type_is_entity hty₁'
    simp [h_entity] at h_not_entity
  · simp [Residual.evaluate, Except.isOk, Except.toBool]
    rename_i x₁ x₂ _ he₁ he₂
    cases hwt with
    | and hwt₁ hwt₂ hty₁ hty₂ =>
      have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
      have ih₂ := error_free_evaluate_ok hwf hwt₂ he₂
      simp [Except.isOk, Except.toBool] at ih₁ ih₂
      split at ih₁ <;> try contradiction
      clear ih₁ ; rename_i ih₁
      split at ih₂ <;> try contradiction
      clear ih₂ ; rename_i ih₂
      simp [ih₁, ih₂, Result.as, Coe.coe, Value.asBool]
      split <;> try rfl
      rename_i heval'
      split at heval'
      · simp at heval'
        split at heval'
        · contradiction
        · have hwts₂ := residual_well_typed_is_sound hwf hwt₂ ih₂
          rw [hty₂] at hwts₂
          have ⟨_, hb⟩ := instance_of_anyBool_is_bool hwts₂
          subst hb
          simp at heval'
      · have hwts₁ := residual_well_typed_is_sound hwf hwt₁ ih₁
        rw [hty₁] at hwts₁
        have ⟨_, hb⟩ := instance_of_anyBool_is_bool hwts₁
        subst hb
        rename_i h_not_bool
        simp at h_not_bool

end Cedar.Thm
