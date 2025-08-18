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

/-!
This file contains theorems about partial evaluation preserving well-typedness of residuals.
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

abbrev PEWellTyped (env : TypeEnv)
  (r₁ r₂ : Residual)
  (req : Request)
  (preq : PartialRequest)
  (es : Entities)
  (pes : PartialEntities) : Prop :=
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env r₁ →
  Residual.WellTyped env r₂


/--
Theorem: TPE.evaluate preserves the typeOf property.

If a residual has a certain type, then partially evaluating it produces
a residual with the same type. This is a key property for type preservation
in partial evaluation.
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
  -- Proof by cases on the structure of the residual
  cases res with
  | val v ty =>
    -- Case: .val v ty
    -- TPE.evaluate (.val v ty) = .val v ty, so typeOf is preserved
    simp [TPE.evaluate, Residual.typeOf]
  | var v ty =>
    -- Case: .var v ty
    -- This case is more complex as varₚ can return different residuals
    simp [TPE.evaluate, Residual.typeOf]
    unfold varₚ
    cases v with
    | principal =>
      -- For each variable case, we need to show that varₚ preserves the type
      -- This requires analyzing the someOrSelf function
      dsimp [varₚ.varₒ]
      cases h: preq.principal.asEntityUID
      . dsimp [someOrSelf, Option.bind]
      . dsimp [someOrSelf]
    | resource | action =>
      dsimp [varₚ.varₒ]
      cases h: preq.resource.asEntityUID
      . dsimp [someOrSelf, Option.bind]
      . dsimp [someOrSelf]
    | context =>
      dsimp [varₚ.varₒ]
      dsimp [someOrSelf, Option.bind]
      cases h: preq.context
      . simp
      . simp
  | and a b ty =>
    simp [TPE.evaluate, Residual.typeOf]
    . cases h_wt with
      | and h₁ h₂ h₃ h₄ =>
        split
        any_goals (
          rename Residual => x
          rename CedarType => ty
          rename_i heq
          unfold TPE.and at heq
          split at heq
          . have h₅ := partial_eval_preserves_typeof h_wf h_ref h₂
            rw [heq] at h₅
            rw [h₄] at h₅
            simp [Residual.typeOf] at h₅
            exact h₅
          . (first
             | contradiction
             | injection heq with h₅ h₆
               rw [h₆])
          . first
            | contradiction
            | injection heq
              rename_i heq
              rw [heq]
          . have h₅ := partial_eval_preserves_typeof h_wf h_ref h₁
            rw [h₃] at h₅
            rw [heq] at h₅
            simp [Residual.typeOf] at h₅
            exact h₅
          . first
            | contradiction
            | injection heq with h₅ h₆ h₇
              rw [h₇]
          )
  | or a b ty =>
    simp [TPE.evaluate, Residual.typeOf]
    . cases h_wt with
      | or h₁ h₂ h₃ h₄ =>
        split
        repeat case _ =>
          rename Residual => x
          rename CedarType => ty
          rename_i heq
          unfold TPE.or at heq
          split at heq

          . injection heq
            try rename_i heq
            try rw [heq]
          . have h₅ := partial_eval_preserves_typeof h_wf h_ref h₂
            rw [heq] at h₅
            rw [h₄] at h₅
            simp [Residual.typeOf] at h₅
            exact h₅
          . (first
             | contradiction
             | injection heq with h₅
               rw [h₅])
          . have h₅ := partial_eval_preserves_typeof h_wf h_ref h₁
            rw [heq] at h₅
            rw [h₃] at h₅
            simp [Residual.typeOf] at h₅
            exact h₅
          . first
            | contradiction
            | injection heq with h₅ h₆ h₇
              rw [h₇]
  | ite c t e ty =>
    -- Case: .ite c t e ty
    -- TPE.evaluate (.ite c t e ty) = TPE.ite (TPE.evaluate c) (TPE.evaluate t) (TPE.evaluate e) ty
    simp [TPE.evaluate, Residual.typeOf]
    cases h_wt with
    | ite h_c h_t h_e h_ty_c h_ty_t =>
      split
      repeat case _ =>
        rename Residual => x
        rename CedarType => result_ty
        rename_i heq
        unfold TPE.ite at heq
        split at heq
        · split at heq
          · -- b = true case
            have h_t_type := partial_eval_preserves_typeof h_wf h_ref h_t
            rw [heq] at h_t_type
            simp [Residual.typeOf] at h_t_type
            exact h_t_type
          · -- b = false case
            have h_e_type := partial_eval_preserves_typeof h_wf h_ref h_e
            rw [heq] at h_e_type
            rw [h_ty_t]
            rw [← h_e_type]
            simp [Residual.typeOf]
        · first
          | contradiction
          | injection heq with h₁
            rw [h₁]
        · first
          | contradiction
          | have heq' := congr_arg (·.typeOf) heq
            simp [Residual.typeOf] at heq'
            unfold Residual.typeOf
            rw [heq']
  | error ty =>
    -- Case: .error ty
    -- TPE.evaluate (.error ty) = .error ty, so typeOf is preserved
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
        . rename Int64 => i
          cases h₃ : i.neg?
          all_goals
            simp [intOrErr, Except.toOption, someOrError, Residual.typeOf]
      . simp [Residual.typeOf, Except.toOption, someOrError]
  | binaryApp op e ty =>
    simp [TPE.evaluate, TPE.apply₂]
    split
    . split
      any_goals simp [Residual.typeOf, Except.toOption, someOrError]
      . rename_i i j h₁ h₂
        cases i.add? j
        all_goals simp
      . rename_i i j h₁ h₂
        cases i.sub? j
        all_goals simp
      . rename_i i j h₁ h₂
        cases i.mul? j
        all_goals simp
      . rename_i v₁ v₂ uid₁ uid₂ h₁ h₂
        cases (TPE.inₑ uid₁ uid₂ pes)
        any_goals simp [someOrSelf, apply₂.self]
      . rename_i uid₁ uid₂ vs h₃
        cases (TPE.inₛ uid₁ uid₂ pes)
        any_goals (simp [someOrSelf, apply₂.self])
      . rename_i uid₁ tag h₃ h₄
        cases (TPE.hasTag uid₁ tag pes)
        any_goals (simp [someOrSelf, apply₂.self])
      . rename_i uid₁ tag h₃ h₄
        split
        . cases h_wt
          rename_i h₅ h₆ h₇ h₈
          have ih := partial_eval_preserves_typeof h_wf h_ref h₆
          unfold TPE.getTag at h₅
          split at h₅
          . unfold someOrError at h₅
            split at h₅
            all_goals (
              have h₉ := congr_arg (·.typeOf) h₅
              simp [Residual.typeOf] at h₉
              rw [h₉]
            )
          . have h₉ := congr_arg (·.typeOf) h₅
            simp [Residual.typeOf] at h₉
            rw [h₉]
        repeat case _ =>
          rename_i h₅
          unfold TPE.getTag at h₅
          split at h₅
          . unfold someOrError at h₅
            split at h₅
            all_goals (
              have h₉ := congr_arg (·.typeOf) h₅
              simp [Residual.typeOf] at h₉
              rw [h₉])
          . simp at h₅
        . rename_i h₅
          unfold TPE.getTag at h₅
          split at h₅
          . unfold someOrError at h₅
            split at h₅
            all_goals (
              have h₉ := congr_arg (·.typeOf) h₅
              simp [Residual.typeOf] at h₉
              rw [h₉])
          . simp at h₅
            rcases h₅ with ⟨_, ⟨_, ⟨_, h₆⟩⟩⟩
            rw [h₆]
        -- TODO same as repeat case _ above
        repeat case _ =>
          rename_i h₅
          unfold TPE.getTag at h₅
          split at h₅
          . unfold someOrError at h₅
            split at h₅
            all_goals (
              have h₉ := congr_arg (·.typeOf) h₅
              simp [Residual.typeOf] at h₉
              rw [h₉])
          . simp at h₅
    . split
      all_goals simp [Residual.typeOf]
      split
      all_goals (
        rename_i h₂
        simp [apply₂.self] at h₂)
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
        all_goals (
          have h₂ := congr_arg (·.typeOf) h₁
          simp [Residual.typeOf] at h₂
          rw [h₂])
      . split at h₁
        all_goals (
          have h₂ := congr_arg (·.typeOf) h₁
          simp [Residual.typeOf] at h₂
          rw [h₂])
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
    repeat case _ =>
      rename_i h₁
      unfold TPE.set at h₁
      split at h₁
      repeat case _ =>
        have h₂ := congr_arg (·.typeOf) h₁
        simp [Residual.typeOf] at h₂
        rw [h₂]
      split at h₁
      repeat case _ =>
        have h₂ := congr_arg (·.typeOf) h₁
        simp [Residual.typeOf] at h₂
        rw [h₂]
  | record =>
    simp [TPE.evaluate, Residual.typeOf]
    split
    repeat case _ =>
      rename_i h₁
      unfold record at h₁
      split at h₁
      repeat case _ =>
        have h₂ := congr_arg (·.typeOf) h₁
        simp [Residual.typeOf] at h₂
        rw [h₂]
    . rename_i h₁
      unfold record at h₁
      split at h₁
      . simp at h₁
        rcases h₁ with ⟨_, h₂⟩
        rw [h₂]
      . split at h₁
        repeat case _ =>
          have h₂ := congr_arg (·.typeOf) h₁
          simp [Residual.typeOf] at h₂
          rw [h₂]
    repeat case _ =>
      rename_i h₁
      unfold record at h₁
      split at h₁
      . simp at h₁
      . split at h₁
        repeat case _ =>
          have h₂ := congr_arg (·.typeOf) h₁
          simp [Residual.typeOf] at h₂
          rw [h₂]


theorem partial_eval_well_typed_app₂ :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  PEWellTyped env (Residual.binaryApp op expr1 expr2 ty) (TPE.apply₂ op (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) pes ty) req preq es pes := by
  unfold PEWellTyped
  intros ih₁ ih₂ h_wf h_ref h_wt
  unfold TPE.apply₂

  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref
  let h_ref₂ := h_ref
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wf₂ := h_wf
  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op
  split
  . simp
    split
    . apply Residual.WellTyped.val
      cases h_op
      all_goals {
        apply InstanceOfType.instance_of_bool
        unfold InstanceOfBoolType
        split <;> try simp
        contradiction
      }
    repeat case _ =>
      apply Residual.WellTyped.val
      cases h_op
      all_goals {
        apply InstanceOfType.instance_of_bool
        unfold InstanceOfBoolType
        split <;> try simp
        contradiction
      }
    . rename_i i j h₁ h₂
      cases (i.add? j) <;> simp [someOrError]
      . apply Residual.WellTyped.error
      . apply Residual.WellTyped.val
        cases h_op
        all_goals {
          apply InstanceOfType.instance_of_int
        }
    . rename_i i j h₁ h₂
      cases (i.sub? j) <;> simp [someOrError]
      . apply Residual.WellTyped.error
      . apply Residual.WellTyped.val
        cases h_op
        all_goals {
          apply InstanceOfType.instance_of_int
        }
    . rename_i i j h₁ h₂
      cases (i.mul? j) <;> simp [someOrError]
      . apply Residual.WellTyped.error
      . apply Residual.WellTyped.val
        cases h_op
        all_goals {
          apply InstanceOfType.instance_of_int
        }
    . rename_i i j h₁ h₂
      apply Residual.WellTyped.val
      cases h_op
      all_goals {
        apply InstanceOfType.instance_of_bool
        simp [InstanceOfBoolType]
      }
    repeat case _ =>
      apply Residual.WellTyped.val
      cases h_op
      all_goals {
        apply InstanceOfType.instance_of_bool
        simp [InstanceOfBoolType]
      }
    any_goals (
      rename_i v1 v2 id1 id2 h₁ h₂
      try cases (TPE.inₑ id1 id2 pes)
      try cases (TPE.inₛ id1 id2 pes)
      . simp [someOrSelf]
        unfold TPE.apply₂.self
        unfold Residual.asValue at h₁
        unfold Residual.asValue at h₂
        split at h₁
        . split at h₂
          . injection h₁
            injection h₂
            rename_i x v ty₁ h₃ h₄ h₅ ty₂ h₇ h₈ h₉
            rw [h₃]
            rw [h₇]
            apply Residual.WellTyped.binaryApp
            . apply Residual.WellTyped.val
              rw [h₃] at ih₁
              rw [h₇] at ih₂
              cases ih₁
              rename_i h₈
              exact h₈
            . apply Residual.WellTyped.val
              rw [h₃] at ih₁
              rw [h₇] at ih₂
              cases ih₂
              rename_i h₈
              exact h₈
            . rw [h₈]
              rw [h₉]
              cases h_op
              . apply BinaryResidualWellTyped.memₑ
                . simp [Residual.typeOf]
                  rename_i ety₁ ety₂ eq₁ eq₂
                  have hᵣ : (ty₁ = CedarType.entity ety₁) := by {
                    have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr1
                    rw [← h₁₀] at eq₁
                    rw [h₃] at eq₁
                    simp [Residual.typeOf] at eq₁
                    exact eq₁
                  }
                  exact hᵣ
                . simp [Residual.typeOf]
                  rename_i ety₁ ety₂ eq₁ eq₂
                  have hᵣ : (ty₂ = CedarType.entity ety₂) := by {
                    have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr2
                    rw [← h₁₀] at eq₂
                    rw [h₇] at eq₂
                    simp [Residual.typeOf] at eq₂
                    exact eq₂
                  }
                  exact hᵣ
              . apply BinaryResidualWellTyped.memₛ
                . simp [Residual.typeOf]
                  rename_i ety₁ ety₂ eq₁ eq₂
                  have hᵣ : (ty₁ = CedarType.entity ety₁) := by {
                    have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr1
                    rw [← h₁₀] at eq₁
                    rw [h₃] at eq₁
                    simp [Residual.typeOf] at eq₁
                    exact eq₁
                  }
                  exact hᵣ
                . simp [Residual.typeOf]
                  rename_i ety₁ ety₂ eq₁ eq₂
                  have hᵣ : (ty₂ = (CedarType.entity ety₂).set) := by {
                    have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr2
                    rw [← h₁₀] at eq₂
                    rw [h₇] at eq₂
                    simp [Residual.typeOf] at eq₂
                    exact eq₂
                  }
                  exact hᵣ
          . contradiction
        . contradiction
      . simp [someOrSelf]
        apply Residual.WellTyped.val
        cases h_op
        . apply InstanceOfType.instance_of_bool
          simp [InstanceOfBoolType]
        . apply InstanceOfType.instance_of_bool
          simp [InstanceOfBoolType]
    )
    . rename_i v1 v2 id1 id2 h₁ h₂
      cases TPE.hasTag id1 id2 pes
      . simp [someOrSelf]
        unfold TPE.apply₂.self
        unfold Residual.asValue at h₁
        unfold Residual.asValue at h₂
        split at h₁
        . split at h₂
          . injection h₁
            injection h₂
            rename_i x v ty₁ h₃ h₄ h₅ ty₂ h₇ h₈ h₉
            rw [h₃]
            rw [h₇]
            apply Residual.WellTyped.binaryApp
            . apply Residual.WellTyped.val
              rw [h₃] at ih₁
              rw [h₇] at ih₂
              cases ih₁
              rename_i h₈
              exact h₈
            . apply Residual.WellTyped.val
              rw [h₃] at ih₁
              rw [h₇] at ih₂
              cases ih₂
              rename_i h₈
              exact h₈
            . rw [h₈]
              rw [h₉]
              cases h_op
              . apply BinaryResidualWellTyped.hasTag
                . simp [Residual.typeOf]
                  rename_i ety₁ ety₂ eq₁ eq₂
                  have hᵣ : (ty₁ = CedarType.entity ety₂) := by {
                    have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr1
                    rw [← h₁₀] at eq₁
                    rw [h₃] at eq₁
                    simp [Residual.typeOf] at eq₁
                    exact eq₁
                  }
                  exact hᵣ
                . simp [Residual.typeOf]
                  rename_i ety₁ ety₂ eq₁ eq₂
                  have hᵣ : (ty₂ = CedarType.string) := by {
                    have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr2
                    rw [← h₁₀] at eq₂
                    rw [h₇] at eq₂
                    simp [Residual.typeOf] at eq₂

                    exact eq₂
                  }
                  exact hᵣ
          . contradiction
        . contradiction
      . simp [someOrSelf]
        apply Residual.WellTyped.val
        cases h_op
        . apply InstanceOfType.instance_of_bool
          simp [InstanceOfBoolType]
    . rename_i v1 v2 id1 id2 h₁ h₂
      unfold TPE.getTag
      split
      . unfold someOrError
        split
        . apply Residual.WellTyped.val
          rename Option (Data.Map Tag Value) => x
          rename_i tags heq x₁ x₂ x₃ v h₃
          cases h_op
          rename_i ety ty h₄ h₅ h₆
          unfold EntitiesRefine at h_eref
          unfold Data.Map.find? at h₃
          split at h₃
          case h_2 =>  contradiction
          dsimp [PartialEntities.tags, PartialEntities.get] at heq
          rename Value => v₂
          cases h₇: (Data.Map.find? pes id1)
          case h_1.none =>
            rw [h₇] at heq
            simp at heq

          rename Value => v₃
          rename PartialEntityData => pv
          specialize h_eref id1 pv h₇
          rw [h₇] at heq
          simp at heq
          cases h_eref
          case h_1.some.inl =>
            rename_i heq₂ h₈
            rcases h₈ with ⟨h₉, _⟩
            unfold PartialEntityData.tags at heq
            rw [h₉] at heq
            simp at heq
            rw [← heq] at heq₂
            simp [Data.Map.kvs] at heq₂
            unfold Data.Map.empty at heq₂
            dsimp [Data.Map.mk] at heq₂
            contradiction
          rename_i h₈
          rcases h₈ with ⟨e, ⟨h₈, ⟨h₉, ⟨h₁₀, h₁₁⟩⟩⟩⟩
          rw [heq] at h₁₁
          cases h₁₁
          rename_i h₁₂
          rename_i h₁₃
          rw [h₁₂] at h₁₃
          unfold InstanceOfWellFormedEnvironment at h_wf
          rcases h_wf with ⟨h₁₄, ⟨h₁₅, h₁₆⟩⟩
          unfold InstanceOfSchema at h₁₆
          rcases h₁₆ with ⟨h₁₆, h₁₇⟩
          specialize h₁₆ id1 e h₈
          unfold InstanceOfSchemaEntry at h₁₆
          cases h₁₆
          . rename_i h₁₆
            unfold InstanceOfEntitySchemaEntry at h₁₆
            rcases h₁₆ with ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, h₁₇⟩⟩⟩⟩⟩
            unfold InstanceOfEntityTags at h₁₇
            rename EntitySchemaEntry => w
            cases h₁₈: w.tags? <;> rw [h₁₈] at h₁₇ <;> simp at h₁₇
            . rw [h₁₇] at h₁₃
              simp [Data.Map.empty, Data.Map.mk, Data.Map.kvs] at h₁₃
            . have h₁₈ : v₃ ∈ e.tags.values := by {
                -- Use h₁₃
                -- use lemma find?_mem_toList
                have h₁₉ := List.list_find?_mem_toList h₁₃
                have h₂₀ := Map.in_list_in_values h₁₉
                exact h₂₀
              }
              specialize h₁₇ v₃ h₁₈
              rename CedarType => ty
              rename_i h₁₉
              rename CedarType => ty₂
              injection h₃
              rename_i h₃
              rw [← h₃]
              -- h₄ is finally useful
              rename Data.Map.find? env.ets id1.ty = some w => h₂₁
              unfold EntitySchema.tags? at h₄
              have h_ety_eq : ety = id1.ty := by {
                have h₂₁ := partial_eval_preserves_typeof h_wf₂ h_ref₂ h_expr1
                rw [← h₂₁] at h₅
                unfold Residual.asValue at h₁
                cases h₂₂: TPE.evaluate expr1 preq pes
                . rw [h₂₂] at h₁
                  rename Value => v₄
                  simp at h₁
                  rw [h₁] at h₂₂
                  rw [h₂₂] at h₅
                  rw [h₂₂] at h₂₁
                  rename  expr1.typeOf = CedarType.entity ety => h₂₃
                  rw [h₂₃] at h₂₁
                  simp [Residual.typeOf] at h₂₁
                  rename CedarType => ty₃
                  rw [h₂₂] at ih₁
                  cases ih₁
                  rename_i h₂₃
                  rw [h₂₁] at h₂₃
                  cases h₂₃
                  rename_i h₂₄
                  unfold InstanceOfEntityType at h₂₄
                  rcases h₂₄ with ⟨h₂₄, _⟩
                  exact h₂₄
                all_goals {
                  rw [h₂₂] at h₁
                  simp at h₁
                }
              }
              rw [h_ety_eq] at h₄
              rw [h₂₁] at h₄
              simp at h₄
              rw [h₁₉] at h₄
              simp at h₄
              -- h₄ should now be: ty₂ = ty
              rw [h₄] at h₁₇
              exact type_lifting_preserves_instance_of_type h₁₇
          . rename_i h₁₆
            unfold InstanceOfActionSchemaEntry at h₁₆
            rcases h₁₆ with ⟨_, ⟨h₁₇, ⟨_, ⟨_, _⟩⟩⟩⟩
            rw [h₁₇] at h₁₃
            simp [Data.Map.empty, Data.Map.kvs] at h₁₃
        . apply Residual.WellTyped.error
      . apply Residual.WellTyped.binaryApp
        . unfold Residual.asValue at h₁
          cases h₃: TPE.evaluate expr1 preq pes
          all_goals (rw [h₃] at h₁
                     simp at h₁)
          rename_i x heq v ty
          rw [h₃] at ih₁
          rw [h₁] at ih₁
          have h_ety_eq : ty = (CedarType.entity id1.ty) := by {
                have h₄ := partial_eval_preserves_typeof h_wf₂ h_ref₂ h_expr1
                cases ih₁
                rename_i h₅
                cases h₅
                rename EntityType => ty₂
                rename_i h₅
                unfold InstanceOfEntityType at h₅
                rcases h₅ with ⟨h₅, _⟩
                rw [h₅]
              }
          rw [h_ety_eq] at ih₁
          exact ih₁
        . apply Residual.WellTyped.val
          apply InstanceOfType.instance_of_string
        . cases h_op with
          | getTag h₃ h₄ h₅ =>
          apply BinaryResidualWellTyped.getTag
          . simp [Residual.typeOf]
            rfl
          . simp [Residual.typeOf]
          . rename_i ety ty
            have h₄ : ety = id1.ty := by {
              have h₄ := partial_eval_preserves_typeof h_wf₂ h_ref₂ h_expr1
              simp [Residual.asValue] at h₁
              split at h₁
              case h_2 =>
                contradiction
              rename_i x v ty h₅
              rw [h₅] at ih₁
              cases ih₁
              rename_i h₆
              injection h₁ with h₇
              rw [h₇] at h₆
              rw [h₅] at h₄
              rw [h₃] at h₄
              rw [h₇] at h₄
              simp [Residual.typeOf] at h₄
              cases h₆
              rename_i ety₂ h₈
              injection h₄ with h₄
              unfold InstanceOfEntityType at h₈
              rcases h₈ with ⟨h₉, _⟩
              rw [h₉] at h₄
              rw [h₄]
            }
            rw [h₄] at h₅
            exact h₅
    . apply Residual.WellTyped.error
  . let h₇ := partial_eval_preserves_typeof h_wf h_ref h_expr1
    have h₈ := partial_eval_preserves_typeof h_wf h_ref h_expr2
    split
    any_goals (apply Residual.WellTyped.error)
    rename_i x₁ x₂ h₁ r₁ r₂ h₃ h₄
    unfold apply₂.self
    apply Residual.WellTyped.binaryApp
    cases op
    any_goals (exact ih₁)
    any_goals (exact ih₂)
    cases op
    . cases h₅: h_op
      . cases h_wt₂
        rename_i h₆
        simp [TPE.evaluate]
        exact h₆
      . apply BinaryResidualWellTyped.eq_entity
        . have h₆ := partial_eval_preserves_typeof h_wf h_ref h_expr1
          rw [h₆]
          rename_i h₇ h₈
          rw [h₇]
        . have h₆ := partial_eval_preserves_typeof h_wf h_ref h_expr2
          rw [h₆]
          rename_i h₇ h₈
          rw [h₈]
      . apply BinaryResidualWellTyped.eq
        have h₆ := partial_eval_preserves_typeof h_wf h_ref h_expr1
        have h₇ := partial_eval_preserves_typeof h_wf h_ref h_expr2
        rename_i h₈
        rw [← h₆] at h₈
        rw [← h₇] at h₈
        exact h₈
    . let h₇ := partial_eval_preserves_typeof h_wf h_ref h_expr1
      have h₈ := partial_eval_preserves_typeof h_wf h_ref h_expr2
      cases h_op <;> rename_i ety₁ ety₂ h₅ h₆
      . apply BinaryResidualWellTyped.memₑ
        . rw [h₇]
          rw [h₅]
        . rw [h₈]
          rw [h₆]
      . apply BinaryResidualWellTyped.memₛ
        . rw [h₇]
          rw [h₅]
        . rw [h₈]
          rw [h₆]
    . cases h_op
      apply BinaryResidualWellTyped.hasTag <;> rename_i ety h₅ h₆
      . rw [h₇]
        rw [h₅]
        congr
        have h₈ : ety = ety := by simp
        exact h₈
      . rw [h₈]
        rw [h₆]
    . cases h_op
      rename_i ety₁ ety₂ ty h₅ h₆
      apply BinaryResidualWellTyped.getTag
      . rw [h₇]
        rw [h₅]
      . rw [h₈]
        rw [h₆]
      . rw [ty]
    . cases h_op <;> rename_i h₅ h₆
      . apply BinaryResidualWellTyped.less_int
        . rw [h₇]
          rw [h₅]
        . rw [h₈]
          rw [h₆]
      . apply BinaryResidualWellTyped.less_datetime
        . rw [h₇]
          rw [h₅]
        . rw [h₈]
          rw [h₆]
      . apply BinaryResidualWellTyped.less_duration
        . rw [h₇]
          rw [h₅]
        . rw [h₈]
          rw [h₆]
    . cases h_op <;> rename_i h₅ h₆
      . apply BinaryResidualWellTyped.lessEq_int
        . rw [h₇]
          rw [h₅]
        . rw [h₈]
          rw [h₆]
      . apply BinaryResidualWellTyped.lessEq_datetime
        . rw [h₇]
          rw [h₅]
        . rw [h₈]
          rw [h₆]
      . apply BinaryResidualWellTyped.lessEq_duration
        . rw [h₇]
          rw [h₅]
        . rw [h₈]
          rw [h₆]
    . cases h_op <;> rename_i h₅ h₆
      apply BinaryResidualWellTyped.add
      . rw [h₇]
        rw [h₅]
      . rw [h₈]
        rw [h₆]
    . cases h_op <;> rename_i h₅ h₆
      apply BinaryResidualWellTyped.sub
      . rw [h₇]
        rw [h₅]
      . rw [h₈]
        rw [h₆]
    . cases h_op <;> rename_i h₅ h₆
      apply BinaryResidualWellTyped.mul
      . rw [h₇]
        rw [h₅]
      . rw [h₈]
        rw [h₆]
    . cases h_op <;> rename_i h₅
      apply BinaryResidualWellTyped.contains
      rw [h₇]
      rw [h₈]
      exact h₅
    . cases h_op <;> rename_i ty h₅ h₆
      apply BinaryResidualWellTyped.containsAll
      rw [h₇]
      rw [h₅]
      rw [h₈]
      rw [h₆]
    . cases h_op <;> rename_i ty h₅ h₆
      apply BinaryResidualWellTyped.containsAny
      rw [h₇]
      rw [h₅]
      rw [h₈]
      rw [h₆]


/--
Helper theorem: Partial evaluation preserves well-typedness for variable residuals.
-/
theorem partial_evaluation_well_typed_var      {env : TypeEnv}
  {v : Var}
  {ty : CedarType}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  :
  PEWellTyped env (Residual.var v ty) (varₚ preq v ty) req preq es pes := by
  intro h_wf h_ref h_wt
  rcases h_ref with ⟨h_rref, h_eref⟩
  unfold varₚ
  cases v with
  | principal =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    cases h : preq.principal.asEntityUID
    . dsimp [varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp [varₚ.varₒ, someOrSelf]
      rw [h] at h_pv
      apply Residual.WellTyped.val
      cases h_pv with
      | some _ h₃ =>
        rw [h₃]
        cases h_wt with
        | var h₄ =>
          cases h₄ with
          | principal =>
            apply InstanceOfType.instance_of_entity req.principal env.reqty.principal
            rcases h_wf with ⟨_, ⟨h_principal, _, _, _⟩, _⟩
            exact h_principal
  | resource =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    cases h : preq.resource.asEntityUID
    . dsimp [varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp [varₚ.varₒ, someOrSelf]
      rw [h] at h_rv
      apply Residual.WellTyped.val
      cases h_rv with
      | some _ h₃ =>
        rw [h₃]
        cases h_wt with
        | var h₄ =>
          cases h₄ with
          | resource =>
            apply InstanceOfType.instance_of_entity req.resource env.reqty.resource
            rcases h_wf with ⟨_, ⟨_, _, h_resource, _⟩, _⟩
            exact h_resource
  | action =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    -- Action is always concrete in partial requests
    dsimp [varₚ.varₒ, someOrSelf]
    apply Residual.WellTyped.val
    cases h_wt with
    | var h₄ =>
      cases h₄ with
      | action =>
        rw [←h_av]
        apply InstanceOfType.instance_of_entity req.action env.reqty.action.ty
        rcases h_wf with ⟨hwf, ⟨_, h_action, _, _⟩, _⟩
        rw [h_action]
        have : InstanceOfEntityType env.reqty.action env.reqty.action.ty env := by
          have ⟨_, _, ⟨_, hwf_act, _⟩⟩ := hwf
          simp [
            InstanceOfEntityType, EntityUID.WellFormed,
            ActionSchema.contains, hwf_act,
          ]
        exact this
  | context =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    cases h : preq.context
    . dsimp [varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp [varₚ.varₒ, someOrSelf]
      rw [h] at h_cv
      apply Residual.WellTyped.val
      cases h_cv with
      | some _ h₃ =>
        rw [h₃]
        cases h_wt with
        | var h₄ =>
          cases h₄ with
          | context =>
            rcases h_wf with ⟨_, ⟨_, _, _, h_context⟩, _⟩
            exact type_lifting_preserves_instance_of_type h_context

theorem partial_eval_record_key_preservation_3 {ls : List (Attr × Residual)} :
  ls.find? (λ x => x.fst == k) = .some (k, v) →
  ∃ v₂,
  (List.map
    (fun x =>
      match x with
      | (a, r) => (a, Qualified.required r.typeOf))
    ls).find? (λ x => x.fst == k) = .some (k, v₂)
:= by
  intro h₁
  cases ls
  . simp at h₁
  . simp at h₁
    cases h₁
    . rename_i hd tl h₁
      rcases h₁ with ⟨h₁, h₂⟩
      exists (Qualified.required v.typeOf)
      simp
      left
      cases hd
      rename_i k₂ v₂
      simp
      simp at h₂
      rcases h₂ with ⟨h₃, h₄⟩
      rw [h₃]
      rw [h₄]
      simp
    . rename_i hd tl h₁
      rcases h₁ with ⟨h₁, h₂⟩
      let ih := partial_eval_record_key_preservation_3 h₂
      rcases ih with ⟨v₂, ih⟩
      exists v₂
      simp at ih
      simp
      right
      constructor
      . assumption
      . rcases ih with ⟨a, b, h₃, h₄, h₅⟩
        exists a
        exists b

theorem partial_eval_record_key_preservation_2 {ls : List (Attr × Residual)} :
  (List.map
    (fun x =>
      match x with
      | (a, r) => (a, Qualified.required r.typeOf))
    ls).find? (λ x => x.fst == k) = .some (k, v₃) →
  ∃ v₂,
  v₃ = Qualified.required v₂.typeOf ∧
  List.find? (fun x => decide (x.fst = k)) ls = some (k, v₂)
:= by
  intro h₁
  cases ls
  . contradiction
  case cons h tl =>
    simp at h₁
    cases h₁
    case inl h₂ =>
      simp at h₂
      rcases h₂ with ⟨h₃, h₄, h₅⟩
      exists h.snd
      simp
      left
      constructor
      . assumption
      . cases h
        simp at h₃
        rw [h₃]
    case inr h₂ =>
      rcases h₂ with ⟨h₂, a, b, h₃, h₄, h₅⟩
      exists b
      constructor
      . rw [h₅]
      . unfold List.find?
        have h₆: (decide (h.fst = k)) = false := by
          simp
          assumption
        rw [h₆]
        simp
        unfold Function.comp at h₃
        simp at h₃
        rw [h₄] at h₃
        exact h₃

theorem partial_eval_record_key_preservation_4 {xs : List (Attr × Residual)} {ys : List (Attr × Value)} :
  List.Forall₂ (fun x y => ((fun x => bindAttr x.fst x.snd.asValue) ∘ fun x => (x.fst, TPE.evaluate x.snd preq pes)) x = some y) xs
  ys →
  xs.find? (λ x => x.fst = k) = .some (k, v) →
  ∃ v₃,
  (ys.find? (λ x => x.fst = k) = .some (k, v₃))
:= by
  intro h₁
  cases h₁
  . simp
  case cons a b l₁ l₂ h₂ h₃=>
  . intro h₄
    simp at h₄
    cases h₄
    case inl h₅ =>
      rcases h₅ with ⟨h₅, h₆⟩
      simp [bindAttr] at h₂
      cases h₇: (TPE.evaluate a.snd preq pes).asValue <;> rw [h₇] at h₂
      case intro.none =>
        simp at h₂
      case intro.some v₂ =>
        simp at h₂
        exists v₂
        simp
        left
        rw [h₅] at h₂
        rw [← h₂]
        simp
    case inr h₅ =>
      rcases h₅ with ⟨h₅, h₆⟩
      have ih := partial_eval_record_key_preservation_4 h₃ h₆
      rcases ih with ⟨v₃, ih⟩
      exists v₃
      simp
      right
      simp [bindAttr] at h₂
      cases h₇: (TPE.evaluate a.snd preq pes).asValue <;> rw [h₇] at h₂
      . simp at h₂
      . simp at h₂
        rw [← h₂]
        simp
        constructor
        . assumption
        .assumption

theorem partial_eval_record_key_preservation {xs : List (Attr × Residual)} {ys : List (Attr × Value)} :
  List.Forall₂ (fun x y => ((fun x => bindAttr x.fst x.snd.asValue) ∘ fun x => (x.fst, TPE.evaluate x.snd preq pes)) x = some y) xs
  ys →
  ys.find? (λ x => x.fst = k) = .some (k, v) →
  ∃ v₂,
  (xs.find? (λ x => x.fst = k) = .some (k, v₂)) ∧
  v = (TPE.evaluate v₂ preq pes).asValue
:= by
  intro h₁ h₂
  cases h₁
  . contradiction
  case cons a₁ b₁ l₁ l₂ h₃ h₄ =>
    simp at h₂
    cases h₂
    case inl h₃ =>
      rename_i h₄
      rename_i h₅
      simp [bindAttr, Residual.asValue] at h₅
      exists a₁.2
      simp
      split at h₅
      . simp at h₅
        rcases h₃ with ⟨h₃, h₆⟩
        rename Value => v₂
        rw [h₆] at h₅
        simp at h₅
        rcases h₅ with ⟨h₅, h₇⟩
        rw [h₅]
        simp
        constructor
        . cases a₁
          rename_i a₁ a₂ h₈
          simp
          simp at h₅
          assumption
        . rename_i h₉
          rw [h₉]
          simp [Residual.asValue]
          rw [h₇]
      . simp at h₅
    case inr h₃ =>
      rcases h₃ with ⟨h₃, h₅⟩
      let ih := partial_eval_record_key_preservation h₄ h₅
      rcases ih with ⟨p₃, ⟨h₄, h₅⟩⟩
      exists p₃
      constructor
      . simp
        right
        rw [h₄]
        simp
        cases a₁
        rename_i k₁ v₁
        cases b₁
        rename_i k₂ v₂
        simp
        simp at h₃
        simp at v₂
        rename_i k₃
        unfold bindAttr at h₃
        simp at h₃
        cases h₄ : (TPE.evaluate v₁ preq pes).asValue
        . rw [h₄] at h₃
          simp at h₃
        . rw [h₄] at h₃
          simp at h₃
          rcases h₃ with ⟨h₅, h₆⟩
          rw [h₅]
          assumption
      . exact h₅


theorem find_lifted_type {m: RecordType} :
  Map.find? m attr = some ty₁ →
  Map.find? m.liftBoolTypes attr = some ty₂ →
  ty₂ = ty₁.liftBoolTypes
:= by
  simp [Map.find?, Map.kvs]
  intro h₁ h₂
  cases h₃: m.1
  . rw [h₃] at h₁
    simp at h₁
  . rename_i hd tl
    rw [h₃] at h₁
    unfold RecordType.liftBoolTypes at h₂
    rw [h₃] at h₂
    simp [CedarType.liftBoolTypesRecord, List.find?] at h₂
    cases h₄ : hd.fst == attr
    case cons.false =>
      rw [h₄] at h₂
      simp at h₂
      simp [List.find?] at h₁
      rw [h₄] at h₁
      simp at h₁
      exact find_lifted_type h₁ h₂
    case cons.true =>
      rw [h₄] at h₂
      simp at h₂
      rw [← h₂]
      simp [List.find?] at h₁
      rw [h₄] at h₁
      simp at h₁
      rw [h₁]
decreasing_by
  have h₅ : sizeOf m.1 < sizeOf m := by {
    simp [sizeOf]
    simp [Map._sizeOf_1]
    sorry
  }
  rename_i hd tail h₆ h₇
  have h₈: sizeOf (Map.mk tail) < sizeOf m.1 := by {
    sorry
  }
  omega


theorem ext_well_typed_after_map :
  ExtResidualWellTyped xfn args ty →
  (∀ x, Residual.WellTyped env x → Residual.WellTyped env (f x)) →
  ExtResidualWellTyped xf (args.map f) ty
:= by
  sorry



/--
Theorem: Partial evaluation preserves well-typedness of residuals.

If a residual is well-typed in some type environment, then partially evaluating it
with a partial request and partial entities produces another well-typed residual
in the same type environment.

This is a fundamental property ensuring that the partial evaluation process
maintains type safety throughout the computation.
-/
theorem partial_eval_preserves_well_typed
  {env : TypeEnv}
  {res : Residual}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  {pes : PartialEntities} :
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env res →
  Residual.WellTyped env (TPE.evaluate res preq pes) := by
  intro h_wf h_ref h_wt
  unfold RequestAndEntitiesRefine at h_ref
  rcases h_ref with ⟨h_rref, h_eref⟩
  have h_ref : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩
  -- Proof by cases on the structure of the residual
  cases res with
  | val v ty =>
    -- Case: .val v ty
    -- TPE.evaluate (.val v ty) req es = .val v ty
    simp [TPE.evaluate]
    exact h_wt
  | var v ty =>
    -- Case: .var v ty
    -- Use the helper theorem for variable cases
    simp [TPE.evaluate]
    exact partial_evaluation_well_typed_var h_wf h_ref h_wt
  | and a b ty =>
    -- Case: .and a b ty
    -- TPE.evaluate (.and a b ty) preq pes = TPE.and (TPE.evaluate a preq pes) (TPE.evaluate b preq pes) ty
    simp [TPE.evaluate]
    -- We need to prove that TPE.and preserves well-typedness
    -- This requires analyzing the cases in TPE.and
    cases h_wt with
    | and h_a h_b h_ty_a h_ty_b =>
      let a_eval := TPE.evaluate a preq pes
      let b_eval := TPE.evaluate b preq pes
      have h_ref_reconstructed : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩
      have h_a_wt : Residual.WellTyped env a_eval := partial_eval_preserves_well_typed h_wf h_ref_reconstructed h_a
      have h_b_wt : Residual.WellTyped env b_eval := partial_eval_preserves_well_typed h_wf h_ref_reconstructed h_b
      -- TPE.and has several cases - we need to handle each one
      unfold TPE.and
      split
      . -- Case: first operand is .val true, so TPE.and returns the second operand
        -- Goal: Residual.WellTyped env (TPE.evaluate b preq pes)
        exact h_b_wt
      . -- Case: first operand is .val false, so TPE.and returns false
        -- Goal: Residual.WellTyped env (Residual.val (Value.prim (Prim.bool false)) (CedarType.bool BoolType.anyBool))
        apply Residual.WellTyped.val
        apply InstanceOfType.instance_of_bool false BoolType.anyBool
        simp [InstanceOfBoolType]
      . -- Case: first operand is .error, so TPE.and returns .error ty
        -- Goal: Residual.WellTyped env (Residual.error ty)
        apply Residual.WellTyped.error
      . -- Case: second operand is .val true, so TPE.and returns the first operand
        -- Goal: Residual.WellTyped env (TPE.evaluate a preq pes)
        exact h_a_wt
      . -- Case: default case, TPE.and returns .and a_eval b_eval ty
        -- Goal: Residual.WellTyped env (Residual.and (TPE.evaluate a preq pes) (TPE.evaluate b preq pes) ty)
        apply Residual.WellTyped.and
        · exact h_a_wt
        · exact h_b_wt
        · -- Need to show a_eval.typeOf = CedarType.bool BoolType.anyBool
          -- This follows from the fact that a has boolean type and TPE preserves types
          have h_a_type : a.typeOf = CedarType.bool BoolType.anyBool := h_ty_a
          -- Use the type preservation theorem
          rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_a]
          exact h_a_type
        · -- Need to show b_eval.typeOf = CedarType.bool BoolType.anyBool
          -- This follows from the fact that b has boolean type and TPE preserves types
          have h_b_type : b.typeOf = CedarType.bool BoolType.anyBool := h_ty_b
          -- Use the type preservation theorem
          rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_b]
          exact h_b_type
  | or a b ty =>
    simp [TPE.evaluate]
    cases h_wt with
    | or h_a h_b h_ty_a h_ty_b =>
      let a_eval := TPE.evaluate a preq pes
      let b_eval := TPE.evaluate b preq pes
      have h_ref_reconstructed : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩
      have h_a_wt : Residual.WellTyped env a_eval := partial_eval_preserves_well_typed h_wf h_ref_reconstructed h_a
      have h_b_wt : Residual.WellTyped env b_eval := partial_eval_preserves_well_typed h_wf h_ref_reconstructed h_b
      unfold TPE.or
      split
      . apply Residual.WellTyped.val
        apply InstanceOfType.instance_of_bool true BoolType.anyBool
        simp [InstanceOfBoolType]
      . exact h_b_wt
      . apply Residual.WellTyped.error
      . exact h_a_wt
      . apply Residual.WellTyped.or
        · exact h_a_wt
        · exact h_b_wt
        · rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_a]
          exact h_ty_a
        · rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_b]
          exact h_ty_b
  | ite c t e ty =>
    simp [TPE.evaluate]
    cases h_wt with
    | ite h_c h_t h_e h_ty_c h_ty_t =>
      let c_eval := TPE.evaluate c preq pes
      let t_eval := TPE.evaluate t preq pes
      let e_eval := TPE.evaluate e preq pes
      have h_ref_reconstructed : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩
      have h_c_wt : Residual.WellTyped env c_eval := partial_eval_preserves_well_typed h_wf h_ref_reconstructed h_c
      have h_t_wt : Residual.WellTyped env t_eval := partial_eval_preserves_well_typed h_wf h_ref_reconstructed h_t
      have h_e_wt : Residual.WellTyped env e_eval := partial_eval_preserves_well_typed h_wf h_ref_reconstructed h_e
      unfold TPE.ite
      split
      . split
        · exact h_t_wt
        · exact h_e_wt
      . apply Residual.WellTyped.error
      . have h_t_type_eq : t.typeOf = t_eval.typeOf := (partial_eval_preserves_typeof h_wf h_ref_reconstructed h_t).symm
        rw [h_t_type_eq]
        apply Residual.WellTyped.ite
        · exact h_c_wt
        · exact h_t_wt
        · exact h_e_wt
        · rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_c]
          exact h_ty_c
        · rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_t]
          rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_e]
          exact h_ty_t
  | unaryApp op expr ty =>
    simp [TPE.evaluate]
    cases h_wt with
    | unaryApp h_expr h_op =>
      let expr_eval := TPE.evaluate expr preq pes
      have h_ref_reconstructed : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩
      have h_expr_wt : Residual.WellTyped env expr_eval := partial_eval_preserves_well_typed h_wf h_ref_reconstructed h_expr
      unfold TPE.apply₁
      split
      . apply Residual.WellTyped.error
      . cases h : expr_eval.asValue with
        | some v =>
          unfold someOrError
          split
          . split
            . rename_i r v₂ ov v₁ v2v ty ox x v heq
              injection v2v with hᵥ
              unfold Spec.apply₁ at heq
              apply Residual.WellTyped.val
              split at heq
              . cases h_op
                simp [Except.toOption] at heq
                rw [← heq]
                apply InstanceOfType.instance_of_bool
                simp [InstanceOfBoolType]
              . cases h_op
                simp [Except.toOption, intOrErr] at heq
                rename Int64 => i
                cases h₂: i.neg?
                . rw [h₂] at heq
                  simp at heq
                . rw [h₂] at heq
                  simp at heq
                  rw [← heq]
                  apply InstanceOfType.instance_of_int
              . cases h_op
                simp [Except.toOption] at heq
                rw [← heq]
                apply InstanceOfType.instance_of_bool
                simp [InstanceOfBoolType]
              . simp [Except.toOption] at heq
                rw [← heq]
                cases h_op
                apply InstanceOfType.instance_of_bool
                simp [InstanceOfBoolType]
              . cases h_op
                simp [Except.toOption] at heq
                rw [← heq]
                apply InstanceOfType.instance_of_bool
                simp [InstanceOfBoolType]
              . contradiction
            . apply Residual.WellTyped.error
          . contradiction
        | none =>
          apply Residual.WellTyped.unaryApp
          · exact h_expr_wt
          · cases h_op with
            | not h_ty =>
              apply UnaryResidualWellTyped.not
              rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_expr]
              exact h_ty
            | neg h_ty =>
              apply UnaryResidualWellTyped.neg
              rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_expr]
              exact h_ty
            | isEmpty h_ty =>
              apply UnaryResidualWellTyped.isEmpty
              rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_expr]
              exact h_ty
            | like h_ty =>
              apply UnaryResidualWellTyped.like
              rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_expr]
              exact h_ty
            | is h_ty =>
              apply UnaryResidualWellTyped.is
              rw [partial_eval_preserves_typeof h_wf h_ref_reconstructed h_expr]
              exact h_ty
  | binaryApp op expr1 expr2 ty =>
    simp [TPE.evaluate]
    have h_wt₂ := h_wt
    cases h_wt with
    | binaryApp h_expr1 h_expr2 h_op =>
      have ih1 : Residual.WellTyped env (TPE.evaluate expr1 preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_expr1
      have ih2 : Residual.WellTyped env (TPE.evaluate expr2 preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_expr2

      apply partial_eval_well_typed_app₂ ih1 ih2 h_wf h_ref h_wt₂
  | error ty =>
    simp [TPE.evaluate]
    exact h_wt
  | set ls ty =>
    cases h_wt
    rename_i ty₁ h₀ h₁ h₂
    simp [TPE.evaluate, TPE.set]
    split
    . rename_i x xs h₃
      apply Residual.WellTyped.val
      apply InstanceOfType.instance_of_set
      intro v h₄
      unfold List.map₁ List.attach List.attachWith at h₃
      rw [List.map_pmap_subtype (fun x => TPE.evaluate x preq pes)] at h₃
      rw [List.mapM_then_map_combiner_option] at h₃
      rw [← Set.make_mem] at h₄
      have h₅ := List.mem_mapM_some_implies_exists_ele h₃ h₄
      rcases h₅ with ⟨y, h₆, h₇⟩
      specialize h₀ y h₆
      let h₈ := partial_eval_preserves_typeof h_wf h_ref h₀
      unfold Residual.asValue at h₇
      split at h₇
      case h_2 =>
        contradiction
      case h_1 x₂ v₂ ty₂ h₉ =>
        injection h₇
        rename_i h₇
        rw [h₇] at h₉
        let ih := partial_eval_preserves_well_typed h_wf h_ref h₀
        rw [h₉] at ih
        cases ih
        case val h₁₀ =>
        specialize h₁ y h₆
        rw [h₁] at h₈
        rw [h₉] at h₈
        simp [Residual.typeOf] at h₈
        rw [← h₈]
        exact h₁₀
    . split
      . apply Residual.WellTyped.error
      . rename_i x h₃ h₄
        apply Residual.WellTyped.set
        . intro x h₅
          simp [List.map₁, List.attach] at h₅
          rcases h₅ with ⟨x₂, h₆, h₇⟩
          specialize h₀ x₂ h₆
          let ih := partial_eval_preserves_well_typed h_wf h_ref h₀
          rw [← h₇]
          exact ih
        . intro x h₅
          simp [List.map₁, List.attach] at h₅
          rcases h₅ with ⟨x₂, h₆, h₇⟩
          specialize h₀ x₂ h₆
          let h₆ := partial_eval_preserves_typeof h_wf h_ref h₀
          rw [h₇] at h₆
          rename_i h₈
          specialize h₁ x₂ h₈
          rw [← h₁]
          exact h₆
        . simp [List.map₁]
          simp at h₂
          exact h₂
  | record ls ty =>
    cases h_wt
    rename_i ty₁ h₀ h₁
    simp [TPE.evaluate, TPE.set]
    unfold List.map₁ List.attach List.attachWith
    rw [List.map_pmap_subtype (fun x => (x.fst, TPE.evaluate x.snd preq pes)) ls]
    simp [record]
    split
    . rename_i x xs h₃
      apply Residual.WellTyped.val
      apply InstanceOfType.instance_of_record
      . intro k h₄
        rw [Map.contains_iff_some_find?] at h₄
        rcases h₄ with ⟨v, h₄⟩

        have h₅ := Map.make_find?_implies_list_find? h₄
        rw [Map.contains_iff_some_find?]
        rw [List.mapM_some_iff_forall₂] at h₃
        have h₈ := partial_eval_record_key_preservation h₃ h₅
        rcases h₈ with ⟨v₂, h₈, h₉⟩
        have h₉ := partial_eval_record_key_preservation_3 h₈
        subst ty₁
        rcases h₉ with ⟨v₃, h₉⟩
        have h₁₀ := Map.list_find?_implies_make_find? h₉
        exists v₃
      . intro k v qty h₄ h₅
        rw [h₁] at h₅
        have h₆ := Map.make_find?_implies_list_find? h₄
        have h₇ := Map.make_find?_implies_list_find? h₅
        rw [List.mapM_some_iff_forall₂] at h₃
        have h₈ := partial_eval_record_key_preservation h₃ h₆
        rcases h₈ with ⟨v₂, h₈, h₉⟩
        have h₉ := partial_eval_record_key_preservation_2 h₇
        rcases h₉ with ⟨v₃, h₉, h₁₀⟩
        rw [h₉]
        have h₁₁ := h₀
        have h₁₂ := List.mem_of_find?_eq_some h₈
        specialize h₁₁ k v₂ h₁₂
        rw [h₁₀] at h₈
        injection h₈
        rename_i h₁₃
        simp at h₁₃
        rw [h₁₃]
        rename_i h₁₄
        simp [Residual.asValue] at h₁₄
        split at h₁₄
        case h_2 => contradiction
        rename_i v₄ ty h₁₅
        injection h₁₄
        rename_i h₁₅
        rw [h₁₅]
        simp [Qualified.getType]
        rename_i h₁₆
        have h₁₇ := partial_eval_preserves_typeof h_wf h_ref h₁₁
        rw [h₁₆] at h₁₇
        rw [←h₁₇]
        simp [Residual.typeOf]
        let ih := partial_eval_preserves_well_typed h_wf h_ref h₁₁
        rw [h₁₆] at ih
        cases ih
        assumption
      . intro k qty h₄ h₅
        subst ty₁
        have h₄ := Map.make_find?_implies_list_find? h₄
        have h₆ := partial_eval_record_key_preservation_2 h₄
        rcases h₆ with ⟨v₂, h₆, h₇⟩
        rw [List.mapM_some_iff_forall₂] at h₃
        have h₈ := partial_eval_record_key_preservation_4 h₃ h₇
        rw [Map.contains_iff_some_find?]
        rcases h₈ with ⟨v₃, h₈⟩
        exists v₃
        exact Map.list_find?_implies_make_find? h₈
    case h_2 x h₂ =>
      split
      . apply Residual.WellTyped.error
      . rename_i h₃
        apply Residual.WellTyped.record
        . intros k v h₄
          have h₅ := List.mem_of_map_implies_exists_unmapped h₄
          rcases h₅ with ⟨p, h₅, h₆⟩
          cases p ; rename_i k₂ v₂
          simp at h₆
          rcases h₆ with ⟨h₆, h₇⟩
          rw [← h₆] at h₅
          specialize h₀ k v₂ h₅
          have ih := partial_eval_preserves_well_typed h_wf h_ref h₀
          rw [h₇]
          assumption
        . rw [h₁]
          simp
          unfold Function.comp
          simp
          congr 2
          -- should be an easy proof with lemma bout forall and function equality
          sorry
  | getAttr expr attr ty =>
    simp [TPE.evaluate, TPE.getAttr, TPE.attrsOf]
    split
    case h_1 =>
      apply Residual.WellTyped.error
    case h_2 r₁ h₁ =>
      split
      case h_1 x m h₂ =>
        split at h₂
        case h_1 r₂ m₂ ty₂ h₃ =>
          injection h₂; rename_i h₂
          rw [h₂] at h₃
          cases h_wt
          case getAttr_entity ety rty h₄ h₅ h₆ h₇ =>
            have ih := partial_eval_preserves_well_typed h_wf h_ref h₅
            rw [h₃] at ih
            cases ih
            rename_i h₇
            cases h₇
            rename_i rty₂ h₈ h₉ h₁₀
            cases h₁₂ : m.find? attr
            . simp [someOrError]
              apply Residual.WellTyped.error
            . rename_i v
              simp [someOrError]
              apply Residual.WellTyped.val
              have h₁₁ := partial_eval_preserves_typeof h_wf h_ref h₅
              rw [h₃] at h₁₁
              rw [h₆] at h₁₁
              simp [Residual.typeOf] at h₁₁
          case getAttr_record rty h₄ h₅ h₆ =>
            have ih := partial_eval_preserves_well_typed h_wf h_ref h₄
            rw [h₃] at ih
            cases ih
            rename_i h₇
            cases h₇
            rename_i rty₂ h₈ h₉ h₁₀
            cases h₁₂ : m.find? attr
            . simp [someOrError]
              apply Residual.WellTyped.error
            . rename_i v
              simp [someOrError]
              apply Residual.WellTyped.val
              have h₁₁ := partial_eval_preserves_typeof h_wf h_ref h₄
              rw [h₃] at h₁₁
              rw [h₅] at h₁₁
              simp [Residual.typeOf] at h₁₁
              cases h₁₃ : (Map.find? rty attr) <;> rw [h₁₃] at h₆
              . simp at h₆
              rename_i qty
              simp at h₆
              rw [h₁₁] at h₉
              specialize h₉ attr v qty h₁₂ h₁₃
              rw [h₆] at h₉
              exact h₉
        case h_2 r₂ uid ty₂ h₃ =>
          cases h_wt
          case getAttr_entity ety rty h₄ h₅ h₆ h₇ =>
            have ih := partial_eval_preserves_well_typed h_wf h_ref h₅
            rw [h₃] at ih
            cases ih
            rename_i h₇
            cases h₇
            rename_i ety₂ h₈
            cases h₁₂ : m.find? attr
            . simp [someOrError]
              apply Residual.WellTyped.error
            . rename_i v
              simp [someOrError]
              apply Residual.WellTyped.val
              have h₁₁ := partial_eval_preserves_typeof h_wf h_ref h₅
              rw [h₃] at h₁₁
              rw [h₆] at h₁₁
              simp [Residual.typeOf] at h₁₁
              unfold EntitiesRefine at h_eref
              unfold PartialEntities.attrs PartialEntities.get at h₂
              cases h₁₃ : (Map.find? pes uid) <;> rw [h₁₃] at h₂
              . simp at h₂
              . rename_i e
                specialize h_eref uid e h₁₃
                cases h_eref
                . rename_i h₁₄
                  rcases h₁₄ with ⟨h₁₅, h₁₆⟩
                  rw [h₁₅] at h₂
                  simp [PartialEntityData.attrs] at h₂
                  rw [← h₂] at h₁₂
                  simp [Map.empty, Map.find?, Map.kvs, List.find?] at h₁₂
                . rename_i h₁₄
                  rcases h₁₄ with ⟨e₂, h₁₄, h₁₅, h₁₆, h₁₇⟩
                  simp [Option.bind] at h₂
                  rw [h₂] at h₁₅
                  cases h₁₅
                  rename_i h₁₈
                  rw [h₁₈] at h₁₂
                  have h_wf2 := h_wf
                  unfold InstanceOfWellFormedEnvironment at h_wf2
                  rcases h_wf2 with ⟨h₁₉, h₂₀, h₂₁⟩
                  unfold InstanceOfSchema at h₂₁
                  rcases h₂₁ with ⟨h₂₁, h₂₂⟩
                  specialize h₂₁ uid e₂ h₁₄
                  unfold InstanceOfSchemaEntry at h₂₁
                  cases h₂₁
                  . rename_i h₂₃
                    unfold InstanceOfEntitySchemaEntry at h₂₃
                    rcases h₂₃ with ⟨e₃, h₂₃, h₂₄, h₂₅, h₂₆, h₂₇⟩
                    unfold InstanceOfEntityType at h₈
                    rcases h₈ with ⟨h₈, h₂₈⟩
                    rw [← h₈] at h₂₃
                    cases h₂₅
                    rename_i h₂₉ h₃₀ h₃₁
                    specialize h₃₀ attr v
                    simp [EntitySchema.attrs?] at h₄
                    rcases h₄ with ⟨e₄, h₃₂, h₃₃⟩
                    rw [h₁₁] at h₂₃
                    rw [h₂₃] at h₃₂
                    injection h₃₂; rename_i h₃₂
                    rw [← h₃₂] at h₃₃
                    rw [← h₃₃] at h₇
                    cases h₃₄ : (Map.find? e₃.attrs attr)
                    . specialize h₂₉ attr
                      simp [Map.contains] at h₂₉
                      rw [h₁₂] at h₂₉
                      simp at h₂₉
                      rw [h₃₄] at h₂₉
                      simp at h₂₉
                    . rename_i ty₃
                      cases h₃₅ : (Map.find? e₃.attrs.liftBoolTypes attr)
                      . rw [h₃₅] at h₇
                        simp at h₇
                      . have h₃₆ := find_lifted_type h₃₄ h₃₅
                        rename_i v₃
                        rw [h₃₅] at h₇

                        specialize h₃₀ ty₃ h₁₂ h₃₄
                        simp at h₇
                        rw [← h₇]
                        rw [h₃₆]
                        have h₃₇ := type_lifting_preserves_instance_of_type h₃₀
                        cases ty₃
                        all_goals
                          rename_i ty₃
                          simp [Qualified.getType] at h₃₇
                          simp [QualifiedType.liftBoolTypes, Qualified.getType]
                          exact h₃₇
                  . rename_i h₂₃
                    unfold InstanceOfActionSchemaEntry at h₂₃
                    rcases h₂₃ with ⟨e₃, h₂₃, h₂₄, h₂₅⟩
                    rw [e₃] at h₁₂
                    simp [Map.empty, Map.find?, Map.kvs] at h₁₂
          case getAttr_record rty h₄ h₅ h₆ =>
            have h₇ := partial_eval_preserves_typeof h_wf h_ref h₄
            rw [h₃] at h₇
            rw [h₅] at h₇
            simp [Residual.typeOf] at h₇
            have h₈ := partial_eval_preserves_well_typed h_wf h_ref h₄
            rw [h₃] at h₈
            cases h₈
            rename_i h₈
            rw [h₇] at h₈
            cases h₈ -- contradiction
        case h_3 =>
          contradiction
      case h_2 x h₂ =>
        cases h_wt
        case getAttr_entity ety rty h₅ h₆ h₇ h₈ =>
          apply Residual.WellTyped.getAttr_entity
          case h₁ =>
            exact partial_eval_preserves_well_typed h_wf h_ref h₆
          case h₂ =>
            have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₆
            rw [h₁₀]
            rw [h₇]
          case h₃ =>
            rw [h₅]
          case h₄ =>
            exact h₈
        case getAttr_record rty h₆ h₇ h₈ =>
          apply Residual.WellTyped.getAttr_record
          case h₁ =>
            exact partial_eval_preserves_well_typed h_wf h_ref h₆
          case h₂ =>
            have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₆
            rw [h₁₀]
            rw [h₇]
          case h₃ =>
            rw [h₈]
  | hasAttr expr attr ty =>
    simp [TPE.evaluate, TPE.hasAttr, TPE.attrsOf]
    split
    case h_1 =>
      apply Residual.WellTyped.error
    case h_2 r₁ h₁ =>
      split
      case h_1 x m h₂ =>
        apply Residual.WellTyped.val
        apply InstanceOfType.instance_of_bool
        unfold InstanceOfBoolType
        simp
      case h_2 x h₂ =>
        cases h_wt
        case hasAttr_entity ety  h₅ h₆ =>
          apply Residual.WellTyped.hasAttr_entity
          case h₁ =>
            exact partial_eval_preserves_well_typed h_wf h_ref h₅
          case h₂ =>
            have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₅
            rw [h₁₀]
            rw [h₆]
        case hasAttr_record rty h₆ h₇ =>
          apply Residual.WellTyped.hasAttr_record
          case h₁ =>
            exact partial_eval_preserves_well_typed h_wf h_ref h₆
          case h₂ =>
            have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₆
            rw [h₁₀]
            rw [h₇]
  | call xfn args ty =>
    simp [TPE.evaluate, TPE.call]
    simp [List.map₁, List.attach, List.attachWith]
    unfold Function.comp
    simp
    unfold List.unattach
    rw [List.map_pmap_subtype (fun x => x)]
    simp [List.mapM_then_map_combiner]
    rw [List.map_pmap_subtype (fun x => TPE.evaluate x preq pes)]
    split
    case h_1 x xs h₁ =>
      cases h_wt
      rename_i h₂ h₃

      unfold Spec.call
      split
      case h_1 | h_6 | h_7 | h_8 | h_9 | h_10 | h_12 | h_13 | h_16 =>
        rename ExtFun => xf
        rename List Value => vs
        try unfold res
        first
          | unfold Ext.Decimal.decimal
          | unfold Ext.IPAddr.ip
          | unfold Ext.IPAddr.IPNet.isV4
          | unfold Ext.IPAddr.IPNet.isV6
          | unfold Ext.IPAddr.IPNet.isLoopback
          | unfold Ext.IPAddr.IPNet.isMulticast
          | skip

        split
        case h_1 x₂ v =>
          simp [someOrError, Except.toOption]
          apply Residual.WellTyped.val
          rw [List.mapM_some_iff_forall₂, List.forall₂_singleton_right_iff] at h₁
          rcases h₁ with ⟨x₃, h₁, h₅⟩
          unfold Residual.asValue at h₁
          split at h₁
          case h_2 => contradiction
          rename_i x₄ v₂ ty₂ h₆
          have h₇ : x₃ ∈ args := by {
            simp [Membership.mem]
            rw [h₅]
            apply List.Mem.head
          }
          injection h₁ ; rename_i h₁
          specialize h₂ x₃ h₇
          have ih := partial_eval_preserves_well_typed h_wf h_ref h₂
          rw [h₆] at ih
          rw [h₁] at ih
          cases ih ; rename_i ih
          cases ih
          cases h₃
          first
          | apply InstanceOfType.instance_of_ext
            simp [InstanceOfExtType]
          | apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
        case h_2 x₂ h₄ =>
          simp [someOrError, Except.toOption]
          first
          | apply Residual.WellTyped.error
          | apply Residual.WellTyped.val
            cases h₃
            apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
      case h_2 | h_3 | h_4 | h_5 =>
        rename_i xf vs d₁ d₂
        simp [someOrError, Except.toOption]
        cases h₃
        apply Residual.WellTyped.val
        apply InstanceOfType.instance_of_bool
        simp [InstanceOfBoolType]
      case h_11 | h_14 | h_15 =>
        rename ExtFun => xf
        rename List Value => vs
        try unfold res

        first
          | unfold Ext.IPAddr.IPNet.inRange
          | unfold Ext.Datetime.offset
          | skip

        split
        case h_1 x₂ v =>
          simp [someOrError, Except.toOption]
          apply Residual.WellTyped.val
          rw [List.mapM_some_iff_forall₂, List.forall₂_pair_right_iff] at h₁
          rcases h₁ with ⟨x₃, x₄, h₁, h₅, h₆⟩

          unfold Residual.asValue at h₁
          split at h₁
          case h_2 => contradiction
          rename_i x₄ v₂ ty₂ h₇
          have h₈ : x₃ ∈ args := by {
            simp [Membership.mem]
            rw [h₆]
            apply List.Mem.head
          }
          injection h₁ ; rename_i h₁
          specialize h₂ x₃ h₈
          have ih := partial_eval_preserves_well_typed h_wf h_ref h₂
          rw [h₇] at ih
          rw [h₁] at ih
          cases ih ; rename_i ih
          cases ih
          cases h₃
          first
          | apply InstanceOfType.instance_of_ext
            simp [InstanceOfExtType]
          | apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
        case h_2 x₂ h₄ =>
          simp [someOrError, Except.toOption]
          first
          | apply Residual.WellTyped.error
          | apply Residual.WellTyped.val
            cases h₃
            apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
        try case h_3 x₂ v =>
          simp [someOrError, Except.toOption]
          cases h₃
          apply Residual.WellTyped.val
          apply InstanceOfType.instance_of_bool
          simp [InstanceOfBoolType]
      case h_17 | h_18 | h_19 | h_20 | h_21 | h_22 =>
        simp [someOrError, Except.toOption, Ext.Datetime.toTime, Ext.Datetime.Duration.toMilliseconds]
        rw [List.mapM_some_iff_forall₂, List.forall₂_singleton_right_iff] at h₁
        rcases h₁ with ⟨x₃, h₁, h₅⟩
        unfold Residual.asValue at h₁
        split at h₁
        case h_2 => contradiction
        rename_i x₄ v₂ ty₂ h₆
        have h₇ : x₃ ∈ args := by {
          simp [Membership.mem]
          rw [h₅]
          apply List.Mem.head
        }
        injection h₁ ; rename_i h₁
        specialize h₂ x₃ h₇

        have ih := partial_eval_preserves_well_typed h_wf h_ref h₂
        rw [h₆] at ih
        rw [h₁] at ih
        cases ih ; rename_i ih
        cases ih
        cases h₃
        apply Residual.WellTyped.val
        first
        | apply InstanceOfType.instance_of_ext
          simp [InstanceOfExtType]
        | apply InstanceOfType.instance_of_int
      case h_23 =>
        simp [someOrError, Except.toOption]
        apply Residual.WellTyped.error
    case h_2 x h₂ =>
      split
      case isTrue =>
        apply Residual.WellTyped.error
      case isFalse =>
        cases h_wt
        rename_i h₁ h₂
        apply Residual.WellTyped.call
        case call.h₁ =>
          intro r h₃
          have h₄ := List.mem_of_map_implies_exists_unmapped h₃
          rcases h₄ with ⟨r₂, h₄, h₅⟩
          specialize h₁ r₂ h₄
          have ih := partial_eval_preserves_well_typed h_wf h_ref h₁
          rw [h₅]
          exact ih
        case call.h₂ =>
          have h₃ : ∀ x, Residual.WellTyped env x → Residual.WellTyped env ((fun x => TPE.evaluate x preq pes) x) := by {
            intro r h₃
            simp
            exact partial_eval_preserves_well_typed h_wf h_ref h₃
          }
          exact ext_well_typed_after_map h₂ h₃


end Cedar.Thm
