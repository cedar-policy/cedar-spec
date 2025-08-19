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
import Cedar.Thm.TPE.PreservesTypeOf
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




theorem partial_eval_well_typed_app₂ :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  PEWellTyped env (Residual.binaryApp op expr1 expr2 ty) (TPE.apply₂ op (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) pes ty) req preq es pes := by
  unfold PEWellTyped
  intros ih₁ ih₂ h_wf h_ref h_wt
  unfold TPE.apply₂

  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>

  split
  case h_1 =>
    simp
    split
    any_goals
      apply Residual.WellTyped.val
      cases h_op
      all_goals
        apply InstanceOfType.instance_of_bool
        unfold InstanceOfBoolType
        split <;> try simp
        contradiction
    case h_8 | h_9 | h_10 =>
      simp only [Option.bind]
      split
      case h_1 =>
       apply Residual.WellTyped.error
      case h_2 =>
        apply Residual.WellTyped.val
        cases h_op
        all_goals {
          apply InstanceOfType.instance_of_int
        }
    -- mem and mem set
    case h_14 | h_15 =>
      rename_i v1 v2 id1 id2 h₁ h₂
      simp [Option.bind]
      split
      case h_1 =>
        simp only [someOrSelf, TPE.apply₂.self]
        unfold Residual.asValue at h₁
        unfold Residual.asValue at h₂
        split at h₁
        case h_1 x v ty₁ h₃ =>
          split at h₂
          case h_1  h₄ h₅ ty₂ h₇ =>
            -- both expr1 and expr2 are values
            injection h₁
            injection h₂
            rename_i h₈ h₉
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
      case h_2 =>
        simp only [someOrSelf]
        apply Residual.WellTyped.val
        cases h_op
        all_goals
          apply InstanceOfType.instance_of_bool
          simp [InstanceOfBoolType]

    case h_16 v1 v2 id1 id2 h₁ h₂ =>
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
          let h_wf₂ := h_wf
          unfold InstanceOfWellFormedEnvironment at h_wf₂
          rcases h_wf₂ with ⟨h₁₄, ⟨h₁₅, h₁₆⟩⟩
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
                have h₂₁ := partial_eval_preserves_typeof h_wf h_ref h_expr1
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
                have h₄ := partial_eval_preserves_typeof h_wf h_ref h_expr1
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
              have h₄ := partial_eval_preserves_typeof h_wf h_ref h_expr1
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
  case h_2 x₁ x₂ =>
    let h₁ := partial_eval_preserves_typeof h_wf h_ref h_expr1
    have h₂ := partial_eval_preserves_typeof h_wf h_ref h_expr2
    split
    case h_1 =>
      apply Residual.WellTyped.error
    case h_2 =>
      apply Residual.WellTyped.error

    case h_3 =>
    rename_i h₁ r₁ r₂ h₃ h₄
    unfold apply₂.self
    apply Residual.WellTyped.binaryApp
    cases op
    any_goals (exact ih₁)
    any_goals (exact ih₂)
    case h₃ =>
    cases op
    case eq =>
      cases h₅: h_op
      case eq_val =>
        cases h_wt₂
        rename_i h₆
        simp [TPE.evaluate]
        exact h₆
      case eq_entity =>
        apply BinaryResidualWellTyped.eq_entity
        . rw [h₁]
          rename_i h₉ _
          rw [h₉]
        . rw [h₂]
          rename_i h₇ h₈
          rw [h₈]
      case eq =>
        apply BinaryResidualWellTyped.eq
        rename_i h₉
        rw [h₁]
        rw [h₂]
        rw [h₉]
    case mem =>
      cases h_op <;> rename_i ety₁ ety₂ h₅ h₆
      . apply BinaryResidualWellTyped.memₑ
        . rw [h₁]
          rw [h₅]
        . rw [h₂]
          rw [h₆]
      . apply BinaryResidualWellTyped.memₛ
        . rw [h₁]
          rw [h₅]
        . rw [h₂]
          rw [h₆]
    case hasTag =>
      cases h_op
      apply BinaryResidualWellTyped.hasTag <;> rename_i ety h₅ h₆
      . rw [h₁]
        rw [h₅]
        congr
        have h₈ : ety = ety := by simp
        exact h₈
      . rw [h₂]
        rw [h₆]
    case getTag =>
      cases h_op ; rename_i ty h₅ h₆
      apply BinaryResidualWellTyped.getTag
      . rw [h₁]
        rw [h₅]
      . rw [h₂]
        rw [h₆]
      . rw [ty]
    case less =>
      cases h_op <;> rename_i h₃ h₄
      case less_int =>
        apply BinaryResidualWellTyped.less_int
        . rw [h₁]
          rw [h₃]
        . rw [h₂]
          rw [h₄]
      case less_datetime =>
        apply BinaryResidualWellTyped.less_datetime
        . rw [h₁]
          rw [h₃]
        . rw [h₂]
          rw [h₄]
      case less_duration =>
        apply BinaryResidualWellTyped.less_duration
        . rw [h₁]
          rw [h₃]
        . rw [h₂]
          rw [h₄]
    case lessEq =>
      cases h_op <;> rename_i h₃ h₄
      case lessEq_int =>
        apply BinaryResidualWellTyped.lessEq_int
        . rw [h₁]
          rw [h₃]
        . rw [h₂]
          rw [h₄]
      case lessEq_datetime =>
        apply BinaryResidualWellTyped.lessEq_datetime
        . rw [h₁]
          rw [h₃]
        . rw [h₂]
          rw [h₄]
      case lessEq_duration =>
        apply BinaryResidualWellTyped.lessEq_duration
        . rw [h₁]
          rw [h₃]
        . rw [h₂]
          rw [h₄]
    case mul | sub | add =>
      cases h_op <;> rename_i h₃ h₄
      first
      | apply BinaryResidualWellTyped.mul
      | apply BinaryResidualWellTyped.sub
      | apply BinaryResidualWellTyped.add
      . rw [h₁]
        rw [h₃]
      . rw [h₂]
        rw [h₄]
    case contains =>
      cases h_op <;> rename_i h₃
      apply BinaryResidualWellTyped.contains
      rw [h₁]
      rw [h₂]
      exact h₃
    case containsAll | containsAny =>
      cases h_op <;> rename_i ty h₃ h₄
      first
      | apply BinaryResidualWellTyped.containsAll
      | apply BinaryResidualWellTyped.containsAny
      rw [h₁]
      rw [h₃]
      rw [h₂]
      rw [h₄]
