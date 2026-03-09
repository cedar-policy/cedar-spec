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
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

import Cedar.Thm.TPE.WellTyped.Basic

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

theorem tags_if_partial_tags
  {env : TypeEnv} {req : Request} {es : Entities} {pes : PartialEntities}
  {uid : EntityUID} {tags : Map Tag Value}
  (h_wf : InstanceOfWellFormedEnvironment req es env)
  (h_eref : EntitiesRefine es pes)
  (h_tags : PartialEntities.tags pes uid = some tags) :
  ∃ (edata : EntityData),
    edata.tags = tags ∧
    InstanceOfSchemaEntry uid edata env
:= by
  unfold PartialEntities.tags PartialEntities.get at h_tags
  cases h₁ : (Map.find? pes uid) <;> rw [h₁] at h_tags
  . simp at h_tags
  . rename_i pe
    have ⟨edata, h_es, _, _, h_pt, h_entry⟩ :=
      entity_data_from_partial h_wf h_eref h₁
    simp only [Option.bind] at h_tags
    cases h_pe : pe.tags <;> rw [h_pe] at h_tags
    . simp at h_tags
    . simp only [Option.some.injEq] at h_tags
      rw [h_pe] at h_pt
      cases h_pt
      rename_i h_eq
      exact ⟨edata, by rw [← h_tags, h_eq], h_entry⟩

theorem entity_tag_well_typed
  {env : TypeEnv} {req : Request} {es : Entities} {pes : PartialEntities}
  {uid : EntityUID} {ety : EntityType}
  {tags : Map Tag Value} {v : Value} {ty : CedarType} :
  InstanceOfWellFormedEnvironment req es env →
  EntitiesRefine es pes →
  InstanceOfEntityType uid ety env →
  PartialEntities.tags pes uid = some tags →
  v ∈ tags.values →
  env.ets.tags? ety = some (some ty) →
  InstanceOfType env v ty.liftBoolTypes
:= by
  intros h_wf h_eref h_ent h_tags h_mem h_schema
  have ⟨edata, h_eq, h_entry⟩ := tags_if_partial_tags h_wf h_eref h_tags
  rw [← h_eq] at h_mem
  unfold InstanceOfSchemaEntry at h_entry
  cases h_entry
  . rename_i h_ent_entry
    unfold InstanceOfEntitySchemaEntry at h_ent_entry
    rcases h_ent_entry with ⟨entry, h_ets, _, _, _, h_inst_tags⟩
    unfold InstanceOfEntityType at h_ent
    rcases h_ent with ⟨h_ent_ty, _⟩
    rw [← h_ent_ty] at h_ets
    unfold InstanceOfEntityTags at h_inst_tags
    cases h₂ : entry.tags? <;> rw [h₂] at h_inst_tags <;> simp only at h_inst_tags
    . rw [h_inst_tags] at h_mem
      simp [Map.empty, Map.values] at h_mem
    . specialize h_inst_tags v h_mem
      unfold EntitySchema.tags? at h_schema
      rw [h_ets] at h_schema
      simp only [Option.map_some, Option.some.injEq] at h_schema
      rw [h₂] at h_schema
      simp only [Option.some.injEq] at h_schema
      rw [h_schema] at h_inst_tags
      exact type_lifting_preserves_instance_of_type h_inst_tags
  . rename_i h_act_entry
    unfold InstanceOfActionSchemaEntry at h_act_entry
    rcases h_act_entry with ⟨_, h_empty, _⟩
    rw [h_empty] at h_mem
    simp [Map.empty, Map.values] at h_mem

theorem partial_eval_well_typed_app₂_values_hasTag :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  (TPE.evaluate expr1 preq pes).asValue = some (Value.prim (Prim.entityUID id₁)) →
  (TPE.evaluate expr2 preq pes).asValue = some (Value.prim (Prim.string id₂)) →
  PEWellTyped env (Residual.binaryApp BinaryOp.hasTag expr1 expr2 ty)
    (someOrSelf ((TPE.hasTag id1 id2 pes).bind fun a => some (Value.prim (Prim.bool a))) ty
    (Residual.binaryApp BinaryOp.hasTag (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) ty)) req preq es pes
:= by
  unfold PEWellTyped
  intros ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt
  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>

  cases TPE.hasTag id1 id2 pes
  . simp only [someOrSelf, Option.bind_none]
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
            . simp only [Residual.typeOf]
              rename_i ety₂ eq₁ eq₂
              have hᵣ : (ty₁ = CedarType.entity ety₂) := by {
                have h₁₀ := partial_eval_preserves_typeof _ h_expr1
                rw [← h₁₀] at eq₁
                rw [h₃] at eq₁
                simp only [Residual.typeOf] at eq₁
                exact eq₁
              }
              exact hᵣ
            . simp only [Residual.typeOf]
              rename_i ety₂ eq₁ eq₂
              have hᵣ : (ty₂ = CedarType.string) := by {
                have h₁₀ := partial_eval_preserves_typeof _ h_expr2
                rw [← h₁₀] at eq₂
                rw [h₇] at eq₂
                simp [Residual.typeOf] at eq₂

                exact eq₂
              }
              exact hᵣ
      . contradiction
    . contradiction
  . simp only [someOrSelf, Option.bind_some]
    cases h_op
    exact well_typed_bool


theorem partial_eval_well_typed_app₂_values_getTag :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  (TPE.evaluate expr1 preq pes).asValue = some (Value.prim (Prim.entityUID id₁)) →
  (TPE.evaluate expr2 preq pes).asValue = some (Value.prim (Prim.string id₂)) →
  PEWellTyped env (Residual.binaryApp BinaryOp.getTag expr1 expr2 ty) (TPE.getTag id₁ id₂ pes ty) req preq es pes
:= by
  unfold PEWellTyped
  intros ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt
  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>

  unfold TPE.getTag
  split
  . unfold someOrError
    split
    . apply Residual.WellTyped.val
      rename Option (Data.Map Tag Value) => x
      rename_i tags heq x₁ x₂ x₃ v h₃
      cases h_op
      rename_i ety ty h₄ h₅ h₆
      unfold Data.Map.find? at h₃
      split at h₃ <;> try contradiction
      rename_i v₂ v₃ _
      injection h₃; rename_i h₃; rw [← h₃]
      have h_v_mem : v₃ ∈ tags.values := by
        have h₁₉ := List.mem_of_find?_eq_some (by assumption)
        exact Map.in_list_in_values h₁₉
      have h_ent : InstanceOfEntityType id₁ ety env := by
        have h₂₁ := partial_eval_preserves_typeof _ h_expr1 preq pes
        unfold Residual.asValue at h₁
        cases h₂₂: TPE.evaluate expr1 preq pes
        case val v ty₃ =>
          replace h₁ : v = .prim (.entityUID id₁) := by
            simpa [h₂₂] using h₁
          rw [h₁] at h₂₂
          rw [h₂₂] at ih₁
          replace h₂₁ : ty₃ = CedarType.entity ety := by
            rw [h₅, h₂₂] at h₂₁
            simpa [Residual.typeOf] using h₂₁
          cases ih₁; rename_i h₂₃
          rw [h₂₁] at h₂₃
          cases h₂₃; rename_i h₂₄
          exact h₂₄
        all_goals
          rw [h₂₂] at h₁
          simp at h₁
      exact entity_tag_well_typed h_wf h_eref h_ent heq h_v_mem h₄
    . apply Residual.WellTyped.error
  . apply Residual.WellTyped.binaryApp
    . unfold Residual.asValue at h₁
      cases h₃: TPE.evaluate expr1 preq pes
      all_goals (rw [h₃] at h₁
                 simp at h₁)
      rename_i x heq v ty
      rw [h₃] at ih₁
      rw [h₁] at ih₁
      have h_ety_eq : ty = (CedarType.entity id₁.ty) := by {
        have h₄ := partial_eval_preserves_typeof _ h_expr1 preq pes
        cases ih₁
        rename_i h₅
        cases h₅
        rename_i h₅
        unfold InstanceOfEntityType at h₅
        rw [h₅.left]
      }
      rw [h_ety_eq] at ih₁
      exact ih₁
    . apply Residual.WellTyped.val
      apply InstanceOfType.instance_of_string
    . cases h_op with
      | getTag h₃ h₄ h₅ =>
      apply BinaryResidualWellTyped.getTag
      . simp only [Residual.typeOf, CedarType.entity.injEq]
        rfl
      . simp [Residual.typeOf]
      . rename_i ety ty
        have h₄ : ety = id₁.ty := by
          have h₄ := partial_eval_preserves_typeof _ h_expr1 preq pes
          simp only [Residual.asValue] at h₁
          split at h₁
          case h_2 =>
            contradiction
          rename_i x v ty h₅
          rw [h₅] at ih₁
          cases ih₁
          rename_i h₆
          injection h₁ with h₇
          rw [h₇] at h₆
          rw [h₅, h₃, h₇] at h₄
          simp only [Residual.typeOf] at h₄
          cases h₆
          rename_i ety₂ h₈
          injection h₄ with h₄
          unfold InstanceOfEntityType at h₈
          rcases h₈ with ⟨h₉, _⟩
          rw [h₉] at h₄
          rw [h₄]
        rw [h₄] at h₅
        exact h₅


theorem partial_eval_well_typed_app₂_values_mem :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  (TPE.evaluate expr1 preq pes).asValue = .some v₁ →
  (TPE.evaluate expr2 preq pes).asValue = .some v₂ →
  PEWellTyped env (Residual.binaryApp BinaryOp.mem expr1 expr2 ty) (Residual.binaryApp BinaryOp.mem (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) ty) req preq es pes
:= by
  unfold PEWellTyped
  intros ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt
  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>

  unfold Residual.asValue at h₁
  unfold Residual.asValue at h₂
  split at h₁
  case h_1 x v ty₁ h₃ =>
    split at h₂
    case h_1 x₂ v₃ ty₂ h₇ =>
      -- both expr1 and expr2 are values
      injection h₁
      injection h₂
      rename_i h₈ h₉
      subst h₈ h₉
      rw [h₃, h₇]
      rw [h₃] at ih₁
      rw [h₇] at ih₂
      apply Residual.WellTyped.binaryApp
      . apply Residual.WellTyped.val
        cases ih₁
        rename_i h₈
        exact h₈
      . apply Residual.WellTyped.val
        cases ih₂
        rename_i h₈
        exact h₈
      . cases h_op
        . apply BinaryResidualWellTyped.memₑ
          . simp only [Residual.typeOf]
            rename_i ety₁ ety₂ eq₁ eq₂
            have hᵣ : (ty₁ = CedarType.entity ety₁) := by {
              have h₁₀ := partial_eval_preserves_typeof _ h_expr1
              rw [← h₁₀] at eq₁
              rw [h₃] at eq₁
              simp only [Residual.typeOf] at eq₁
              exact eq₁
            }
            exact hᵣ
          . simp only [Residual.typeOf]
            rename_i ety₁ ety₂ eq₁ eq₂
            have hᵣ : (ty₂ = CedarType.entity ety₂) := by {
              have h₁₀ := partial_eval_preserves_typeof _ h_expr2
              rw [← h₁₀] at eq₂
              rw [h₇] at eq₂
              simp only [Residual.typeOf] at eq₂
              exact eq₂
            }
            exact hᵣ
        . apply BinaryResidualWellTyped.memₛ
          . simp only [Residual.typeOf]
            rename_i ety₁ ety₂ eq₁ eq₂
            have hᵣ : (ty₁ = CedarType.entity ety₁) := by {
              have h₁₀ := partial_eval_preserves_typeof _ h_expr1
              rw [← h₁₀] at eq₁
              rw [h₃] at eq₁
              simp only [Residual.typeOf] at eq₁
              exact eq₁
            }
            exact hᵣ
          . simp only [Residual.typeOf]
            rename_i ety₁ ety₂ eq₁ eq₂
            have hᵣ : (ty₂ = (CedarType.entity ety₂).set) := by {
              have h₁₀ := partial_eval_preserves_typeof _ h_expr2
              rw [← h₁₀] at eq₂
              rw [h₇] at eq₂
              simp only [Residual.typeOf] at eq₂
              exact eq₂
            }
            exact hᵣ
    . contradiction
  . contradiction

theorem partial_eval_well_typed_app₂_values :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  (TPE.evaluate expr1 preq pes).asValue = .some v₁ →
  (TPE.evaluate expr2 preq pes).asValue = .some v₂ →
  PEWellTyped env (Residual.binaryApp op expr1 expr2 ty) (TPE.apply₂ op (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) pes ty) req preq es pes
:= by
  unfold PEWellTyped
  intros ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt

  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>

  simp only [TPE.apply₂]
  rw [h₁, h₂]
  simp only
  split

  any_goals
    cases h_op
    all_goals
      exact well_typed_bool
  case h_8 | h_9 | h_10 =>
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind]
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
    rename_i v1 v2 id1 id2
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind]
    split
    case h_1 =>
      simp only [someOrSelf, TPE.apply₂.self]
      apply partial_eval_well_typed_app₂_values_mem ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt₂
    case h_2 =>
      simp only [someOrSelf]
      cases h_op
      all_goals
        exact well_typed_bool
  case h_16 v1 v2 id1 id2 =>
    simp only [Option.pure_def, Option.bind_eq_bind, apply₂.self]
    apply partial_eval_well_typed_app₂_values_hasTag ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt₂
  case h_17 v₁ v₂ id₁ id₂ =>
    apply partial_eval_well_typed_app₂_values_getTag ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt₂
  case h_18 =>
    apply Residual.WellTyped.error

theorem partial_eval_well_typed_app₂_nonvalues :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  (TPE.evaluate expr1 preq pes).asValue = .none ∨ (TPE.evaluate expr2 preq pes).asValue = .none →
  PEWellTyped env (Residual.binaryApp op expr1 expr2 ty) (TPE.apply₂ op (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) pes ty) req preq es pes
:= by
  unfold PEWellTyped
  intros ih₁ ih₂ h₁ h_wf h_ref h_wt

  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>


  simp only [TPE.apply₂]
  split
  case h_1 h₂ h₃ =>
    cases h₁
    case inl h₁ =>
      rw [h₁] at h₂
      contradiction
    case inr h₁ =>
      rw [h₁] at h₃
      contradiction
  case h_2 _ _ =>
    have h₁ := partial_eval_preserves_typeof _ h_expr1
    have h₂ := partial_eval_preserves_typeof _ h_expr2
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
        simp only [TPE.evaluate]
        exact h₆
      case eq_entity =>
        apply BinaryResidualWellTyped.eq_entity
        case h₁ h₉ _ =>
          rw [h₁, h₉]
        case h₂ h₇ h₈ =>
          rw [h₂, h₈]
      case eq h₉ =>
        apply BinaryResidualWellTyped.eq
        rw [h₁, h₂, h₉]
    case mem =>
      cases h_op <;> rename_i ety₁ ety₂ h₅ h₆
      . apply BinaryResidualWellTyped.memₑ
        . rw [h₁, h₅]
        . rw [h₂, h₆]
      . apply BinaryResidualWellTyped.memₛ
        . rw [h₁, h₅]
        . rw [h₂, h₆]
    case hasTag =>
      cases h_op
      apply BinaryResidualWellTyped.hasTag <;> rename_i ety h₅ h₆
      . rw [h₁, h₅]
      . rw [h₂, h₆]
    case getTag =>
      cases h_op ; rename_i ty h₅ h₆
      apply BinaryResidualWellTyped.getTag
      . rw [h₁, h₅]
      . rw [h₂, h₆]
      . rw [ty]
    case less =>
      cases h_op <;> rename_i h₃ h₄
      case less_int =>
        apply BinaryResidualWellTyped.less_int
        . rw [h₁, h₃]
        . rw [h₂, h₄]
      case less_datetime =>
        apply BinaryResidualWellTyped.less_datetime
        . rw [h₁, h₃]
        . rw [h₂, h₄]
      case less_duration =>
        apply BinaryResidualWellTyped.less_duration
        . rw [h₁, h₃]
        . rw [h₂, h₄]
    case lessEq =>
      cases h_op <;> rename_i h₃ h₄
      case lessEq_int =>
        apply BinaryResidualWellTyped.lessEq_int
        . rw [h₁, h₃]
        . rw [h₂, h₄]
      case lessEq_datetime =>
        apply BinaryResidualWellTyped.lessEq_datetime
        . rw [h₁, h₃]
        . rw [h₂, h₄]
      case lessEq_duration =>
        apply BinaryResidualWellTyped.lessEq_duration
        . rw [h₁, h₃]
        . rw [h₂, h₄]
    case mul | sub | add =>
      cases h_op; rename_i h₃ h₄
      first
      | apply BinaryResidualWellTyped.mul
      | apply BinaryResidualWellTyped.sub
      | apply BinaryResidualWellTyped.add
      . rw [h₁, h₃]
      . rw [h₂, h₄]
    case contains =>
      cases h_op; rename_i h₃
      apply BinaryResidualWellTyped.contains
      rw [h₁, h₂]
      exact h₃
    case containsAll | containsAny =>
      cases h_op; rename_i ty h₃ h₄
      first
      | apply BinaryResidualWellTyped.containsAll
      | apply BinaryResidualWellTyped.containsAny
      rw [h₁, h₃]
      rw [h₂, h₄]



theorem partial_eval_well_typed_app₂ :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  PEWellTyped env (Residual.binaryApp op expr1 expr2 ty) (TPE.apply₂ op (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) pes ty) req preq es pes
:= by
  intro ih₁ ih₂ h₁
  cases h₂ : (TPE.evaluate expr1 preq pes).asValue
  case none =>
    apply partial_eval_well_typed_app₂_nonvalues ih₁ ih₂
    . left
      exact h₂
    . exact h₁
  case some v₁ =>
    cases h₃ : (TPE.evaluate expr2 preq pes).asValue
    case none =>
      apply partial_eval_well_typed_app₂_nonvalues ih₁ ih₂
      . right
        exact h₃
      . exact h₁
    case some v₂ =>
      apply partial_eval_well_typed_app₂_values ih₁ ih₂ h₂ h₃
      . exact h₁
