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

theorem find_lifted_type {attr ty₁ ty₂} {m: RecordType} :
  Map.find? m attr = some ty₁ →
  Map.find? m.liftBoolTypes attr = some ty₂ →
  ty₂ = ty₁.liftBoolTypes
:= by
  simp only [Map.find?]
  intro h₁ h₂
  cases h₃: m.toList
  case nil =>
    rw [h₃] at h₁
    simp at h₁
  case cons hd tl =>
    rw [h₃] at h₁
    rw [lift_bool_types_record_eq_map_on_values, Data.Map.mapOnValues] at h₂
    simp only [h₃, List.map_cons, Map.toList_mk_id] at h₂
    cases h₄ : hd.fst == attr <;> simp only [List.find?, h₄] at h₁ h₂
    case false =>
      have h₂' : Map.find? (RecordType.liftBoolTypes (Map.mk tl)) attr = some ty₂ := by
        simp only [lift_bool_types_record_eq_map_on_values, Data.Map.mapOnValues, Map.find?]
        exact h₂
      exact find_lifted_type h₁ h₂'
    case true =>
      simp only [Option.some.injEq] at h₁ h₂
      rw [← h₂, h₁]
decreasing_by
  rename_i hd tail _ _
  have h₈: sizeOf (Map.mk tail) < sizeOf m := by {
    simp only [sizeOf, Map._sizeOf_1, Nat.add_lt_add_iff_left]
    have h₉ : m.1 = hd :: tail := h₃
    rw [h₉]
    simp only [List._sizeOf_1, Nat.lt_add_left_iff_pos, gt_iff_lt]
    omega
  }
  exact h₈

theorem partial_eval_well_typed_getAttr {env : TypeEnv} {expr : Residual} {attr : Attr} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate expr preq pes) →
  PEWellTyped env (Residual.getAttr expr attr ty) (TPE.evaluate (Residual.getAttr expr attr ty) preq pes) req preq es pes
:= by
  intros h_expr_wt h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.getAttr, TPE.attrsOf]
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
          have ih := h_expr_wt
          rw [h₃] at ih
          cases ih
          rename_i h_wt_val
          cases h_wt_val
          rename_i rty₂ h₈ h₉ _
          cases h₁₂ : m.find? attr
          . simp only [someOrError]
            apply Residual.WellTyped.error
          . simp only [someOrError]
            apply Residual.WellTyped.val
            have h₁₁ := partial_eval_preserves_typeof _ h₅ preq pes
            rw [h₃, h₆] at h₁₁
            simp [Residual.typeOf] at h₁₁
        case getAttr_record rty h₄ h₅ h₆ =>
          have ih := h_expr_wt
          rw [h₃] at ih
          cases ih
          rename_i h_wt_rec
          cases h_wt_rec
          rename_i rty₂ h₈ h₉ _
          cases h₁₂ : m.find? attr
          . simp only [someOrError]
            apply Residual.WellTyped.error
          . rename_i v
            simp only [someOrError]
            apply Residual.WellTyped.val
            have h₁₁ := partial_eval_preserves_typeof _ h₄ preq pes
            rw [h₃] at h₁₁
            rw [h₅] at h₁₁
            simp only [Residual.typeOf, CedarType.record.injEq] at h₁₁
            cases h₁₃ : (Map.find? rty attr) <;> rw [h₁₃] at h₆
            . simp only [Option.map_none, reduceCtorEq] at h₆
            rename_i qty
            simp only [Option.map_some, Option.some.injEq] at h₆
            rw [h₁₁] at h₉
            specialize h₉ attr v qty h₁₂ h₁₃
            rw [h₆] at h₉
            exact h₉
      case h_2 r₂ uid ty₂ h₃ =>
        cases h_wt
        case getAttr_entity ety rty h₄ h₅ h₆ h₇ =>
          have ih := h_expr_wt
          rw [h₃] at ih
          cases ih
          rename_i h_wt_ent
          cases h_wt_ent
          rename_i ety₂ h₈
          cases h₁₂ : m.find? attr
          . simp only [someOrError]
            apply Residual.WellTyped.error
          . rename_i v
            simp only [someOrError]
            apply Residual.WellTyped.val
            have h₁₁ := partial_eval_preserves_typeof _ h₅ preq pes
            rw [h₃, h₆] at h₁₁
            simp only [Residual.typeOf, CedarType.entity.injEq] at h₁₁
            unfold RequestAndEntitiesRefine at h_ref
            rcases h_ref with ⟨h_rref, h_eref⟩
            unfold EntitiesRefine at h_eref
            unfold PartialEntities.attrs PartialEntities.get at h₂
            cases h₁₃ : (Map.find? pes uid) <;> rw [h₁₃] at h₂
            . simp at h₂
            . rename_i e
              specialize h_eref uid e h₁₃
              cases h_eref
              . rename_i h₁₄
                rcases h₁₄ with ⟨h₁₄, h₁₅, _, h₁₇⟩
                simp only [Option.bind] at h₂
                rw [h₂] at h₁₅
                cases h₁₅
                rename_i h₁₈
                rw [h₁₈] at h₁₂
                have h_wf2 := h_wf
                unfold InstanceOfWellFormedEnvironment at h_wf2
                rcases h_wf2 with ⟨h₁₉, _, h₂₁⟩
                unfold InstanceOfSchema at h₂₁
                rcases h₂₁ with ⟨h₂₁, h₂₂⟩
                rename EntityData => e₂
                specialize h₂₁ uid e₂ h₁₄
                unfold InstanceOfSchemaEntry at h₂₁
                cases h₂₁
                . rename_i h₂₃
                  unfold InstanceOfEntitySchemaEntry at h₂₃
                  rcases h₂₃ with ⟨e₃, h₂₃, _, h₂₅, _, _⟩
                  unfold InstanceOfEntityType at h₈
                  rcases h₈ with ⟨h₈, _⟩
                  rw [← h₈] at h₂₃
                  cases h₂₅
                  rename_i h₂₉ h₃₀ h₃₁
                  specialize h₃₀ attr v
                  simp only [EntitySchema.attrs?, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h₄
                  rcases h₄ with ⟨e₄, h₃₂, h₃₃⟩
                  rw [h₁₁] at h₂₃
                  rw [h₂₃] at h₃₂
                  injection h₃₂; rename_i h₃₂
                  rw [← h₃₂] at h₃₃
                  rw [← h₃₃] at h₇
                  cases h₃₄ : (Map.find? e₃.attrs attr)
                  . specialize h₂₉ attr
                    simp only [Map.contains] at h₂₉
                    rw [h₁₂] at h₂₉
                    simp only [Option.isSome_some, forall_const] at h₂₉
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
                      simp only [Option.map_some, Option.some.injEq] at h₇
                      rw [← h₇]
                      rw [h₃₆]
                      have h₃₇ := type_lifting_preserves_instance_of_type h₃₀
                      cases ty₃
                      all_goals
                        rename_i ty₃
                        simp only [Qualified.getType] at h₃₇
                        simp only [Qualified.getType, QualifiedType.liftBoolTypes]
                        exact h₃₇
                . rename_i h₂₃
                  unfold InstanceOfActionSchemaEntry at h₂₃
                  rcases h₂₃ with ⟨e₃, h₂₃, _, _⟩
                  rw [e₃] at h₁₂
                  simp [Map.empty, Map.find?] at h₁₂
        case getAttr_record rty h₄ h₅ h₆ =>
          have h₇ := partial_eval_preserves_typeof _ h₄ preq pes
          rw [h₃] at h₇
          rw [h₅] at h₇
          simp only [Residual.typeOf] at h₇
          have h₈ := h_expr_wt
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
          exact h_expr_wt
        case h₂ =>
          have h₈ := partial_eval_preserves_typeof _ h₆
          rw [h₈]
          rw [h₇]
        case h₃ =>
          rw [h₅]
        case h₄ =>
          exact h₈
      case getAttr_record rty h₆ h₇ h₈ =>
        apply Residual.WellTyped.getAttr_record
        case h₁ =>
          exact h_expr_wt
        case h₂ =>
          have h₁₀ := partial_eval_preserves_typeof _ h₆
          rw [h₁₀, h₇]
        case h₃ =>
          rw [h₈]
