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

/-- Convert an entity chain to a record chain given the entity's schema record type. -/
private theorem entity_chain_to_record_chain
  {ets : EntitySchema} {ety : EntityType} {rty : RecordType} {attrs : List Attr}
  (h_schema : ets.attrs? ety = .some rty)
  (h_chain : ExtHasAttrChainValid ets (.entity ety) attrs) :
  ExtHasAttrChainValid ets (.record rty) attrs := by
  cases h_chain with
  | last => exact .last
  | cons_entity h₁ h₂ h₃ h₄ =>
    have h_eq : rty = _ := Option.some.inj (h_schema ▸ h₁)
    subst h_eq; exact .cons_entity_from_record h₂ h₃ h₄
  | cons_record_from_entity h₁ h₂ h₃ h₄ =>
    have h_eq : rty = _ := Option.some.inj (h_schema ▸ h₁)
    subst h_eq; exact .cons_record_from_record h₂ h₃ h₄
  | cons_not_in_schema_entity h₁ =>
    cases h₁ with
    | inl h_none => exact absurd (h_schema ▸ h_none) (by simp)
    | inr h_all_none => exact .cons_not_in_record (h_all_none rty h_schema)

/-- The extHasAttr TPE loop produces a well-typed residual when given
    chain validity from a record type and InstanceOfType for the map.
-/
private theorem extHasAttr_loop_well_typed
  {env : TypeEnv} {attrs : List Attr}
  {pes : PartialEntities}
  {m : Map Attr Value}
  {req : Request} {es : Entities} {preq : PartialRequest}
  {rty : RecordType}
  (hwf : InstanceOfWellFormedEnvironment req es env)
  (href : RequestAndEntitiesRefine req es preq pes)
  (h_inst : InstanceOfType env (.record m) (.record rty))
  (h_chain : ExtHasAttrChainValid env.ets (.record rty) attrs) :
  Residual.WellTyped env (TPE.extHasAttr.loop m attrs pes (.bool .anyBool)) := by
  induction attrs generalizing m rty with
  | nil =>
    unfold TPE.extHasAttr.loop
    exact well_typed_bool
  | cons a rest ih =>
    unfold TPE.extHasAttr.loop
    cases rest with
    | nil => exact well_typed_bool
    | cons b rest' =>
      simp only
      cases h_chain with
      | cons_entity_from_record h₁ h₂ h₃ =>
        cases h_find : m.find? a with
        | none => exact well_typed_bool
        | some next =>
          have h_next_inst := instance_of_attribute_type h_inst h₁ h₂ h_find
          have ⟨uid, h_uid_ty, h_next_val⟩ := instance_of_entity_type_is_entity h_next_inst
          subst h_next_val
          simp only [TPE.attrsOf, PartialEntities.attrs, PartialEntities.get]
          subst h_uid_ty
          cases h_pes_find : pes.find? uid with
          | none =>
            simp [Option.bind]
            exact Residual.WellTyped.extHasAttr_entity
              (Residual.WellTyped.val h_next_inst)
              (by simp [Residual.typeOf])
              h₃
          | some pedata =>
            simp only [Option.bind]
            cases h_pe_attrs : pedata.attrs with
            | none =>
              simp only
              exact Residual.WellTyped.extHasAttr_entity
                (Residual.WellTyped.val h_next_inst)
                (by simp [Residual.typeOf])
                h₃
            | some m' =>
              simp only
              have ⟨edata, h_es_find, h_attrs_ref, _, _, _⟩ :=
                entity_data_from_partial hwf href.2 h_pes_find
              simp only [h_pe_attrs, PartialIsValid.some_inv] at h_attrs_ref
              subst h_attrs_ref
              -- h₃ : ExtHasAttrChainValid (.entity uid.ty) (b :: rest')
              -- Need schema for uid.ty and convert to record chain
              cases h₃ with
              | last =>
                unfold TPE.extHasAttr.loop; exact well_typed_bool
              | cons_entity h₃₁ h₃₂ h₃₃ h₃₄ =>
                have h_inst' := well_typed_entity_attributes hwf h_es_find h₃₁
                exact ih h_inst'
                  (entity_chain_to_record_chain h₃₁ (.cons_entity h₃₁ h₃₂ h₃₃ h₃₄))
              | cons_record_from_entity h₃₁ h₃₂ h₃₃ h₃₄ =>
                have h_inst' := well_typed_entity_attributes hwf h_es_find h₃₁
                exact ih h_inst'
                  (entity_chain_to_record_chain h₃₁ (.cons_record_from_entity h₃₁ h₃₂ h₃₃ h₃₄))
              | cons_not_in_schema_entity h₃₁ =>
                -- Entity not in schema or attr b not found → loop returns false
                have ⟨_, _, h_schema⟩ := hwf
                have h_entry := h_schema.1 uid edata h_es_find
                cases h₃₁ with
                | inl h_none =>
                  cases h_entry with
                  | inl h =>
                    obtain ⟨entry, h_entry_find, _, _, _, _⟩ := h
                    simp [EntitySchema.attrs?] at h_none
                    rw [h_entry_find] at h_none; simp at h_none
                  | inr h =>
                    obtain ⟨h_empty, _, _, _, _⟩ := h
                    rw [h_empty]
                    unfold TPE.extHasAttr.loop
                    cases rest' with
                    | nil => exact well_typed_bool
                    | cons => simp [Map.empty, Map.find?]; exact well_typed_bool
                | inr h_all_none =>
                  cases h_entry with
                  | inl h =>
                    obtain ⟨entry, h_entry_find, _, _, _, _⟩ := h
                    have h_schema_attrs : env.ets.attrs? uid.ty = .some entry.attrs := by
                      simp [EntitySchema.attrs?]; exact ⟨entry, h_entry_find, rfl⟩
                    have h_attr_none := h_all_none entry.attrs h_schema_attrs
                    have h_inst' := well_typed_entity_attributes hwf h_es_find h_schema_attrs
                    have h_abs := absent_attribute_is_absent h_inst' h_attr_none
                    unfold TPE.extHasAttr.loop
                    cases rest' with
                    | nil => exact well_typed_bool
                    | cons => simp [h_abs]; exact well_typed_bool
                  | inr h =>
                    obtain ⟨h_empty, _, _, _, _⟩ := h
                    rw [h_empty]
                    unfold TPE.extHasAttr.loop
                    cases rest' with
                    | nil => exact well_typed_bool
                    | cons => simp [Map.empty, Map.find?]; exact well_typed_bool
      | cons_record_from_record h₁ h₂ h₃ =>
        cases h_find : m.find? a with
        | none => exact well_typed_bool
        | some next =>
          have h_next_inst := instance_of_attribute_type h_inst h₁ h₂ h_find
          have ⟨r, h_next_val⟩ := instance_of_record_type_is_record h_next_inst
          subst h_next_val
          simp only [TPE.attrsOf]
          exact ih h_next_inst h₃
      | cons_not_in_record h₁ =>
        have h_abs := absent_attribute_is_absent h_inst h₁
        simp only [h_abs]
        exact well_typed_bool

theorem partial_eval_well_typed_extHasAttr {env : TypeEnv} {expr : Residual} {attr : Attr} {attrs : List Attr} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate expr preq pes) →
  PEWellTyped env (Residual.extHasAttr expr attr attrs ty) (TPE.evaluate (Residual.extHasAttr expr attr attrs ty) preq pes) req preq es pes
:= by
  intros h₁ hwf href h₂
  simp only [TPE.evaluate, TPE.extHasAttr]
  split
  case h_1 =>
    apply Residual.WellTyped.error
  case h_2 r₁ _ =>
    split
    case h_1 x m heq =>
      have hty : ty = .bool .anyBool := by cases h₂ <;> simp
      subst hty
      cases h₂ with
      | extHasAttr_entity h₅ h₆ h₇ =>
        rename_i ety
        have h_typeof : (TPE.evaluate expr preq pes).typeOf = .entity ety := by
          rw [partial_eval_preserves_typeof _ h₅ preq pes, h₆]
        -- Analyze attrsOf
        simp [TPE.attrsOf] at heq
        split at heq
        case h_1 m_rec ty_r heq₁ =>
          simp [Option.some.injEq] at heq; subst heq
          simp only [heq₁, Residual.typeOf] at h_typeof
          -- h_typeof : ty_r = .entity ety
          -- h₁ : WellTyped env (TPE.evaluate expr preq pes)
          rw [heq₁] at h₁
          -- Now h₁ : WellTyped env (.val (.record m_rec) ty_r)
          subst h_typeof
          -- h₁ : WellTyped env (.val (.record m_rec) (.entity ety))
          rcases h₁ with ⟨h_inst⟩
          nomatch h_inst
        case h_2 uid ty_u heq₁ =>
          -- entity case: m from pes.attrs uid
          simp [heq₁, Residual.typeOf] at h_typeof
          -- h_typeof : ty_u = .entity ety
          subst h_typeof
          -- Get ety = uid.ty from InstanceOfEntityType
          rw [heq₁] at h₁
          rcases h₁ with ⟨h_inst_uid⟩
          -- h_inst_uid : InstanceOfType env (.prim (.entityUID uid)) (.entity ety)
          -- Extract ety = uid.ty
          have h_ety_eq : ety = uid.ty := by
            cases h_inst_uid
            rename_i h_ioe
            exact h_ioe.1
          subst h_ety_eq
          simp [PartialEntities.attrs, PartialEntities.get, Option.bind_eq_some_iff] at heq
          rcases heq with ⟨pedata, h_pes_find, h_pe_attrs⟩
          have ⟨edata, h_es_find, h_attrs_ref, _, _, _⟩ :=
            entity_data_from_partial hwf href.2 h_pes_find
          simp only [h_pe_attrs, PartialIsValid.some_inv] at h_attrs_ref
          subst h_attrs_ref
          -- m = edata.attrs, h₇ : chain from (.entity uid.ty) (attr :: attrs)
          cases h₇ with
          | last => unfold TPE.extHasAttr.loop; exact well_typed_bool
          | cons_entity h₇₁ h₇₂ h₇₃ h₇₄ =>
            exact extHasAttr_loop_well_typed hwf href
              (well_typed_entity_attributes hwf h_es_find h₇₁)
              (entity_chain_to_record_chain h₇₁ (.cons_entity h₇₁ h₇₂ h₇₃ h₇₄))
          | cons_record_from_entity h₇₁ h₇₂ h₇₃ h₇₄ =>
            exact extHasAttr_loop_well_typed hwf href
              (well_typed_entity_attributes hwf h_es_find h₇₁)
              (entity_chain_to_record_chain h₇₁ (.cons_record_from_entity h₇₁ h₇₂ h₇₃ h₇₄))
          | cons_not_in_schema_entity h₇₁ =>
            have ⟨_, _, h_schema_wf⟩ := hwf
            have h_entry := h_schema_wf.1 uid edata h_es_find
            cases h₇₁ with
            | inl h_none =>
              cases h_entry with
              | inl h =>
                obtain ⟨entry, h_entry_find, _, _, _, _⟩ := h
                simp [EntitySchema.attrs?] at h_none; rw [h_entry_find] at h_none; simp at h_none
              | inr h =>
                obtain ⟨h_empty, _, _, _, _⟩ := h; rw [h_empty]
                unfold TPE.extHasAttr.loop
                cases attrs with
                | nil => exact well_typed_bool
                | cons => simp [Map.empty, Map.find?]; exact well_typed_bool
            | inr h_all_none =>
              cases h_entry with
              | inl h =>
                obtain ⟨entry, h_entry_find, _, _, _, _⟩ := h
                have h_sa : env.ets.attrs? uid.ty = .some entry.attrs := by
                  simp [EntitySchema.attrs?]; exact ⟨entry, h_entry_find, rfl⟩
                have h_abs := absent_attribute_is_absent
                  (well_typed_entity_attributes hwf h_es_find h_sa)
                  (h_all_none entry.attrs h_sa)
                unfold TPE.extHasAttr.loop
                cases attrs with
                | nil => exact well_typed_bool
                | cons => simp [h_abs]; exact well_typed_bool
              | inr h =>
                obtain ⟨h_empty, _, _, _, _⟩ := h; rw [h_empty]
                unfold TPE.extHasAttr.loop
                cases attrs with
                  | nil => exact well_typed_bool
                  | cons => simp [Map.empty, Map.find?]; exact well_typed_bool
        case h_3 => simp at heq
      | extHasAttr_record h₅ h₆ h₇ =>
        rename_i rty
        have h_typeof : (TPE.evaluate expr preq pes).typeOf = .record rty := by
          rw [partial_eval_preserves_typeof _ h₅ preq pes, h₆]
        simp [TPE.attrsOf] at heq
        split at heq
        case h_1 m_rec ty_r heq₁ =>
          simp [Option.some.injEq] at heq; subst heq
          simp [heq₁, Residual.typeOf] at h_typeof
          subst h_typeof
          rw [heq₁] at h₁
          rcases h₁ with ⟨h_inst⟩
          exact extHasAttr_loop_well_typed hwf href h_inst h₇
        case h_2 uid ty_u heq₁ =>
          -- entity UID but typeOf = .record → absurd
          simp [heq₁, Residual.typeOf] at h_typeof
          subst h_typeof
          rw [heq₁] at h₁
          rcases h₁ with ⟨h_inst⟩
          nomatch h_inst
        case h_3 => simp at heq
    case h_2 x _ =>
      cases h₂ with
      | extHasAttr_entity h₅ h₆ h₇ =>
        apply Residual.WellTyped.extHasAttr_entity
        · exact h₁
        · have h₁₀ := partial_eval_preserves_typeof _ h₅
          rw [h₁₀, h₆]
        · exact h₇
      | extHasAttr_record h₅ h₆ h₇ =>
        apply Residual.WellTyped.extHasAttr_record
        · exact h₁
        · have h₁₀ := partial_eval_preserves_typeof _ h₅
          rw [h₁₀, h₆]
        · exact h₇

end Cedar.Thm
