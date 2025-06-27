import Cedar.Thm.SymCC.Env.WF

/-!
This file contains some facts about `SymEnv.ofEnv`.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open SymCC

/--
If some entity exists in `Γ`, then it must
also exists in `SymEnv.ofEnv Γ` with the corresponding `SymEntityData`
-/
theorem ofEnv_preserves_entity
  {Γ : Environment} {εnv : SymEnv} {ety : EntityType} {entry : EntitySchemaEntry}
  (hεnv : εnv = SymEnv.ofEnv Γ)
  (hfound : Data.Map.find? Γ.ets ety = some entry) :
  Data.Map.find? εnv.entities ety = some (SymEntityData.ofEntityType ety entry)
:= by
  simp [hεnv, Data.Map.find?, SymEnv.ofEnv, SymEntities.ofSchema, Data.Map.toList]
  simp [Data.Map.find?] at hfound
  -- Simplify hfound
  split at hfound
  case _ _ _ hfound2 =>
    simp only [Option.some.injEq] at hfound
    simp only [hfound] at hfound2
    have hfound := hfound2
    have h := List.find?_some hfound
    simp only [beq_iff_eq] at h
    simp only [h] at hfound
    apply Data.Map.find?_implies_make_find?
    apply List.find?_implies_append_find?
    apply List.find?_implies_find?_fst_map
    assumption
  case _ => contradiction

/--
Lemma that if a concrete `Γ : Environment` has tags for
a particular entity type, then `SymEnv.ofEnv Γ` must also
have tags for it
-/
theorem ofEnv_preserves_tags
  {Γ : Environment} {ety : EntityType} {ty : CedarType}
  (h : Γ.ets.tags? ety = some (some ty)) :
  ∃ τags : SymTags,
    (SymEnv.ofEnv Γ).entities.tags ety = some (some τags) ∧
    τags.vals.outType = TermType.ofType ty
:= by
  simp only [EntitySchema.tags?, Option.map_eq_some_iff] at h
  have ⟨found_entry, ⟨hfound, hty_entry⟩⟩ := h
  -- The corresponding entity exists in `εnv`
  have hety_exists :
    Data.Map.find? (SymEnv.ofEnv Γ).entities ety
    = some (SymEntityData.ofEntityType ety found_entry)
  := by
    apply ofEnv_preserves_entity ?_ hfound
    rfl
  simp only [
    hety_exists,
    SymEntities.tags, SymEntityData.ofEntityType,
    SymEntityData.ofStandardEntityType,
    SymEntityData.ofEnumEntityType,
    Option.map_some, Option.some.injEq,
  ]
  split <;> simp only [Option.eq_some_iff_get_eq, reduceCtorEq, false_and, exists_const]
  case h_1 std_entry =>
    simp only [EntitySchemaEntry.tags?] at hty_entry
    simp [hty_entry, SymEntityData.ofStandardEntityType.symTags, UnaryFunction.outType]
  case h_2 enum_entry =>
    contradiction

/--
Show that `SymEnv.ofEnv Γ` preserves the result of attribute lookup
-/
theorem ofEnv_preserves_entity_attr
  {Γ : Environment} {εnv : SymEnv}
  {rty : RecordType} {ety : EntityType}
  (hεnv : εnv = SymEnv.ofEnv Γ)
  (hattrs_exists : Γ.ets.attrs? ety = some rty)
  (hwf : εnv.WellFormed) :
  ∃ attrs : UnaryFunction,
    εnv.entities.attrs ety = .some attrs ∧
    UnaryFunction.WellFormed εnv.entities attrs ∧
    attrs.argType = .entity ety ∧
    attrs.outType = .record (Data.Map.mk (TermType.ofRecordType rty.1))
:= by
  simp only [EntitySchema.attrs?, Data.Map.find?, Option.map_eq_some_iff] at hattrs_exists
  split at hattrs_exists
  case h_1 found_ety found_entry hfound =>
    simp only [Option.some.injEq, exists_eq_left'] at hattrs_exists
    -- The corresponding entity exists in `εnv`
    have hety_exists :
      Data.Map.find? εnv.entities ety
      = some (SymEntityData.ofEntityType ety found_entry)
    := by
      apply ofEnv_preserves_entity hεnv
      simp [Data.Map.find?, hfound]
    have ⟨attrs, hattrs_exists2⟩ :
      ∃ attrs : UnaryFunction, εnv.entities.attrs ety = .some attrs
    := by simp [SymEntities.attrs, hety_exists]
    have ⟨hwf_attrs, hty_arg_attrs⟩ := wf_env_implies_attrs_wf hwf hattrs_exists2
    exists attrs
    constructor
    -- Entity type exists in `εnv.entities`
    · assumption
    -- Some well-formedness and well-typedness conditions
    · simp only [hwf_attrs, hty_arg_attrs, true_and]
      -- TODO: show that the `attrs.outType` is `TermType.ofRecordType rty.1`
      simp only [
        hety_exists,
        SymEntities.attrs, SymEntityData.ofEntityType,
        SymEntityData.ofStandardEntityType,
        SymEntityData.ofStandardEntityType.attrsUUF,
        SymEntityData.ofEnumEntityType,
        SymEntityData.emptyAttrs,
        Option.bind_some_fun,
        Option.some.injEq,
      ] at hattrs_exists2
      split at hattrs_exists2 <;> simp only at hattrs_exists2
      -- Standard entity types
      · simp only [
          ← hattrs_exists2,
          UnaryFunction.outType, TermType.ofType,
          TermType.record.injEq, Data.Map.mk.injEq,
        ]
        simp only [EntitySchemaEntry.attrs] at hattrs_exists
        simp [hattrs_exists]
      -- Enum entity types
      · simp only [← hattrs_exists2, UnaryFunction.outType, TermType.ofType, TermType.record.injEq]
        simp only [EntitySchemaEntry.attrs] at hattrs_exists
        simp [← hattrs_exists, TermType.ofRecordType, Data.Map.empty]
  case _ =>
    simp at hattrs_exists

end Cedar.Thm
