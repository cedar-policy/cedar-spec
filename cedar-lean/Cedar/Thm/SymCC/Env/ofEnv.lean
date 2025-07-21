import Cedar.Thm.Validation.Typechecker.WF
import Cedar.Thm.Validation.WellTyped.TypeLifting
import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.SymCC.Data.Hierarchy
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Data.LT
import Cedar.Thm.SymCC.Term.WF
import Cedar.Thm.SymCC.Term.Lit
import Cedar.Thm.SymCC.Term.UDF
import Cedar.Thm.Data.List.Lemmas

/-!
This file contains some facts about `SymEnv.ofEnv`.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open SymCC
open Cedar.Data

/--
If some entity exists in `Γ`, then it must
also exists in `SymEnv.ofEnv Γ` with the corresponding `SymEntityData`
-/
theorem ofEnv_preserves_entity
  {Γ : TypeEnv} {εnv : SymEnv} {ety : EntityType} {entry : EntitySchemaEntry}
  (hεnv : εnv = SymEnv.ofEnv Γ)
  (hfind : Map.find? Γ.ets ety = some entry) :
  Map.find? εnv.entities ety = some (SymEntityData.ofEntityType ety entry)
:= by
  simp [hεnv, Map.find?, SymEnv.ofEnv, SymEntities.ofSchema, Map.toList]
  simp [Map.find?] at hfind
  -- Simplify hfind
  split at hfind
  case _ _ _ hfind2 =>
    simp only [Option.some.injEq] at hfind
    simp only [hfind] at hfind2
    have hfind := hfind2
    have h := List.find?_some hfind
    simp only [beq_iff_eq] at h
    simp only [h] at hfind
    apply Map.find?_implies_make_find?
    apply List.find?_implies_append_find?
    apply List.find?_implies_find?_fst_map
    assumption
  case _ => contradiction

/-- An action entity type is compiled correctly -/
theorem ofEnv_preserves_action_entity
  {Γ : TypeEnv} {uid : EntityUID}
  (hwf : Γ.WellFormed)
  (hmem : Map.contains Γ.acts uid) :
  Map.find? (SymEnv.ofEnv Γ).entities uid.ty =
    some (SymEntityData.ofActionType
      uid.ty
      (Γ.acts.toList.map λ (act, _) => act.ty).eraseDups
      Γ.acts)
:= by
  simp only [SymEnv.ofEnv, SymEntities.ofSchema]
  have hfind₁ :
    (List.map
      (fun x => (x.fst, SymEntityData.ofEntityType x.fst x.snd))
      (Map.toList Γ.ets)
    ).find? (λ ⟨k', _⟩ => k' == uid.ty) = none
  := by
    apply List.find?_eq_none.mpr
    intros entry hmem_entry heq_ety_uid_ty
    have ⟨ety, data⟩ := entry
    have ⟨entry', hmem_entry', heq⟩ := List.mem_map.mp hmem_entry
    have ⟨ety', data'⟩ := entry'
    simp only [Prod.mk.injEq] at heq
    have ⟨heq_ety, heq_data⟩ := heq
    have hwf_ets : Map.WellFormed Γ.ets :=
      wf_env_implies_wf_ets_map hwf
    have hmem_ets := (Map.in_list_iff_find?_some hwf_ets).mp hmem_entry'
    simp only [beq_iff_eq] at heq_ety_uid_ty
    simp only [heq_ety, heq_ety_uid_ty] at hmem_ets
    have ⟨_, hmem_acts⟩ := Map.contains_iff_some_find?.mp hmem
    have := wf_env_disjoint_ets_acts hwf hmem_ets hmem_acts
    contradiction
  have hfind₂ :
    ((List.map
        (fun actTy =>
          (actTy,
            SymEntityData.ofActionType actTy
              (List.map (fun x => x.fst.ty) (Map.toList Γ.acts)).eraseDups Γ.acts))
        (List.map (fun x => x.fst.ty) (Map.toList Γ.acts)).eraseDups).find?
      (λ ⟨k', _⟩ => k' == uid.ty)
    ).isSome
  := by
    apply List.find?_isSome.mpr
    simp only [
      List.mem_map, beq_iff_eq, Prod.exists,
      Prod.mk.injEq, exists_and_right,
      exists_eq_right,
    ]
    apply Exists.intro
    exists uid.ty
    simp only [true_and]
    constructor
    · apply List.mem_implies_mem_eraseDups
      apply List.mem_map.mpr
      have ⟨entry, hmem_entry⟩ := Map.contains_iff_some_find?.mp hmem
      exists (uid, entry)
      simp only [and_true]
      have hwf_acts : Map.WellFormed Γ.acts :=
        wf_env_implies_wf_acts_map hwf
      apply (Map.in_list_iff_find?_some hwf_acts).mpr
      assumption
    · rfl
  have ⟨_, hfind, hmem⟩ := Map.map_make_append_find_disjoint hfind₁ hfind₂
  simp only [hfind, Option.some.injEq]
  have ⟨_, _, heq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at heq
  have ⟨heq_uid_ty, heq⟩ := heq
  simp only [heq_uid_ty] at heq
  simp [heq]

theorem ofActionType_contains_act
  {Γ : TypeEnv} {uid : EntityUID}
  (hwf : Γ.WellFormed)
  (hmem : Map.contains Γ.acts uid) :
  ∃ m, (SymEntityData.ofActionType
      uid.ty
      (Γ.acts.toList.map λ (act, _) => act.ty).eraseDups
      Γ.acts).members = some m ∧ m.contains uid.eid
:= by
  simp only [
    SymEntityData.ofActionType,
    SymEntityData.ofActionType.acts,
    Option.some.injEq, exists_eq_left',
  ]
  apply Set.contains_prop_bool_equiv.mpr
  apply (Set.make_mem _ _).mp
  apply List.mem_filterMap.mpr
  have ⟨entry, hentry⟩ := Map.contains_iff_some_find?.mp hmem
  exists (uid, entry)
  constructor
  · have hwf_acts : Map.WellFormed Γ.acts := wf_env_implies_wf_acts_map hwf
    exact (Map.in_list_iff_find?_some hwf_acts).mpr hentry
  · simp

/-- A variant of `ofEnv_preserves_entity` -/
theorem ofEnv_entity_exists
  {Γ : TypeEnv} {ety : EntityType}
  (hmem : Map.contains Γ.ets ety) :
  Map.contains (SymEnv.ofEnv Γ).entities ety
:= by
  apply Map.contains_iff_some_find?.mpr
  have ⟨entry, hentry⟩ := Map.contains_iff_some_find?.mp hmem
  exists (SymEntityData.ofEntityType ety entry)
  exact ofEnv_preserves_entity rfl hentry

/-- Similar to `ofEnv_entity_exists` but for action entities -/
theorem ofEnv_action_entity_exists
  {Γ : TypeEnv} {uid : EntityUID}
  (hwf : Γ.WellFormed)
  (hmem : Map.contains Γ.acts uid) :
  Map.contains (SymEnv.ofEnv Γ).entities uid.ty
:= by
  apply Map.contains_iff_some_find?.mpr
  simp [ofEnv_preserves_action_entity hwf hmem]

theorem ofSchema_find?_ets
  {Γ : TypeEnv} {ety : EntityType} {entry : EntitySchemaEntry}
  (hfind_ety : Γ.ets.find? ety = .some entry) :
  Map.find? (SymEntities.ofSchema Γ.ets Γ.acts) ety
  = .some (SymEntityData.ofEntityType ety entry)
:= by
  apply Map.find?_implies_make_find?
  simp only [List.find?_append]
  simp only [Option.or_eq_some_iff]
  apply Or.inl
  simp only [List.find?_map]
  unfold Function.comp
  simp only
  have hfind_ety':
    List.find? (fun x => x.fst == ety) (Map.toList Γ.ets)
    = .some (ety, entry)
  := by
    simp only [Map.find?] at hfind_ety
    simp only [Map.toList]
    split at hfind_ety
    · rename_i heq
      simp only [Option.some.injEq] at hfind_ety
      simp only [hfind_ety] at heq ⊢
      have := List.find?_some heq
      simp only [beq_iff_eq] at this
      simp only [heq, this]
    · contradiction
  simp [hfind_ety']

theorem ofSchema_find?_acts
  {Γ : TypeEnv} {uid : EntityUID} {entry : ActionSchemaEntry}
  (hwf_Γ : Γ.WellFormed)
  (hfind_uid : Γ.acts.find? uid = .some entry) :
  Map.find? (SymEntities.ofSchema Γ.ets Γ.acts) uid.ty
  = .some (SymEntityData.ofActionType
    uid.ty
    (Γ.acts.toList.map λ (act, _) => act.ty).eraseDups
    Γ.acts)
:= by
  have ⟨δ, hfind_δ, hmem_δ⟩ :
    ∃ δ,
      Map.find? (SymEntities.ofSchema Γ.ets Γ.acts) uid.ty
      = .some δ ∧
      (uid.ty, δ) ∈ List.map
        (λ actTy =>
          (actTy,
            SymEntityData.ofActionType actTy (List.map (λ x => x.fst.ty) (Map.toList Γ.acts)).eraseDups Γ.acts))
        (List.map (λ x => x.fst.ty) (Map.toList Γ.acts)).eraseDups
  := by
    have hnot_find_ets : Map.find? Γ.ets uid.ty = .none := by
      cases hfind_ets : Map.find? Γ.ets uid.ty with
      | none => rfl
      | some =>
        have := wf_env_disjoint_ets_acts hwf_Γ hfind_ets hfind_uid
        contradiction
    apply Map.map_make_append_find_disjoint
    · simp only [List.find?_map]
      unfold Function.comp
      simp only
      simp only [Map.find?] at hnot_find_ets
      have :
        List.find? (fun x => x.fst == uid.ty) (Map.toList Γ.ets) = .none
      := by
        cases h : List.find? (fun x => x.fst == uid.ty) (Map.toList Γ.ets) with
        | none => rfl
        | some =>
          simp only [Map.toList] at h
          simp [h] at hnot_find_ets
      simp [this]
    · apply List.find?_isSome.mpr
      simp only [
        List.mem_map, beq_iff_eq,
        Prod.exists, Prod.mk.injEq,
        exists_and_right,
        exists_eq_right,
      ]
      exists SymEntityData.ofActionType uid.ty
        (List.map (fun x => x.fst.ty) (Map.toList Γ.acts)).eraseDups
        Γ.acts
      exists uid.ty
      simp only [and_self, and_true]
      apply List.mem_implies_mem_eraseDups
      apply List.mem_map.mpr
      exists (uid, entry)
      simp only [and_true]
      have := wf_env_implies_wf_acts_map hwf_Γ
      exact (Map.in_list_iff_find?_some this).mpr hfind_uid
  simp only [hfind_δ, Option.some.injEq]
  have ⟨_, _, h⟩ := List.mem_map.mp hmem_δ
  simp only [Prod.mk.injEq] at h
  simp only [h.1, true_and] at h
  simp [h]

theorem ofEnv_wf_entity
  {Γ : TypeEnv} {ety : EntityType}
  (hwf : Γ.WellFormed)
  (hwf_ety : EntityType.WellFormed Γ ety) :
  (SymEntities.ofSchema Γ.ets Γ.acts).isValidEntityType ety
:= by
  simp only [SymEntities.isValidEntityType]
  cases hwf_ety with
  | inl hwf_ety =>
    exact ofEnv_entity_exists hwf_ety
  | inr hwf_ety_act =>
    -- Principal is an action. TODO: do we allow this?
    have ⟨uid, huid, heq⟩ := hwf_ety_act
    simp only [←heq]
    exact ofEnv_action_entity_exists hwf huid

/--
Lemma that if a concrete `Γ : TypeEnv` has tags for
a particular entity type, then `SymEnv.ofEnv Γ` must also
have tags for it
-/
theorem ofEnv_preserves_tags
  {Γ : TypeEnv} {ety : EntityType} {ty : CedarType}
  (h : Γ.ets.tags? ety = some (some ty)) :
  ∃ τags : SymTags,
    (SymEnv.ofEnv Γ).entities.tags ety = some (some τags) ∧
    τags.vals.outType = TermType.ofType ty
:= by
  simp only [EntitySchema.tags?, Option.map_eq_some_iff] at h
  have ⟨found_entry, ⟨hfind, hty_entry⟩⟩ := h
  -- The corresponding entity exists in `εnv`
  have hety_exists :
    Map.find? (SymEnv.ofEnv Γ).entities ety
    = some (SymEntityData.ofEntityType ety found_entry)
  := by
    apply ofEnv_preserves_entity ?_ hfind
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
  {Γ : TypeEnv} {εnv : SymEnv}
  {rty : RecordType} {ety : EntityType}
  (hεnv : εnv = SymEnv.ofEnv Γ)
  (hattrs_exists : Γ.ets.attrs? ety = some rty)
  (hwf : εnv.WellFormed) :
  ∃ attrs : UnaryFunction,
    εnv.entities.attrs ety = .some attrs ∧
    UnaryFunction.WellFormed εnv.entities attrs ∧
    attrs.argType = .entity ety ∧
    attrs.outType = .record (Map.mk (TermType.ofRecordType rty.1))
:= by
  simp only [EntitySchema.attrs?, Map.find?, Option.map_eq_some_iff] at hattrs_exists
  split at hattrs_exists
  case h_1 found_ety found_entry hfind =>
    simp only [Option.some.injEq, exists_eq_left'] at hattrs_exists
    -- The corresponding entity exists in `εnv`
    have hety_exists :
      Map.find? εnv.entities ety
      = some (SymEntityData.ofEntityType ety found_entry)
    := by
      apply ofEnv_preserves_entity hεnv
      simp [Map.find?, hfind]
    have ⟨attrs, hattrs_exists2⟩ :
      ∃ attrs : UnaryFunction, εnv.entities.attrs ety = .some attrs
    := by simp [SymEntities.attrs, hety_exists]
    have ⟨hwf_attrs, hty_arg_attrs⟩ := wf_εnv_implies_attrs_wf hwf hattrs_exists2
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
          TermType.record.injEq, Map.mk.injEq,
        ]
        simp only [EntitySchemaEntry.attrs] at hattrs_exists
        simp [hattrs_exists]
      -- Enum entity types
      · simp only [← hattrs_exists2, UnaryFunction.outType, TermType.ofType, TermType.record.injEq]
        simp only [EntitySchemaEntry.attrs] at hattrs_exists
        simp [← hattrs_exists, TermType.ofRecordType, Map.empty]
  case _ =>
    simp at hattrs_exists

theorem ofRecordType_eq_map
  {rty : List (Attr × QualifiedType)} :
  TermType.ofRecordType rty =
    rty.map (fun x => (x.fst, TermType.ofQualifiedType x.snd))
:= by
  induction rty with
  | nil => simp [TermType.ofRecordType]
  | cons hd tl ih =>
    simp only [TermType.ofRecordType, List.map_cons, ih]

/--
`TermType.ofType` of well-formed `CedarType` is well-formed
(under the compiled `SymEnv`).
-/
theorem ofType_wf
  {Γ : TypeEnv} {ty : CedarType}
  (hwf : Γ.WellFormed)
  (hwf_ty : CedarType.WellFormed Γ ty) :
  (TermType.ofType ty).WellFormed (SymEnv.ofEnv Γ).entities
:= by
  cases ty with
  | bool _ | int | string | ext _ => constructor
  | entity ety =>
    constructor
    cases hwf_ty with | entity_wf hwf_ety =>
    apply ofEnv_wf_entity hwf hwf_ety
  | set sty =>
    constructor
    cases hwf_ty with | set_wf hwf_sty =>
    exact ofType_wf hwf hwf_sty
  | record rty =>
    cases hwf_ty with | record_wf hwf_rty hwf_attrs =>
    simp only [TermType.ofType, ofRecordType_eq_map]
    constructor
    · intros attr attr_ty hfind_attr
      have := Map.find?_mem_toList hfind_attr
      simp only [Map.toList, Map.kvs] at this
      have ⟨entry, hmem_entry, heq_entry⟩ := List.mem_map.mp this
      simp only [Prod.mk.injEq] at heq_entry
      have ⟨heq_attr, heq_attr_ty⟩ := heq_entry
      have hfind := hwf_attrs attr entry.snd
      have := (Map.in_list_iff_find?_some hwf_rty).mp hmem_entry
      simp only [heq_attr] at this
      specialize hfind this
      simp only [←heq_attr_ty]
      cases hsnd : entry.snd with
      | optional attr_ty' | required attr_ty' =>
        simp only [hsnd, TermType.ofQualifiedType] at hfind ⊢
        cases hfind with | _ hfind =>
        try constructor
        exact ofType_wf hwf hfind
    · apply Map.mapOnValues_wf.mp
      exact hwf_rty
termination_by ty
decreasing_by
  simp [*]
  all_goals
    have h1 : ty = CedarType.record rty := by assumption
    simp [h1]
    calc
      sizeOf attr_ty' < sizeOf entry.snd := by simp [hsnd]
      _ < sizeOf entry := by
        cases entry
        simp
        omega
      _ < sizeOf rty.1 := by
        simp [List.sizeOf_lt_of_mem hmem_entry]
      _ < sizeOf rty := by
        cases rty
        simp
      _ < 1 + sizeOf rty := by omega

/--
`TermType.ofType` is a right inverse of `CedarType.cedarType?`
when applied to a well-formed `CedarType`.
-/
theorem wf_ofType_right_inverse_cedarType?
  {Γ : TypeEnv} {ty : CedarType}
  (hwf : Γ.WellFormed)
  (hwf_ty : CedarType.WellFormed Γ ty) :
  (TermType.ofType ty).cedarType? = ty.liftBoolTypes
:= by
  cases ty with
  | bool _ | int | string | entity _ | ext _ =>
    simp only [
      TermType.ofType, TermType.cedarType?,
      CedarType.liftBoolTypes, BoolType.lift,
    ]
  | set sty =>
    cases hwf_ty with | set_wf hwf_sty =>
    have := wf_ofType_right_inverse_cedarType? hwf hwf_sty
    simp [
      TermType.ofType, TermType.cedarType?,
      this, CedarType.liftBoolTypes,
    ]
  | record rty =>
    simp only [
      TermType.ofType, TermType.cedarType?,
      Option.bind_eq_bind, CedarType.liftBoolTypes,
    ]
    rw [List.mapM₃_eq_mapM
        (fun x =>
          (TermType.cedarType?.qualifiedType? x.snd).bind
          fun t => some (x.fst, t))]
    have := ofRecordType_forall₂ rty.1 hwf_ty
    have := List.mapM_some_iff_forall₂.mpr this
    simp [this, RecordType.liftBoolTypes]
termination_by sizeOf ty
decreasing_by
  simp [*]
  simp [*]
  cases rty
  simp
  omega
where
  ofRecordType_forall₂
    (rty : List (Attr × QualifiedType))
    (hwf : CedarType.WellFormed Γ (CedarType.record (Map.mk rty))) :
    List.Forall₂ (fun x y =>
      ((TermType.cedarType?.qualifiedType? x.snd).bind fun t => some (x.fst, t)) = some y)
      (TermType.ofRecordType rty) (CedarType.liftBoolTypesRecord rty)
  := by
    cases hwf with | record_wf hwf_rty hwf_attrs =>
    simp [
      ←Map.in_list_iff_find?_some hwf_rty,
      Map.kvs,
    ] at hwf_attrs
    cases hrty : rty with
    | nil => constructor
    | cons hd tl =>
      simp only [hrty] at hwf_attrs hwf_rty
      constructor
      · have hwf_hd_snd := hwf_attrs hd.fst hd.snd
        simp only [List.mem_cons, true_or, forall_const] at hwf_hd_snd
        cases h : hd.snd with
        | optional attr_ty =>
          simp only [h] at hwf_hd_snd
          cases hwf_hd_snd with | optional_wf hwf_hd_snd =>
          simp only [
            wf_ofType_right_inverse_cedarType? hwf hwf_hd_snd,
            TermType.ofQualifiedType,
            TermType.cedarType?.qualifiedType?,
          ]
          simp only [
            Option.bind_some_fun, Option.bind_some,
            Option.some.injEq, Prod.mk.injEq,
            true_and, QualifiedType.liftBoolTypes,
          ]
        | required attr_ty =>
          simp only [h] at hwf_hd_snd
          cases hwf_hd_snd with | required_wf hwf_hd_snd =>
          simp only [
            TermType.ofQualifiedType,
            TermType.cedarType?.qualifiedType?,
            Option.bind_some_fun, Option.bind_some,
            Option.some.injEq, Prod.mk.injEq,
            true_and, QualifiedType.liftBoolTypes,
          ]
          unfold TermType.cedarType?.qualifiedType?
          split
          case _ heq =>
            unfold TermType.ofType at heq
            split at heq
            all_goals contradiction
          case _ heq =>
            simp [wf_ofType_right_inverse_cedarType? hwf hwf_hd_snd]
      · apply ofRecordType_forall₂
        constructor
        · exact Map.wf_implies_tail_wf hwf_rty
        · intros attr qty hmem_tl
          apply hwf_attrs
          simp only [List.mem_cons]
          apply Or.inr
          apply (Map.in_list_iff_find?_some (Map.wf_implies_tail_wf hwf_rty)).mpr
          exact hmem_tl
  termination_by sizeOf rty
  decreasing_by
    any_goals
      calc
        sizeOf attr_ty < sizeOf hd.snd := by simp [*]
        _ < sizeOf hd := by
          cases hd
          simp
          omega
        _ < sizeOf (hd :: tl) := by
          simp
          omega
        _ = sizeOf rty := by
          simp [*]
    simp [*]
    omega

theorem ofEnv_request_is_wf
  {Γ : TypeEnv}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).request.WellFormed
    (SymEnv.ofEnv Γ).entities
:= by
  simp only [
    SymEnv.ofEnv,
    SymRequest.ofRequestType,
    SymRequest.WellFormed,
    TermType.ofType,
  ]
  have ⟨hwf_princ, hwf_act, hwf_res, hwf_ctx⟩ := wf_env_implies_wf_request hwf
  and_intros
  -- Principal well-formed
  · constructor
    constructor
    exact ofEnv_wf_entity hwf hwf_princ
  -- Principal well-typed
  · simp only [Term.typeOf, TermType.isEntityType]
  -- Action well-formed
  · constructor
    constructor
    have := ofEnv_preserves_action_entity hwf hwf_act
    simp only [SymEnv.ofEnv] at this
    simp only [SymEntities.isValidEntityUID, this]
    have ⟨m, hm⟩ := ofActionType_contains_act hwf hwf_act
    simp only [hm]
  -- Action well-typed
  · simp only [Term.typeOf, TermPrim.typeOf, TermType.isEntityType]
  -- Resource well-formed
  · constructor
    constructor
    exact ofEnv_wf_entity hwf hwf_res
  -- Resource well-typed
  · simp only [Term.typeOf, TermType.isEntityType]
  -- Context well-formed
  · constructor
    exact ofType_wf hwf hwf_ctx
  -- Context well-typed
  · simp [Term.typeOf, TermType.isCedarRecordType]
    have := wf_ofType_right_inverse_cedarType? hwf hwf_ctx
    simp only [TermType.ofType] at this
    simp [this, CedarType.liftBoolTypes]

theorem ofEnv_request_is_basic
  {Γ : TypeEnv} :
  (SymEnv.ofEnv Γ).request.IsBasic
:= by
  simp [
    SymEnv.ofEnv,
    SymRequest.ofRequestType,
    SymRequest.IsBasic,
    Term.isBasic,
    Term.isLiteral,
  ]

theorem ofEnv_request_is_swf
  {Γ : TypeEnv}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).request.StronglyWellFormed
    (SymEnv.ofEnv Γ).entities
:= by
  simp only [SymRequest.StronglyWellFormed]
  constructor
  exact ofEnv_request_is_wf hwf
  exact ofEnv_request_is_basic

theorem ofStandardEntityType_is_wf
  {ety : EntityType} {Γ : TypeEnv} {entry : StandardSchemaEntry}
  (hwf : Γ.WellFormed)
  (hfind : Map.find? Γ.ets ety = some (.standard entry)) :
  SymEntityData.WellFormed
    (SymEnv.ofEnv Γ).entities
    ety
    (SymEntityData.ofStandardEntityType ety entry)
:= by
  simp only [SymEntityData.ofStandardEntityType]
  have hwf_attrs : (CedarType.record entry.attrs).WellFormed Γ := by
    apply wf_env_implies_wf_attrs (ety := ety) hwf
    simp only [EntitySchema.attrs?, hfind, Option.map, EntitySchemaEntry.attrs]
  have hwf_ety :
    TermType.WellFormed (SymEnv.ofEnv Γ).entities (TermType.ofType (CedarType.entity ety))
  := by
    apply ofType_wf hwf
    constructor
    apply Or.inl
    simp only [EntitySchema.contains, hfind, Option.isSome]
  and_intros
  all_goals simp only
  · exact hwf_ety
  · exact ofType_wf hwf hwf_attrs
  · simp only [
      SymEntityData.ofStandardEntityType.attrsUUF,
      UnaryFunction.argType,
      TermType.ofType,
    ]
  · have := wf_ofType_right_inverse_cedarType? hwf hwf_attrs
    simp [
      SymEntityData.ofStandardEntityType.attrsUUF,
      UnaryFunction.outType,
      TermType.isCedarRecordType,
      this,
      CedarType.liftBoolTypes,
    ]
  -- Symbolic ancestors are well-formed
  · intros anc_ty sym_anc_f hfind_anc
    have := Map.find?_mem_toList hfind_anc
    simp only [Map.toList] at this
    have := Map.make_mem_list_mem this
    have ⟨anc_ty', hmem_anc', heq_anc'⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq_anc'
    simp only [heq_anc'.1] at hmem_anc'
    simp only [←heq_anc'.2, heq_anc'.1]
    and_intros
    · exact hwf_ety
    · simp
      apply ofType_wf hwf
      constructor
      constructor
      exact wf_env_implies_wf_ancestor hwf hfind hmem_anc'
    · simp only [
        UnaryFunction.argType,
        SymEntityData.ofStandardEntityType.ancsUUF,
      ]
      rfl
    · simp only [
        UnaryFunction.outType,
        SymEntityData.ofStandardEntityType.ancsUUF,
      ]
      rfl
  · exact Map.make_wf _
  -- Symbolic tags are well-formed
  · cases htags : entry.tags with
    | none => simp
    | some tags =>
      have hwf_tags : CedarType.WellFormed Γ tags
      := by
        apply wf_env_implies_wf_tag_type (ety := ety) hwf
        simp [
          EntitySchema.tags?,
          EntitySchemaEntry.tags?,
          hfind, htags,
        ]
      intros τs hτs
      simp only [
        Option.map,
        SymEntityData.ofStandardEntityType.symTags,
        Option.some.injEq,
      ] at hτs
      simp only [←hτs, SymTags.WellFormed]
      and_intros
      all_goals simp only [
        UnaryFunction.argType,
        UnaryFunction.outType,
      ]
      · exact hwf_ety
      · simp only [TermType.ofType]
        constructor
        constructor
      · simp only [TermType.ofType]
      · simp only [TermType.ofType]
      · simp only [TermType.tagFor, EntityTag.mk]
        constructor
        · intros attr attr_ty hfind_attr
          have := Map.find?_mem_toList hfind_attr
          simp only [
            Map.toList, Map.kvs, List.mem_cons,
            Prod.mk.injEq, List.not_mem_nil,
            or_false,
          ] at this
          cases this with
          | inl h =>
            simp only [h.2]
            exact hwf_ety
          | inr h =>
            simp only [h.2]
            constructor
        · simp [
            Map.WellFormed, Map.toList, Map.kvs,
            Map.make, List.canonicalize, Map.mk.injEq,
            List.insertCanonical,
          ]
      · exact ofType_wf hwf hwf_tags
      · simp only [
          TermType.isCedarType,
          wf_ofType_right_inverse_cedarType? hwf hwf_tags,
          Option.isSome,
        ]
  · simp

theorem ofEnumEntityType_is_wf
  {ety : EntityType} {Γ : TypeEnv} {eids : Set String}
  (hwf : Γ.WellFormed)
  (hfind : Map.find? Γ.ets ety = some (.enum eids)) :
  SymEntityData.WellFormed
    (SymEnv.ofEnv Γ).entities
    ety
    (SymEntityData.ofEnumEntityType ety eids)
:= by
  and_intros
  all_goals simp only [
    SymEntityData.ofEnumEntityType,
    Map.empty, Map.toList, Map.kvs,
  ]
  · constructor
    · intros _ _ h
      simp [Map.empty, Map.toList, Map.kvs] at h
    · simp [Map.WellFormed, Map.make, Map.empty, List.canonicalize, Map.toList]
  · simp only [
      Map.empty, Term.isLiteral,
      List.nil.sizeOf_spec, Nat.reduceAdd,
      List.all_eq_true,
      Subtype.forall, Prod.forall,
    ]
    intros _ _ _ h
    simp [List.attach₃] at h
  · simp [Term.typeOf, Map.empty, List.attach₃]
  · simp [Map.WellFormed, Map.make, Map.empty, List.canonicalize, Map.toList]
  · intros _ _ h
    contradiction
  · simp only [UnaryFunction.argType, SymEntityData.emptyAttrs, TermType.ofType]
  · simp [
      UnaryFunction.outType, SymEntityData.emptyAttrs,
      TermType.ofType, TermType.isCedarRecordType,
      Map.empty, TermType.cedarType?, List.mapM₃,
      List.attach₃,
    ]
  · intros _ _ h
    simp [Map.empty, Map.toList, Map.kvs, Map.find?] at h
  · simp [Map.WellFormed, Map.make, Map.empty, List.canonicalize, Map.toList]
  · intros _ h
    contradiction
  · have ⟨_, h⟩ := wf_env_implies_wf_entity_entry hwf hfind
    simp [h]

theorem ofEntityType_is_wf
  {ety : EntityType} {Γ : TypeEnv} {entry : EntitySchemaEntry}
  (hwf : Γ.WellFormed)
  (hfind : Map.find? Γ.ets ety = some entry) :
  SymEntityData.WellFormed
    (SymEnv.ofEnv Γ).entities
    ety
    (SymEntityData.ofEntityType ety entry)
:= by
  cases entry with
  | standard entry => exact ofStandardEntityType_is_wf hwf hfind
  | enum eids => exact ofEnumEntityType_is_wf hwf hfind

/--
A technical lemma that `SymEntityData.ofActionType.ancsUDF`
produces a well-formed UDF.
-/
theorem ofActionType_ancsUDF_is_wf
  {uid : EntityUID} {Γ : TypeEnv}
  {anc : EntityType}
  {anc_f : UnaryFunction} (hwf : Γ.WellFormed)
  (hanc :
    (SymEntityData.ofActionType
      uid.ty
      (List.map (fun x => x.fst.ty) (Map.toList Γ.acts)).eraseDups
      Γ.acts).ancestors.find? anc = some anc_f) :
  UnaryFunction.WellFormed
    (SymEnv.ofEnv Γ).entities
    (SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts anc) ∧
  (SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts anc).argType = .entity uid.ty ∧
  (SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts anc).outType = .set (.entity anc)
:= by
  have hwf_acts := wf_env_implies_wf_acts_map hwf
  simp only [
    SymEntityData.ofActionType.ancsUDF,
    SymEntityData.ofActionType,
    UnaryFunction.argType,
    UnaryFunction.outType,
  ]
  have := Map.find?_mem_toList hanc
  simp only [Map.toList] at this
  have := Map.make_mem_list_mem this
  have ⟨anc_ty', hmem_anc', heq_anc'⟩ := List.mem_map.mp this
  simp only [Prod.mk.injEq] at heq_anc'
  simp only [heq_anc'.1] at hmem_anc'
  and_intros
  any_goals simp only
  · constructor
    · intros; contradiction
    · intros; contradiction
    · apply ofType_wf hwf
      constructor
      have := List.mem_eraseDups_implies_mem hmem_anc'
      have ⟨act, hact, hact_ty⟩ := List.mem_map.mp this
      apply Or.inr
      simp only [
        ActionSchema.IsActionEntityType,
        ActionSchema.contains,
      ]
      have := (Map.in_list_iff_find?_some
        (wf_env_implies_wf_acts_map hwf)).mp hact
      exists act.fst
      simp only [this, Option.isSome, true_and, hact_ty]
    · simp [Set.empty, Set.WellFormed, Set.make, Set.toList, Set.elts, List.canonicalize]
  · simp [Set.empty, Term.isLiteral]
  · simp [Term.typeOf, TermType.ofType, Set.empty, List.attach₃]
  · simp only [Map.make_wf]
  · -- WF of the ancestor UDF
    intros tᵢ tₒ hmem
    have := Map.make_mem_list_mem hmem
    have ⟨act_entry, hact_entry, hsym⟩ := List.mem_filterMap.mp this
    simp [bind, Option.bind] at hsym
    split at hsym
    contradiction
    rename_i t₁ h₁
    simp only [
      SymEntityData.ofActionType.termOfType?,
      Option.ite_none_right_eq_some,
      Option.some.injEq,
    ] at h₁
    simp only [
      Option.some.injEq, Prod.mk.injEq,
      SymEntityData.ofActionType.ancsTerm,
    ] at hsym
    constructor
    -- tᵢ is well-formed
    · simp only [←hsym.1, ←h₁.2]
      constructor
      · constructor
        constructor
        have := (Map.in_list_iff_find?_some hwf_acts).mp hact_entry
        have : Map.contains Γ.acts act_entry.fst := by
          simp [Map.contains, this]
        have := ofEnv_preserves_action_entity hwf this
        simp only [
          this,
          SymEntities.isValidEntityUID,
          SymEntityData.ofActionType,
          SymEntityData.ofActionType.acts,
          Set.contains,
        ]
        simp only [List.elem_eq_contains, List.contains_eq_mem, decide_eq_true_eq]
        apply (Set.make_mem _ _).mp
        apply List.mem_filterMap.mpr
        exists act_entry
        simp only [↓reduceIte, and_true]
        apply (Map.in_list_iff_find?_some hwf_acts).mpr
        assumption
      · simp only [Term.isLiteral]
    constructor
    -- tᵢ has the right type
    · simp [←h₁, ←hsym, Term.typeOf, TermPrim.typeOf, TermType.ofType]
    -- tₒ is well-formed and has the right type
    simp only [
      ←h₁, ←hsym, TermType.ofType,
      Term.WellFormedLiteral,
    ]
    apply and_assoc.mpr
    apply and_left_comm.mp
    constructor
    · -- tₒ is literal
      simp only [Factory.setOf]
      apply lit_term_set_impliedBy_lit_elts
      intros t hmem_t
      have := (Set.make_mem _ _).mpr hmem_t
      have ⟨anc, hanc, hsym⟩ := List.mem_filterMap.mp this
      simp only [
        SymEntityData.ofActionType.termOfType?,
        Option.ite_none_right_eq_some,
        Option.some.injEq,
      ] at hsym
      simp only [←hsym, Term.isLiteral]
    · apply wf_setOf
      · intros t hmem_t
        simp only [List.mem_filterMap] at hmem_t
        have ⟨anc2, hmem_anc2, hsym⟩ := hmem_t
        simp only [
          SymEntityData.ofActionType.termOfType?,
          Option.ite_none_right_eq_some,
          Option.some.injEq,
        ] at hsym
        simp only [←hsym]
        constructor
        constructor
        have := (Map.in_list_iff_find?_some hwf_acts).mp hact_entry
        have ⟨anc_entry, hfind_anc_entry, hwf_anc_entry⟩ :=
          wf_env_implies_wf_action_entity_ancestor hwf this hmem_anc2
        have := ofEnv_preserves_action_entity hwf
          (Map.find?_some_implies_contains hfind_anc_entry)
        simp only [
          SymEntities.isValidEntityUID,
          this,
          SymEntityData.ofActionType,
          SymEntityData.ofActionType.acts,
        ]
        apply Set.contains_prop_bool_equiv.mpr
        apply (Set.make_mem _ _).mp
        apply List.mem_filterMap.mpr
        simp only [
          Option.ite_none_right_eq_some,
          Option.some.injEq, Prod.exists,
          exists_and_right,
        ]
        exists anc2
        simp only [and_self, and_true]
        exists anc_entry
        apply (Map.in_list_iff_find?_some hwf_acts).mpr
        exact hfind_anc_entry
      · intros t hmem_t
        have ⟨anc, hanc, hsym⟩ := List.mem_filterMap.mp hmem_t
        simp only [
          SymEntityData.ofActionType.termOfType?,
          Option.ite_none_right_eq_some,
          Option.some.injEq,
        ] at hsym
        simp only [←hsym, Term.typeOf, TermPrim.typeOf]
      · constructor
        have := List.mem_eraseDups_implies_mem hmem_anc'
        have ⟨_, h₁, h₂⟩ := List.mem_map.mp this
        simp only [←h₂]
        apply ofEnv_action_entity_exists hwf
        simp [Map.contains, (Map.in_list_iff_find?_some hwf_acts).mp h₁]
  · simp [SymEntityData.ofActionType.ancsUDF, TermType.ofType]
  · simp [SymEntityData.ofActionType.ancsUDF, TermType.ofType]

theorem ofActionType_is_wf
  {uid : EntityUID} {Γ : TypeEnv} {entry : ActionSchemaEntry}
  (hwf : Γ.WellFormed)
  (hfind : Map.find? Γ.acts uid = some entry) :
  SymEntityData.WellFormed
    (SymEnv.ofEnv Γ).entities
    uid.ty
    (SymEntityData.ofActionType
      uid.ty
      (List.map (fun x => x.fst.ty) (Map.toList Γ.acts)).eraseDups
      Γ.acts)
:= by
  have hwf_acts := wf_env_implies_wf_acts_map hwf
  and_intros
  any_goals simp only [
    SymEntityData.ofActionType,
    SymEntityData.emptyAttrs,
    Map.empty, Map.toList, Map.kvs,
    UnaryFunction.argType,
    UnaryFunction.outType,
    TermType.ofType,
  ]
  · constructor
    · intros _ _ h
      simp [Map.toList, Map.kvs] at h
    · simp [Map.WellFormed, Map.make, List.canonicalize, Map.toList]
  · simp [Term.isLiteral, List.attach₃]
  · simp [Term.typeOf, List.attach₃]
  · simp [Map.WellFormed, Map.make, List.canonicalize, Map.toList]
  · intros; contradiction
  · simp [
      TermType.isCedarRecordType,
      TermType.cedarType?,
      List.mapM₃, List.attach₃,
    ]
  -- Symbolic ancestors are well-formed
  · intros anc sym_anc_f hfind_anc
    have := Map.find?_mem_toList hfind_anc
    simp only [Map.toList] at this
    have := Map.make_mem_list_mem this
    have ⟨anc_ty', hmem_anc', heq_anc'⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq_anc'
    simp only [heq_anc'.1] at hmem_anc'
    have := ofActionType_ancsUDF_is_wf hwf hfind_anc
    simp only [←heq_anc'.2, heq_anc'.1]
    exact this
  · simp only [Map.make_wf]
  · intros; contradiction
  · intros mems h
    simp only [SymEntityData.ofActionType.acts, Option.some.injEq] at h
    simp only [Bool.not_eq_true, ←h]
    apply (Set.make_non_empty _).mp
    simp only [
      ne_eq, List.filterMap_eq_nil_iff, ite_eq_right_iff,
      reduceCtorEq, imp_false,
      Prod.forall, Classical.not_forall,
      not_imp, Decidable.not_not, exists_and_right,
    ]
    exists uid
    exists entry
    exists (Map.find?_mem_toList hfind)

theorem ofEnv_entities_is_wf
  {Γ : TypeEnv}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).entities.WellFormed
:= by
  constructor
  · exact Map.make_wf _
  · intros ety data hfind
    have := Map.find?_mem_toList hfind
    simp only [Map.kvs] at this
    have := Map.make_mem_list_mem this
    have := List.mem_append.mp this
    -- Reduce to either `ofEntityType_is_wf` or `ofActionType_is_wf`
    cases this with
    | inl hmem_ets =>
      have ⟨⟨ety', entry⟩, hmem_entry, heq_entry⟩ := List.mem_map.mp hmem_ets
      simp only [Prod.mk.injEq] at heq_entry
      have ⟨heq_ety, heq_data⟩ := heq_entry
      have hwf_ets := wf_env_implies_wf_ets_map hwf
      have := (Map.in_list_iff_find?_some hwf_ets).mp hmem_entry
      simp only [heq_ety] at this heq_data
      simp only [←heq_data]
      exact ofEntityType_is_wf hwf this
    | inr hmem_acts =>
      have ⟨ety, hmem_ety, heq_entry⟩ := List.mem_map.mp hmem_acts
      simp only [Prod.mk.injEq] at heq_entry
      have ⟨heq_ety, heq_es⟩ := heq_entry
      have hwf_acts := wf_env_implies_wf_acts_map hwf
      have hmem_ety := List.mem_eraseDups_implies_mem hmem_ety
      have ⟨⟨uid, entry⟩, hmem, heq⟩ := List.mem_map.mp hmem_ety
      simp only at heq
      have := (Map.in_list_iff_find?_some hwf_acts).mp hmem
      simp only [heq_ety] at heq
      simp only [←heq, ←heq_es, heq_ety]
      exact ofActionType_is_wf hwf this

theorem entity_uid_wf_implies_sym_entities_is_valid_entity_uid
  {Γ : TypeEnv} {uid : EntityUID}
  (hwf : Γ.WellFormed)
  (huid : EntityUID.WellFormed Γ uid) :
  (SymEnv.ofEnv Γ).entities.isValidEntityUID uid
:= by
  simp only [SymEntities.isValidEntityUID]
  cases huid with
  | inl huid =>
    simp only [EntitySchema.isValidEntityUID] at huid
    split at huid
    · rename_i entry hfind
      have := ofEnv_preserves_entity rfl hfind
      simp only [
        this,
        SymEntityData.ofEntityType,
      ]
      split
      · rename_i eids h
        split at h
        · simp only [SymEntityData.ofStandardEntityType] at h
          contradiction
        · simp only [SymEntityData.ofEnumEntityType] at h
          simp only [EntitySchemaEntry.isValidEntityEID] at huid
          simp only [Option.some.injEq] at h
          simp [←h, huid]
      · rfl
    · contradiction
  | inr huid =>
    have := ofEnv_preserves_action_entity hwf huid
    simp only [
      this,
      SymEntityData.ofActionType,
      SymEntityData.ofActionType.acts,
    ]
    apply Set.contains_prop_bool_equiv.mpr
    apply (Set.make_mem _ _).mp
    apply List.mem_filterMap.mpr
    simp only [ActionSchema.contains, Map.contains, Option.isSome] at huid
    split at huid
    · rename_i entry hfind
      exists (uid, entry)
      simp only [↓reduceIte, and_true]
      apply (Map.in_list_iff_find?_some ?_).mpr hfind
      exact wf_env_implies_wf_acts_map hwf
    · contradiction

theorem env_valid_uid_implies_sym_env_valid_uid
  {Γ : TypeEnv} {env : Env} {uid : EntityUID}
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hcont_uid : Map.contains env.entities uid = true) :
  (SymEnv.ofEnv Γ).entities.isValidEntityUID uid = true
:= by
  have ⟨hwf_Γ, _, ⟨hinst_entities, _⟩⟩ := hinst
  simp only [SymEnv.ofEnv, SymEntities.ofSchema]
  simp only [Map.contains, Option.isSome] at hcont_uid
  split at hcont_uid
  · rename_i data hfind_data
    apply entity_uid_wf_implies_sym_entities_is_valid_entity_uid hwf_Γ
    have := hinst_entities uid data hfind_data
    cases this with
    | inl hinst_data =>
      have ⟨entry, hfind_entry, hvalid_uid, _⟩ := hinst_data
      simp only [
        EntityUID.WellFormed,
        EntitySchemaEntry.isValidEntityEID,
        EntitySchema.isValidEntityUID,
        hfind_entry,
      ]
      apply Or.inl
      cases entry with
      | standard => rfl
      | enum eids =>
        simp only [Set.contains, List.elem_eq_contains, List.contains_eq_mem, decide_eq_true_eq]
        simp only [IsValidEntityEID] at hvalid_uid
        exact hvalid_uid
    | inr hinst_data =>
      have ⟨_, _, ⟨_, hfind_acts, _⟩⟩ := hinst_data
      simp only [EntityUID.WellFormed]
      apply Or.inr
      simp only [ActionSchema.contains, Map.contains, hfind_acts, Option.isSome]
  · contradiction

/--
Given a well-formed environment and a well-typed expression in that environment,
we show that the expression satisfies `ValidRefs`
-/
theorem ofEnv_entities_valid_refs_for_wt_expr
  {Γ : TypeEnv} {tx : TypedExpr}
  (hwf : Γ.WellFormed)
  (hwt : TypedExpr.WellTyped Γ tx) :
  tx.toExpr.ValidRefs ((SymEnv.ofEnv Γ).entities.isValidEntityUID ·)
:= by
  cases hwt with
  | lit hwt_prim =>
    rename_i p ty
    cases hwt_prim with
    | bool | int | string =>
      simp only [TypedExpr.toExpr]
      constructor
      constructor
    | entityUID uid huid =>
      simp only [TypedExpr.toExpr]
      constructor
      simp only [Prim.ValidRef]
      apply entity_uid_wf_implies_sym_entities_is_valid_entity_uid hwf huid
  | var hwt_var =>
    simp only [TypedExpr.toExpr]
    constructor
  | ite h₁ h₂ h₃ =>
    simp only [TypedExpr.toExpr]
    constructor
    exact ofEnv_entities_valid_refs_for_wt_expr hwf h₁
    exact ofEnv_entities_valid_refs_for_wt_expr hwf h₂
    exact ofEnv_entities_valid_refs_for_wt_expr hwf h₃
  | and h₁ h₂ | or h₁ h₂ =>
    simp only [TypedExpr.toExpr]
    constructor
    exact ofEnv_entities_valid_refs_for_wt_expr hwf h₁
    exact ofEnv_entities_valid_refs_for_wt_expr hwf h₂
  | unaryApp h
  | hasAttr_entity h | hasAttr_record h
  | getAttr_entity h | getAttr_record h =>
    simp only [TypedExpr.toExpr]
    constructor
    exact ofEnv_entities_valid_refs_for_wt_expr hwf h
  | binaryApp h₁ h₂ =>
    simp only [TypedExpr.toExpr]
    constructor
    exact ofEnv_entities_valid_refs_for_wt_expr hwf h₁
    exact ofEnv_entities_valid_refs_for_wt_expr hwf h₂
  | set hs | call hs =>
    simp only [TypedExpr.toExpr]
    constructor
    intros x hmem_x
    simp only [List.map₁, List.map_attach_eq_pmap] at hmem_x
    have ⟨x', hmem_x', hx'⟩ := List.mem_pmap.mp hmem_x
    simp only [←hx']
    have := hs x' hmem_x'
    exact ofEnv_entities_valid_refs_for_wt_expr hwf this
  | record hrec =>
    simp only [TypedExpr.toExpr]
    constructor
    intros attr hmem_attr
    simp only [List.map, List.attach₂, List.map_pmap] at hmem_attr
    have ⟨attr', hmem_attr', hattr'⟩ := List.mem_pmap.mp hmem_attr
    cases attr with | _ fst snd =>
    simp only [Prod.mk.injEq] at hattr'
    simp only [←hattr']
    have := hrec attr'.fst attr'.snd hmem_attr'
    exact ofEnv_entities_valid_refs_for_wt_expr hwf this
termination_by sizeOf tx
decreasing_by
  any_goals
    simp [*]
    omega
  · simp
    have := List.sizeOf_lt_of_mem hmem_x'
    omega
  · cases attr'
    simp
    have := List.sizeOf_lt_of_mem hmem_attr'
    simp at this
    omega
  · simp
    have := List.sizeOf_lt_of_mem hmem_x'
    omega

theorem ofEnv_entities_find?_some
  {Γ : TypeEnv} {ety : EntityType} {δ : SymEntityData}
  (hwf : Γ.WellFormed)
  (hfind : Map.find? (SymEnv.ofEnv Γ).entities ety = .some δ) :
  ((∃ entry, Map.find? Γ.ets ety = .some (.standard entry) ∧
    δ = SymEntityData.ofStandardEntityType ety entry) ∨
  (∃ entry, Map.find? Γ.ets ety = .some (.enum entry) ∧
    δ = SymEntityData.ofEnumEntityType ety entry)) ∨
  (∃ uid entry,
    uid.ty = ety ∧
    Map.find? Γ.acts uid = .some entry ∧
    δ = SymEntityData.ofActionType uid.ty
      (List.map (fun x => x.fst.ty) (Map.toList Γ.acts)).eraseDups
      Γ.acts)
:= by
  have := Map.find?_mem_toList hfind
  have := Map.make_mem_list_mem this
  have := List.mem_append.mp this
  cases this with
  | inl hmem_ets =>
    apply Or.inl
    have ⟨⟨ety, entry⟩, hmem_ety_entry, hsym_entry⟩ := List.mem_map.mp hmem_ets
    simp only [Prod.mk.injEq, SymEntityData.ofEntityType] at hsym_entry
    have hwf_ets := wf_env_implies_wf_ets_map hwf
    split at hsym_entry
    · rename_i entry
      have := (Map.in_list_iff_find?_some hwf_ets).mp hmem_ety_entry
      apply Or.inl
      exists entry
      simp [this, ←hsym_entry]
    · rename_i entry
      have := (Map.in_list_iff_find?_some hwf_ets).mp hmem_ety_entry
      apply Or.inr
      exists entry
      simp [this, ←hsym_entry]
  | inr hmem_acts =>
    apply Or.inr
    have ⟨ety', hmem_ety, hsym_act⟩ := List.mem_map.mp hmem_acts
    simp only at hmem_ety
    have := List.mem_eraseDups_implies_mem hmem_ety
    have ⟨⟨uid, entry⟩, hmem_uid_entry, heq_ety⟩ := List.mem_map.mp this
    exists uid, entry
    simp only [Prod.mk.injEq] at hsym_act
    simp only at heq_ety
    have hwf_acts := wf_env_implies_wf_acts_map hwf
    have := (Map.in_list_iff_find?_some hwf_acts).mp hmem_uid_entry
    simp [heq_ety, ←hsym_act, this]

/-- Simplifies `SymEntityData.ofActionType.ancsUDF` -/
theorem ancsUDF_app
  {Γ : TypeEnv} {uid : EntityUID} {entry : ActionSchemaEntry}
  (ancTy : EntityType)
  (hwf : Γ.WellFormed)
  (hfind : Map.find? Γ.acts uid = some entry) :
  Factory.app
      (SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts ancTy)
      (Term.entity uid)
    = SymEntityData.ofActionType.ancsTerm ancTy entry.ancestors.toList
:= by
  simp only [SymEntityData.ofActionType.ancsUDF]
  have hwf_acts := wf_env_implies_wf_acts_map hwf
  apply app_table_make_filterMap hfind
  · simp [SymEntityData.ofActionType.termOfType?]
  · intros kv hkv
    simp only [
      SymEntityData.ofActionType.termOfType?,
      Option.bind_eq_bind,
    ] at hkv
    split at hkv
    · simp only [
        Option.bind_some, Option.some.injEq,
        Prod.mk.injEq, Term.prim.injEq,
        TermPrim.entity.injEq, exists_and_left,
        exists_eq', and_true,
      ] at hkv
      exact hkv
    · simp at hkv
  · simp only [Term.isLiteral]

theorem in_ancsUDF_implies_in_ancestors
  {Γ : TypeEnv} {uid uid' : EntityUID} {ancTy : EntityType}
  (hwf : Γ.WellFormed)
  (hmem : uid' ∈ (Factory.app (SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts ancTy) (Term.entity uid)).entityUIDs) :
  ∃ entry,
    uid'.ty = ancTy ∧
    Map.find? Γ.acts uid = some entry ∧
    uid' ∈ entry.ancestors
:= by
  cases hfind_uid : Map.find? Γ.acts uid with
  | none =>
    simp only [
      SymEntityData.ofActionType.ancsUDF,
      Factory.app,
      Term.isLiteral,
      ↓reduceIte,
    ] at hmem
    split at hmem
    · rename_i heq
      have := Map.find?_mem_toList heq
      have := Map.make_mem_list_mem this
      have ⟨entry, hmem_entry, heq_entry⟩ := List.mem_filterMap.mp this
      simp only [bind, Option.bind] at heq_entry
      split at heq_entry
      contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at heq_entry
      rename_i h
      simp only [
        SymEntityData.ofActionType.termOfType?, heq_entry,
        Option.ite_none_right_eq_some,
        Option.some.injEq, Term.prim.injEq,
        TermPrim.entity.injEq,
      ] at h
      cases entry with | mk a b =>
      simp only at h
      simp only [h.2] at hmem_entry
      have hwf_acts := wf_env_implies_wf_acts_map hwf
      have := (Map.in_list_iff_find?_some hwf_acts).mp hmem_entry
      simp only [this] at hfind_uid
      contradiction
    · simp only [Set.empty, Term.entityUIDs] at hmem
      contradiction
  | some entry =>
    simp only [
      ancsUDF_app ancTy hwf hfind_uid,
      SymEntityData.ofActionType.ancsTerm,
      Factory.setOf,
    ] at hmem
    unfold Term.entityUIDs at hmem
    have ⟨s, hmem_s, hmem_uid'⟩ := (Set.mem_mapUnion_iff_mem_exists _).mp hmem
    replace ⟨s, hmem_s⟩ := s
    have := (Set.make_mem _ _).mpr hmem_s
    have ⟨anc', hmem_anc', hanc'⟩ := List.mem_filterMap.mp this
    simp only [
      SymEntityData.ofActionType.termOfType?,
      Option.ite_none_right_eq_some,
      Option.some.injEq,
    ] at hanc'
    simp only [←hanc'.2, Term.entityUIDs, TermPrim.entityUIDs, Set.singleton] at hmem_uid'
    have := (Set.mem_singleton_iff_eq _ _).mp hmem_uid'
    simp only [←this] at hmem_anc'
    exists entry
    simp only [this, hanc', true_and, true_and]
    simp only [←this]
    exact hmem_anc'

theorem in_ancestors_implies_in_ancsUDF
  {Γ : TypeEnv} {uid uid' : EntityUID} {entry : ActionSchemaEntry}
  (hwf : Γ.WellFormed)
  (hfind : Map.find? Γ.acts uid = some entry)
  (hmem : uid' ∈ entry.ancestors):
  uid' ∈ (Factory.app (SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts uid'.ty) (Term.entity uid)).entityUIDs
:= by
  simp only [
    ancsUDF_app uid'.ty hwf hfind,
    SymEntityData.ofActionType.ancsTerm,
    Factory.setOf,
    Term.entityUIDs,
  ]
  unfold Term.entityUIDs
  apply (Set.mem_mapUnion_iff_mem_exists _).mpr
  simp only [List.mem_attach, true_and, Subtype.exists, exists_prop]
  exists .prim (.entity uid')
  constructor
  · apply (Set.make_mem _ _).mp
    apply List.mem_filterMap.mpr
    exists uid'
    constructor
    · exact hmem
    · simp [SymEntityData.ofActionType.termOfType?]
  · simp only [Term.entityUIDs, TermPrim.entityUIDs]
    exact Set.mem_singleton _

theorem ofEnv_entities_is_acyclic
  {Γ : TypeEnv}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).entities.Acyclic
:= by
  intros uid δ udf hfind_uid_ty hfind_udf_ancs huid_cyclic
  simp only [SymEnv.ofEnv, SymEntities.ofSchema] at hfind_uid_ty
  have := Map.find?_mem_toList hfind_uid_ty
  have := Map.make_mem_list_mem this
  have := List.mem_append.mp this
  cases this with
  | inl hmem_ets =>
    -- Not possible since all `ancs` maps for `ets` are UUFs
    have ⟨⟨ety, entry⟩, hmem_ety_entry, hsym_entry⟩ := List.mem_map.mp hmem_ets
    simp only [Prod.mk.injEq] at hsym_entry
    simp only [
      ←hsym_entry.2,
      SymEntityData.ofEntityType,
      SymEntityData.ofStandardEntityType,
      SymEntityData.ofEnumEntityType,
    ] at hfind_udf_ancs
    split at hfind_udf_ancs
    · simp only at hfind_udf_ancs
      have := Map.find?_mem_toList hfind_udf_ancs
      have := Map.make_mem_list_mem this
      have ⟨_, _, h⟩ := List.mem_map.mp this
      simp [
        Prod.mk.injEq,
        SymEntityData.ofStandardEntityType.ancsUUF,
      ] at h
    · simp [Map.empty, Map.find?, Map.kvs] at hfind_udf_ancs
  | inr hmem_acts =>
    have ⟨ety, hmem_ety, hsym_act⟩ := List.mem_map.mp hmem_acts
    simp only [Prod.mk.injEq, SymEntityData.ofActionType] at hsym_act
    simp only [←hsym_act.2] at hfind_udf_ancs
    have := Map.find?_mem_toList hfind_udf_ancs
    have := Map.make_mem_list_mem this
    have ⟨ancTy, hmem_ancTy, hudf⟩ := List.mem_map.mp this
    have := List.mem_eraseDups_implies_mem hmem_ancTy
    have ⟨⟨anc, entry⟩, hmem_anc, heq_anc⟩ := List.mem_map.mp this
    simp only at heq_anc
    simp only [Prod.mk.injEq] at hudf
    simp only [←hudf.2, hsym_act.1] at huid_cyclic
    have ⟨entry, heq_ancTy, hfind_entry, hanc⟩ := in_ancsUDF_implies_in_ancestors hwf huid_cyclic
    have := wf_env_implies_acyclic_action_hierarchy hwf uid entry hfind_entry hanc
    contradiction

theorem ofEnv_entities_is_transitive
  {Γ : TypeEnv}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).entities.Transitive
:= by
  intros uid₁ δ₁ uid₂ δ₂ hfind_uid₁ hfind_uid₂ hanc
  apply Set.subset_def.mpr
  intros uid huid_anc₂
  have h₁ := ofEnv_entities_find?_some hwf hfind_uid₁
  have h₂ := ofEnv_entities_find?_some hwf hfind_uid₂
  rcases h₁ with (⟨entry₁, hfind_entry₁, hδ₁⟩ | ⟨entry₁, hfind_entry₁, hδ₁⟩) | ⟨uid₁', entry₁', heq_ety₁, hfind_entry₁', hδ₁⟩
  all_goals rcases h₂ with (⟨entry₂, hfind_entry₂, hδ₂⟩ | ⟨entry₂, hfind_entry₂, hδ₂⟩) | ⟨uid₂', entry₂', heq_ety₂, hfind_entry₂', hδ₂⟩
  -- Case: `uid₁` is an enum entity
  all_goals
    simp only [
      hδ₁,
      SymEntityData.ofEnumEntityType,
      SymEntityData.knownAncestors,
    ] at hanc
    try contradiction
  -- Case: `uid₂` is an enum entity
  all_goals
    simp only [
      hδ₂,
      SymEntityData.ofEnumEntityType,
      SymEntityData.knownAncestors,
    ] at huid_anc₂
    try contradiction
  -- Case: `uid₁`: standard; `uid₂`: standard
  -- Case: `uid₁`: action; `uid₂`: standard
  any_goals
    have ⟨⟨ety, f_anc⟩, hmem_ety_f_anc, hmem_uid₁⟩ := (Set.mem_mapUnion_iff_mem_exists _).mp huid_anc₂
    simp only [SymEntityData.ofStandardEntityType ] at hmem_ety_f_anc
    have := Map.make_mem_list_mem hmem_ety_f_anc
    replace ⟨ancTy, hmem_ancTy, heq_ancTy⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq_ancTy
    simp only [
      ←heq_ancTy.2,
      SymEntityData.knownAncestors.ancs,
      SymEntityData.ofStandardEntityType.ancsUUF,
      Set.empty,
    ] at hmem_uid₁
    contradiction
  -- Case: `uid₁`: standard; `uid₂`: action
  · have ⟨⟨ety, f_anc⟩, hmem_ety_f_anc, hmem_uid₂⟩ := (Set.mem_mapUnion_iff_mem_exists _).mp hanc
    simp only [SymEntityData.ofStandardEntityType ] at hmem_ety_f_anc
    have := Map.make_mem_list_mem hmem_ety_f_anc
    replace ⟨ancTy, hmem_ancTy, heq_ancTy⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq_ancTy
    simp only [
      ←heq_ancTy.2,
      SymEntityData.knownAncestors.ancs,
      SymEntityData.ofStandardEntityType.ancsUUF,
      Set.empty,
    ] at hmem_uid₂
    contradiction
  -- Case: `uid₁`: action; `uid₂`: action
  · have ⟨⟨ety₁, f_anc₁⟩, hmem_ety_f_anc₁, hmem_uid₁⟩ := (Set.mem_mapUnion_iff_mem_exists _).mp hanc
    have ⟨⟨ety₂, f_anc₂⟩, hmem_ety_f_anc₂, hmem_uid₂⟩ := (Set.mem_mapUnion_iff_mem_exists _).mp huid_anc₂
    have := Map.make_mem_list_mem hmem_ety_f_anc₁
    replace ⟨ancTy₁, hmem_ancTy₁, heq_ancTy₁⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq_ancTy₁
    simp only [
      ←heq_ancTy₁.2,
      SymEntityData.knownAncestors.ancs,
      Set.empty,
    ] at hmem_uid₁
    replace hmem_uid₁ : uid₂ ∈ (Factory.app
      (SymEntityData.ofActionType.ancsUDF uid₁'.ty Γ.acts ancTy₁)
      (Term.entity uid₁)).entityUIDs
    := by
      split at hmem_uid₁
      contradiction
      rename_i heq
      simp only [Prod.mk.injEq] at heq
      simp only [←heq.2] at hmem_uid₁
      exact hmem_uid₁
    simp only [heq_ety₁] at hmem_uid₁
    have := Map.make_mem_list_mem hmem_ety_f_anc₂
    replace ⟨ancTy₂, hmem_ancTy₂, heq_ancTy₂⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq_ancTy₂
    simp only [
      ←heq_ancTy₂.2,
      SymEntityData.knownAncestors.ancs,
      Set.empty,
    ] at hmem_uid₂
    replace hmem_uid₂ : uid ∈ (Factory.app
      (SymEntityData.ofActionType.ancsUDF uid₂'.ty Γ.acts ancTy₂)
      (Term.entity uid₂)).entityUIDs
    := by
      split at hmem_uid₂
      contradiction
      rename_i heq
      simp only [Prod.mk.injEq] at heq
      simp only [←heq.2] at hmem_uid₂
      exact hmem_uid₂
    simp only [heq_ety₂] at hmem_uid₂
    have ⟨entry₁, heq_uid₂_ty_ancTy₁, hfind_entry₁, huid₂_in_entry₁_anc⟩ := in_ancsUDF_implies_in_ancestors hwf hmem_uid₁
    have ⟨entry₂, heq_uid_ty_ancTy₂, hfind_entry₂, huid_in_entry₂_anc⟩ := in_ancsUDF_implies_in_ancestors hwf hmem_uid₂
    have htrans := wf_env_implies_transitive_action_hierarchy hwf
      uid₁ entry₁ uid₂ entry₂
      hfind_entry₁ hfind_entry₂ huid₂_in_entry₁_anc
    replace htrans := Set.subset_def.mp htrans uid huid_in_entry₂_anc
    simp only [
      SymEntityData.knownAncestors,
      hδ₁, heq_ety₁,
      SymEntityData.ofActionType,
    ]
    apply (Set.mem_mapUnion_iff_mem_exists _).mpr
    exists (uid.ty, SymEntityData.ofActionType.ancsUDF uid₁.ty Γ.acts uid.ty)
    constructor
    · apply (Map.in_list_iff_find?_some (Map.make_wf _)).mpr
      apply Map.make_map_values_find
      apply List.mem_implies_mem_eraseDups
      apply List.mem_map.mpr
      have ⟨entry, hfind_entry, _⟩ := wf_env_implies_wf_action_entity_ancestor hwf hfind_entry₁ htrans
      exists (uid, entry)
      constructor
      · exact (Map.in_list_iff_find?_some (wf_env_implies_wf_acts_map hwf)).mpr hfind_entry
      · rfl
    · simp only [SymEntityData.knownAncestors.ancs]
      have := in_ancestors_implies_in_ancsUDF hwf hfind_entry₁ htrans
      split
      · rename_i heq
        simp [SymEntityData.ofActionType.ancsUDF] at heq
      · rename_i heq
        simp only [Prod.mk.injEq] at heq
        simp only [←heq]
        exact this

theorem ofEnv_entities_is_partitioned
  {Γ : TypeEnv}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).entities.Partitioned
:= by
  constructor
  · intros ety δ hfind_ety
    simp only [SymEntityData.PartitionedAncestors]
    have := ofEnv_entities_find?_some hwf hfind_ety
    cases this with
    | inl hfind_ets =>
      cases hfind_ets with
      | inl hfind_std =>
        have ⟨entry, hfind_std, hstd⟩ := hfind_std
        simp only [
          SymEntityData.isEnum, hstd,
          SymEntityData.ofStandardEntityType,
          Option.isSome_none, Bool.false_eq_true,
          ↓reduceIte,
          SymEntityData.SymbolicAncestors,
        ]
        intros ancTy f hfind_f
        have := Map.find?_mem_toList hfind_f
        replace := Map.make_mem_list_mem this
        have ⟨ancTy', hmem_ancTy', heq_ancTy'⟩ := List.mem_map.mp this
        simp only [Prod.mk.injEq] at heq_ancTy'
        simp only [
          ←heq_ancTy'.2,
          heq_ancTy'.1,
          SymEntityData.ofStandardEntityType.ancsUUF,
          UnaryFunction.isUUF,
        ]
      | inr hfind_enum =>
        have ⟨entry, hfind_std, henum⟩ := hfind_enum
        simp only [
          SymEntityData.isEnum, henum,
          SymEntityData.ofEnumEntityType,
          Option.isSome_some,
          ↓reduceIte,
          SymEntityData.ConcreteAncestors,
        ]
        intros ancTy f hfind_f
        simp [Map.empty, Map.find?, Map.kvs] at hfind_f
    | inr hfind_acts =>
      have ⟨uid, entry, heq_ety, hfind_uid, hact⟩ := hfind_acts
      simp only [
        SymEntityData.isEnum, hact,
        SymEntityData.ofActionType, Option.isSome_some,
        ↓reduceIte,
        SymEntityData.ConcreteAncestors,
      ]
      intros ancTy f hfind_f
      have := Map.find?_mem_toList hfind_f
      replace := Map.make_mem_list_mem this
      have ⟨ancTy', hmem_ancTy', heq_ancTy'⟩ := List.mem_map.mp this
      simp only [Prod.mk.injEq] at heq_ancTy'
      simp only [
        ←heq_ancTy'.2,
        heq_ancTy'.1,
        SymEntityData.ofActionType.ancsUDF,
        UnaryFunction.isUDF,
      ]
  · intros ety₁ δ₁ f ety₂ δ₂ hfind₁ hfind₂ hanc
    have h₁ := ofEnv_entities_find?_some hwf hfind₁
    have h₂ := ofEnv_entities_find?_some hwf hfind₂
    rcases h₁ with (⟨entry₁, hfind_entry₁, hδ₁⟩ | ⟨entry₁, hfind_entry₁, hδ₁⟩) | ⟨uid₁, entry₁, heq_ety₁, hfind_entry₁, hδ₁⟩
    all_goals rcases h₂ with (⟨entry₂, hfind_entry₂, hδ₂⟩ | ⟨entry₂, hfind_entry₂, hδ₂⟩) | ⟨uid₂, entry₂, heq_ety₂, hfind_entry₂, hδ₂⟩
    any_goals simp only [
      hδ₁, hδ₂,
      SymEntityData.isEnum,
      SymEntityData.ofStandardEntityType,
      SymEntityData.ofEnumEntityType,
      SymEntityData.ofActionType,
      Option.isSome,
    ]
    all_goals
      simp only [
        hδ₁,
        SymEntityData.ofEnumEntityType,
        SymEntityData.ofActionType,
      ] at hanc
    any_goals
      try · simp [Map.empty, Map.find?, Map.kvs] at hanc
    -- entry₁: standard; entry₂: enum
    · have hancs_std_only := wf_env_implies_ancestors_of_standard_ety_is_standard hwf hfind_entry₁ ety₂
      simp only [SymEntityData.ofStandardEntityType] at hanc
      have := Map.find?_mem_toList hanc
      replace := Map.make_mem_list_mem this
      have ⟨ancTy, hmem_ancTy, heq_ancTy⟩ := List.mem_map.mp this
      simp only [Prod.mk.injEq] at heq_ancTy
      simp only [heq_ancTy.1] at hmem_ancTy
      specialize hancs_std_only hmem_ancTy
      simp [hfind_entry₂, EntitySchemaEntry.isStandard] at hancs_std_only
    -- entry₁: standard; entry₂: action
    · have hancs_std_only := wf_env_implies_ancestors_of_standard_ety_is_standard hwf hfind_entry₁ ety₂
      simp only [SymEntityData.ofStandardEntityType] at hanc
      have := Map.find?_mem_toList hanc
      replace := Map.make_mem_list_mem this
      have ⟨ancTy, hmem_ancTy, heq_ancTy⟩ := List.mem_map.mp this
      simp only [Prod.mk.injEq] at heq_ancTy
      simp only [heq_ancTy.1] at hmem_ancTy
      have ⟨_, h, _⟩ := hancs_std_only hmem_ancTy
      simp only [←heq_ety₂] at h
      have := wf_env_disjoint_ets_acts hwf h hfind_entry₂
      contradiction
    -- entry₁: action; entry₂: standard
    · have := Map.find?_mem_toList hanc
      replace := Map.make_mem_list_mem this
      have ⟨ancTy, hmem_ancTy, heq_ancTy⟩ := List.mem_map.mp this
      simp only [Prod.mk.injEq] at heq_ancTy
      have := List.mem_eraseDups_implies_mem hmem_ancTy
      have ⟨⟨anc, entry⟩, hmem_anc, heq_anc⟩ := List.mem_map.mp this
      simp only at heq_anc
      simp only [←heq_ancTy.1, ←heq_anc] at hfind_entry₂
      have hwf_acts := wf_env_implies_wf_acts_map hwf
      have := (Map.in_list_iff_find?_some hwf_acts).mp hmem_anc
      have := wf_env_disjoint_ets_acts hwf hfind_entry₂ this
      contradiction

theorem ofEnv_entities_is_hierarchical
  {Γ : TypeEnv}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).entities.Hierarchical
:= by
  constructor
  · exact ofEnv_entities_is_acyclic hwf
  constructor
  · exact ofEnv_entities_is_transitive hwf
  · exact ofEnv_entities_is_partitioned hwf

theorem ofEnv_entities_is_swf
  {Γ : TypeEnv}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).entities.StronglyWellFormed
:= by
  constructor
  exact ofEnv_entities_is_wf hwf
  exact ofEnv_entities_is_hierarchical hwf

/--
Main well-formedness theorem for `SymEnv.ofEnv`,
which says that if the input environment `Γ` is well-formed,
then `SymEnv.ofEnv Γ` is well-formed.
-/
theorem ofEnv_is_wf
  {Γ : TypeEnv}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).WellFormed
:= by
  simp only [SymEnv.WellFormed]
  constructor
  · exact (ofEnv_request_is_swf hwf).1
  · exact ofEnv_entities_is_wf hwf

/--
A stronger version of `ofEnv_is_wf` that
shows that `SymEnv.ofEnv Γ` is strongly well-formed.
-/
theorem ofEnv_is_swf
  {Γ : TypeEnv}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).StronglyWellFormed
:= by
  simp only [SymEnv.StronglyWellFormed]
  constructor
  exact ofEnv_request_is_swf hwf
  exact ofEnv_entities_is_swf hwf

/--
If an expression is well-typed in a concrete, well-formed `TypeEnv`,
then it must also be well-formed in the compiled symbolic environment.
-/
theorem ofEnv_wf_for_expr
  {Γ : TypeEnv} {tx : TypedExpr}
  (hwf : Γ.WellFormed)
  (hwt : TypedExpr.WellTyped Γ tx) :
  (SymEnv.ofEnv Γ).WellFormedFor tx.toExpr
:= by
  constructor
  · exact ofEnv_is_wf hwf
  · exact ofEnv_entities_valid_refs_for_wt_expr hwf hwt

end Cedar.Thm
