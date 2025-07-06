import Cedar.Thm.Validation.Typechecker.WF
import Cedar.Thm.Validation.WellTyped.TypeLifting
import Cedar.Thm.SymCC.Data.Hierarchy
import Cedar.Thm.SymCC.Env.WF
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
  {Γ : Environment} {εnv : SymEnv} {ety : EntityType} {entry : EntitySchemaEntry}
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

theorem map_make_append_find_disjoint
  [LT α] [StrictLT α] [DecidableEq α] [DecidableLT α]
  [SizeOf α] [SizeOf β]
  {l₁ : List (α × β)} {l₂ : List (α × β)} {k : α}
  (hfind₁ : l₁.find? (λ ⟨k', _⟩ => k' == k) = none)
  (hfind₂ : (l₂.find? (λ ⟨k', _⟩ => k' == k)).isSome) :
  ∃ v,
    (Map.make (l₁ ++ l₂)).find? k = some v ∧
    (k, v) ∈ l₂
:= by
  have hwf : (Map.make (l₁ ++ l₂)).WellFormed := by
    exact Map.make_wf _
  have hsub :
    (Map.make (l₁ ++ l₂)).kvs ⊆ l₁ ++ l₂
  := by
    apply List.canonicalize_subseteq
  simp [Subset, List.Subset] at hsub
  have ⟨v, hv⟩ :
    ∃ v, (Map.make (l₁ ++ l₂)).find? k = some v
  := by
    simp only [Option.isSome] at hfind₂
    split at hfind₂
    rotate_left
    contradiction
    rename_i kv hkv
    exists kv.snd
    apply Map.find?_implies_make_find?
    simp [List.find?_append]
    apply Or.inr
    constructor
    · simp only [List.find?_eq_none, beq_iff_eq, Prod.forall] at hfind₁
      exact hfind₁
    have := List.find?_some hkv
    simp only [beq_iff_eq] at this
    simp only [hkv]
    simp [←this]
  simp only [hv, Option.some.injEq, exists_eq_left']
  have := Map.find?_mem_toList hv
  have := hsub k v this
  cases this with
  | inl hmem₁ =>
    have := List.find?_eq_none.mp hfind₁
    specialize this (k, v) hmem₁
    simp at this
  | inr h => exact h

/-- An action entity type is compiled correctly -/
theorem ofEnv_preserves_action_entity
  {Γ : Environment} {uid : EntityUID}
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
  have ⟨_, hfind, hmem⟩ := map_make_append_find_disjoint hfind₁ hfind₂
  simp only [hfind, Option.some.injEq]
  have ⟨_, _, heq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at heq
  have ⟨heq_uid_ty, heq⟩ := heq
  simp only [heq_uid_ty] at heq
  simp [heq]

theorem ofActionType_contains_act
  {Γ : Environment} {uid : EntityUID}
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
  {Γ : Environment} {ety : EntityType}
  (hmem : Map.contains Γ.ets ety) :
  Map.contains (SymEnv.ofEnv Γ).entities ety
:= by
  apply Map.contains_iff_some_find?.mpr
  have ⟨entry, hentry⟩ := Map.contains_iff_some_find?.mp hmem
  exists (SymEntityData.ofEntityType ety entry)
  exact ofEnv_preserves_entity rfl hentry

/-- Similar to `ofEnv_entity_exists` but for action entities -/
theorem ofEnv_action_entity_exists
  {Γ : Environment} {uid : EntityUID}
  (hwf : Γ.WellFormed)
  (hmem : Map.contains Γ.acts uid) :
  Map.contains (SymEnv.ofEnv Γ).entities uid.ty
:= by
  apply Map.contains_iff_some_find?.mpr
  simp [ofEnv_preserves_action_entity hwf hmem]

theorem ofEnv_wf_entity
  {Γ : Environment} {ety : EntityType}
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
  {Γ : Environment} {εnv : SymEnv}
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
  {Γ : Environment} {ty : CedarType}
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
  {Γ : Environment} {ty : CedarType}
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
  {Γ : Environment}
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
  {Γ : Environment} :
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
  {Γ : Environment}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).request.StronglyWellFormed
    (SymEnv.ofEnv Γ).entities
:= by
  simp only [SymRequest.StronglyWellFormed]
  constructor
  exact ofEnv_request_is_wf hwf
  exact ofEnv_request_is_basic

theorem ofEnv_entities_is_swf
  {Γ : Environment}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).entities.StronglyWellFormed
:= by
  sorry

/--
Main well-formedness theorem for `SymEnv.ofEnv`,
which says that if the input environment `Γ` is well-formed,
then `SymEnv.ofEnv Γ` is strongly well-formed.
-/
theorem ofEnv_is_swf
  {Γ : Environment}
  (hwf : Γ.WellFormed) :
  (SymEnv.ofEnv Γ).StronglyWellFormed
:= by
  simp only [SymEnv.StronglyWellFormed]
  constructor
  exact ofEnv_request_is_swf hwf
  exact ofEnv_entities_is_swf hwf

end Cedar.Thm
