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

import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymCC.Term.Interpret.WF
import Cedar.Thm.SymCC.Term.ofType

/-!
This file contains the soundness theorems of `Sym.ofEnv`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Spec
open Cedar.SymCC
open Cedar.Validation
open Cedar.Data

/--
Inverse of `entity_uid_wf_implies_sym_entities_is_valid_entity_uid`
-/
theorem sym_entities_is_valid_entity_uid_implies_entity_uid_wf
  {Γ : TypeEnv} {uid : EntityUID}
  (hwf : Γ.WellFormed)
  (huid : (SymEnv.ofEnv Γ).entities.isValidEntityUID uid) :
  EntityUID.WellFormed Γ uid
:= by
  simp only [
    SymEnv.ofEnv,
    SymEntities.ofSchema,
    SymEntities.isValidEntityUID,
  ] at huid
  have hwf_ets := wf_env_implies_wf_ets_map hwf
  have hwf_acts := wf_env_implies_wf_acts_map hwf
  split at huid
  · rename_i δ hfind
    have := Map.find?_mem_toList hfind
    have := Map.make_mem_list_mem this
    have := List.mem_append.mp this
    cases this with
    | inl hmem =>
      left
      have ⟨⟨ety, entry⟩, hmem_ety, hety⟩ := List.mem_map.mp hmem
      simp only [Prod.mk.injEq] at hety
      simp only [EntitySchema.isValidEntityUID]
      have := (Map.in_list_iff_find?_some hwf_ets).mp hmem_ety
      simp only [hety.1] at this
      simp only [this, EntitySchemaEntry.isValidEntityEID]
      split
      · rfl
      · rename_i eids
        simp only [SymEntityData.ofEntityType, SymEntityData.ofEnumEntityType] at hety
        simp only [←hety.2] at huid
        exact huid
    | inr hmem =>
      right
      have ⟨actTy, hmem_actTy, hactTy⟩ := List.mem_map.mp hmem
      have := List.mem_eraseDups_implies_mem hmem_actTy
      have ⟨⟨act, entry⟩, hmem_act, hact⟩ := List.mem_map.mp this
      simp only at hact
      simp only [SymEntityData.ofActionType, Prod.mk.injEq] at hactTy
      simp only [←hactTy.2, SymEntityData.ofActionType.acts] at huid
      have := Set.contains_prop_bool_equiv.mp huid
      have := (Set.make_mem _ _).mpr this
      have ⟨⟨act', entry'⟩, hmem_act', hact'⟩ := List.mem_filterMap.mp this
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hact'
      have : act' = uid := by
        cases act' with | mk ty' eid' =>
        cases uid with | mk ty eid =>
        simp only at hact'
        simp only at hactTy
        congr
        simp only [hactTy, hact']
        simp only [hact']
      simp only [this] at hmem_act'
      have := (Map.in_list_iff_find?_some hwf_acts).mp hmem_act'
      simp only [ActionSchema.contains, Map.contains, this, Option.isSome]
  · contradiction

/-- `TermPrim` case of `ofType_typeOf_pullback`. -/
theorem ofType_typeOf_pullback_prim
  {Γ : TypeEnv}
  {p : TermPrim} {ty : CedarType} {v : Value}
  (hwf_Γ : Γ.WellFormed)
  (hwf_ty : ty.WellFormed Γ)
  (hlift_ty : ty.IsLifted)
  (hwf_t : (Term.prim p).WellFormed (SymEnv.ofEnv Γ).entities)
  (heq_ty : (Term.prim p).typeOf = TermType.ofType ty)
  (hval : (Term.prim p).value? = .some v) :
  InstanceOfType Γ v ty
:= by
  cases p with
  | bool b =>
    simp only [Term.typeOf, TermPrim.typeOf, TermType.bool] at heq_ty
    unfold TermType.ofType at heq_ty
    split at heq_ty
    rename_i bty
    cases hlift_ty
    any_goals simp only [TermType.prim.injEq, reduceCtorEq] at heq_ty
    simp only [Term.value?, TermPrim.value?, Option.some.injEq] at hval
    simp only [←hval]
    constructor
    simp [InstanceOfBoolType]
  | bitvec bv =>
    rename_i n
    simp only [Term.typeOf, TermPrim.typeOf, TermType.bitvec, BitVec.width] at heq_ty
    unfold TermType.ofType at heq_ty
    split at heq_ty
    any_goals simp only [TermType.prim.injEq, TermPrimType.bitvec.injEq, reduceCtorEq] at heq_ty
    simp only [
      Term.value?, TermPrim.value?, BitVec.int64?,
      heq_ty, ↓reduceIte, Option.pure_def,
      Option.bind_some_fun, Option.some.injEq,
    ] at hval
    simp only [←hval]
    constructor
  | string =>
    simp only [Term.typeOf, TermPrim.typeOf, TermType.string] at heq_ty
    unfold TermType.ofType at heq_ty
    split at heq_ty
    any_goals simp only [TermType.prim.injEq, reduceCtorEq] at heq_ty
    simp only [Term.value?, TermPrim.value?, Option.some.injEq] at hval
    simp only [←hval]
    constructor
  | entity uid =>
    simp only [Term.typeOf, TermPrim.typeOf, TermType.entity] at heq_ty
    unfold TermType.ofType at heq_ty
    split at heq_ty
    any_goals simp only [TermType.prim.injEq, TermPrimType.entity.injEq, reduceCtorEq] at heq_ty
    simp only [Term.value?, TermPrim.value?, Option.some.injEq] at hval
    simp only [←hval]
    constructor
    simp only [←heq_ty, InstanceOfEntityType, true_and]
    cases hwf_t with | prim_wf hwf_t =>
    cases hwf_t with | entity_wf hwf_t =>
    exact sym_entities_is_valid_entity_uid_implies_entity_uid_wf hwf_Γ hwf_t
  | ext =>
    simp only [Term.typeOf, TermPrim.typeOf] at heq_ty
    split at heq_ty
    any_goals contradiction
    all_goals
      unfold TermType.ofType at heq_ty
      rename_i hp
      split at heq_ty
      any_goals simp only [TermType.prim.injEq, reduceCtorEq] at heq_ty
      simp only [Term.value?, TermPrim.value?, Option.some.injEq] at hval
      injection heq_ty with heq_ty
      injection hp with hp
      simp only [←hval, ←heq_ty, hp]
      constructor
      simp only [InstanceOfExtType]

theorem value?_some_implies_typeOf_not_option
  {t : Term} {v : Value} {ty : TermType}
  (hsome : t.value? = .some v)
  (hopt : t.typeOf = .option ty) :
  False
:= by
  cases t with
  | prim p =>
    cases p with
    | ext =>
      simp only [Term.typeOf, TermPrim.typeOf] at hopt
      split at hopt
      all_goals contradiction
    | _ =>
      simp only [Term.typeOf, TermPrim.typeOf] at hopt
      contradiction
  | record =>
    unfold Term.typeOf at hopt
    contradiction
  | _ =>
    try simp only [Term.value?] at hsome
    try simp only [Term.typeOf] at hopt
    contradiction

/--
If a term type is both the result of `TermType.ofType` and `Term.typeOf`
for some well-formed `CedarType` and well-formed `Term`,
then the if the the term is conretizable (via `value?`),
the resulting `Value` should be well-typed.

i.e., if we know "--->"'s below,
then we know "***>", such that the
diagram "commutes."

         ofType
TermType <----- CedarType
   ^               ^
   |               *
   | typeOf        * InstanceOfType
   |               *
   |               *
 Term ---------> Value
        value?
-/
theorem ofType_typeOf_pullback
  {Γ : TypeEnv}
  {t : Term} {ty : CedarType} {v : Value}
  (hwf_Γ : Γ.WellFormed)
  (hwf_ty : ty.WellFormed Γ)
  (hlift_ty : ty.IsLifted)
  (hwf_t : t.WellFormed (SymEnv.ofEnv Γ).entities)
  (heq_ty : t.typeOf = TermType.ofType ty)
  (hval : t.value? = .some v) :
  InstanceOfType Γ v ty
:= by
  cases t with
  | prim p => exact ofType_typeOf_pullback_prim hwf_Γ hwf_ty hlift_ty hwf_t heq_ty hval
  | var var | none | some | app =>
    simp only [Term.value?] at hval
    contradiction
  | set ts ty' =>
    cases ts with | mk ts_set =>
    simp only [Term.value?, bind, Option.bind] at hval
    split at hval
    contradiction
    simp only [Option.some.injEq] at hval
    rename_i val_ts hval_ts
    simp only [List.mapM₁_eq_mapM] at hval_ts
    simp only [Term.typeOf] at heq_ty
    unfold TermType.ofType at heq_ty
    split at heq_ty
    any_goals contradiction
    rename_i ty_ts
    injection heq_ty with heq_ty
    cases hlift_ty with | set_wf hlift_ty_ts =>
    cases hwf_ty with | set_wf hwf_ty_ts =>
    cases hwf_t with | set_wf hwf_ts heq_ty_ts =>
    simp only [←hval]
    constructor
    intros v_ts hmem_v_ts
    have ⟨t', hmem_t', hval_t'⟩ := List.mapM_some_implies_all_from_some
      hval_ts v_ts ((Set.make_mem _ _).mpr hmem_v_ts)
    have hwf_t' := hwf_ts t' hmem_t'
    apply ofType_typeOf_pullback hwf_Γ hwf_ty_ts hlift_ty_ts hwf_t' _ hval_t'
    have heq_ty_t' := heq_ty_ts t' hmem_t'
    simp only [heq_ty_t', ←heq_ty]
  | record rec =>
    cases rec with | mk rec_map =>
    simp only [Term.value?, bind, Option.bind] at hval
    split at hval
    contradiction
    simp only [Option.some.injEq] at hval
    rename_i val_rec hval_rec
    simp only [List.mapM₂_eq_mapM (λ x => Term.value?.attrValue? x.fst x.snd)] at hval_rec
    simp only [Term.typeOf] at heq_ty
    unfold TermType.ofType at heq_ty
    split at heq_ty
    any_goals contradiction
    simp only [TermType.record.injEq, Map.mk.injEq] at heq_ty
    rename_i ty_rec
    cases hlift_ty with | record_wf hlift_ty_rec =>
    cases hwf_ty with | record_wf hwf_ty_rec_map hwf_ty_rec =>
    cases hwf_t with | record_wf hwf_rec heq_ty_rec =>
    simp only [←hval]
    simp only [List.map_attach₃_snd] at heq_ty
    constructor
    · intros attr hcont_attr
      have ⟨v, hfind_v⟩ := Map.contains_iff_some_find?.mp hcont_attr
      have hmem_v := Map.find?_mem_toList hfind_v
      simp only [Map.toList, Map.kvs] at hmem_v
      have ⟨attr_v, hmem_attr_v, hattr_v⟩ := List.mem_filterMap.mp hmem_v
      have ⟨attr_t', hmem_attr_t', hattr_t'⟩ := List.mapM_some_implies_all_from_some hval_rec attr_v hmem_attr_v
      have : (attr_t'.fst, attr_t'.snd.typeOf) ∈ TermType.ofRecordType ty_rec
      := by
        simp only [←heq_ty]
        apply List.mem_map.mpr
        exists attr_t'
      simp only [ofRecordType_as_map ty_rec] at this
      have ⟨attr_ty, hmem_attr_ty, hattr_ty⟩ := List.mem_map.mp this
      have : attr = attr_v.fst := by
        simp only [Option.map] at hattr_v
        split at hattr_v
        · simp only [Option.some.injEq, Prod.mk.injEq] at hattr_v
          simp [hattr_v.1]
        · contradiction
      have : attr = attr_t'.fst := by
        simp only [this]
        unfold Term.value?.attrValue? at hattr_t'
        split at hattr_t'
        · simp only [bind, Option.bind] at hattr_t'
          split at hattr_t'
          contradiction
          simp only [Option.some.injEq] at hattr_t'
          simp only [←hattr_t']
        · simp only [Option.some.injEq] at hattr_t'
          simp only [←hattr_t']
        · simp only [bind, Option.bind] at hattr_t'
          split at hattr_t'
          contradiction
          simp only [Option.some.injEq] at hattr_t'
          simp only [←hattr_t']
      have : attr = attr_ty.fst := by
        simp only [this]
        simp only [Prod.mk.injEq] at hattr_ty
        simp only [hattr_ty.1]
      simp only [this]
      apply Map.contains_iff_some_find?.mpr
      exists attr_ty.snd
      apply (Map.in_list_iff_find?_some hwf_ty_rec_map).mp
      exact hmem_attr_ty
    -- Simplify both sides of `heq_ty` to `Map.mapOnValues`
    all_goals
      have :
        TermType.ofRecordType ty_rec
        = (Map.mapOnValues TermType.ofQualifiedType (Map.mk ty_rec)).toList
      := by
        simp only [ofRecordType_as_map]
        rfl
      simp only [this] at heq_ty
      have :
        List.map (fun x => (x.fst, x.snd.typeOf)) rec_map
        = (Map.mapOnValues Term.typeOf (Map.mk rec_map)).toList
      := by rfl
      simp only [this] at heq_ty
      replace heq_ty := Map.toList_congr heq_ty
    · intros attr val qty hfind_val hfind_qty
      have hwf_ty' := hwf_ty_rec attr qty hfind_qty
      have hlift_ty' := hlift_ty_rec attr qty (Map.find?_mem_toList hfind_qty)
      have := Map.find?_mem_toList hfind_val
      have ⟨attr_v, hmem_attr_v, hattr_v⟩ := List.mem_filterMap.mp this
      have ⟨attr_t', hmem_attr_t', hattr_t'⟩ := List.mapM_some_implies_all_from_some hval_rec attr_v hmem_attr_v
      simp only [Option.map] at hattr_v
      have heq_attr : attr = attr_t'.fst := by
        split at hattr_v
        · simp only [Option.some.injEq, Prod.mk.injEq] at hattr_v
          simp only [←hattr_v.1]
          unfold Term.value?.attrValue? at hattr_t'
          split at hattr_t'
          · simp only [bind, Option.bind] at hattr_t'
            split at hattr_t'
            contradiction
            simp only [Option.some.injEq] at hattr_t'
            simp only [←hattr_t']
          · simp only [Option.some.injEq] at hattr_t'
            simp only [←hattr_t']
          · simp only [bind, Option.bind] at hattr_t'
            split at hattr_t'
            contradiction
            simp only [Option.some.injEq] at hattr_t'
            simp only [←hattr_t']
        · contradiction
      split at hattr_v
      · rename_i v hv
        unfold Term.value?.attrValue? at hattr_t'
        split at hattr_t'
        · rename_i attr_t'' hattr_t''
          simp only [bind, Option.bind] at hattr_t'
          split at hattr_t'
          contradiction
          rename_i v' hv'
          have hwf_t' := hwf_rec attr_t'.fst attr_t'.snd hmem_attr_t'
          simp only [Qualified.getType]
          simp only [Option.some.injEq] at hattr_t'
          simp only [←hattr_t', Option.some.injEq] at hv
          simp only [hv] at hv'
          simp only [Option.some.injEq, Prod.mk.injEq] at hattr_v
          simp only [hattr_v.2] at hv'
          simp only [hattr_t''] at hwf_t'
          cases hwf_t'
          rename_i hwf_t'
          have := (Map.in_list_iff_find?_some heq_ty_rec).mp hmem_attr_t'
          have h₁ := Map.find?_mapOnValues_some Term.typeOf this
          simp only [heq_ty] at h₁
          have h₂ := Map.find?_mapOnValues_some TermType.ofQualifiedType hfind_qty
          simp only [heq_attr] at h₂
          simp only [h₁, Option.some.injEq, hattr_t'', Term.typeOf] at h₂
          cases qty with
          | optional ty' =>
            cases hwf_ty'
            rename_i hwf_ty'
            cases hlift_ty'
            rename_i hlift_ty'
            simp only [TermType.ofQualifiedType, TermType.option.injEq] at h₂
            apply ofType_typeOf_pullback hwf_Γ hwf_ty' hlift_ty' hwf_t' h₂ hv'
          | required ty' =>
            simp only [TermType.ofQualifiedType] at h₂
            unfold TermType.ofType at h₂
            split at h₂
            all_goals contradiction
        · simp only [Option.some.injEq] at hattr_t'
          simp [←hattr_t'] at hv
        · simp only [bind, Option.bind] at hattr_t'
          split at hattr_t'
          contradiction
          rename_i v' hv'
          have hwf_t' := hwf_rec attr_t'.fst attr_t'.snd hmem_attr_t'
          simp only [Qualified.getType]
          simp only [Option.some.injEq] at hattr_t'
          simp only [←hattr_t', Option.some.injEq] at hv
          simp only [hv] at hv'
          simp only [Option.some.injEq, Prod.mk.injEq] at hattr_v
          simp only [hattr_v.2] at hv'
          have := (Map.in_list_iff_find?_some heq_ty_rec).mp hmem_attr_t'
          have h₁ := Map.find?_mapOnValues_some Term.typeOf this
          simp only [Map.find?, heq_ty] at h₁
          have h₂ := Map.find?_mapOnValues_some TermType.ofQualifiedType hfind_qty
          simp only [Map.find?, heq_attr] at h₂
          simp only [h₁, Option.some.injEq, TermType.ofQualifiedType] at h₂
          cases qty with
          | optional ty' =>
            simp only [TermType.ofQualifiedType, TermType.option.injEq] at h₂
            have := value?_some_implies_typeOf_not_option hv' h₂
            contradiction
          | required ty' =>
            cases hwf_ty'
            rename_i hwf_ty'
            cases hlift_ty'
            rename_i hlift_ty'
            exact ofType_typeOf_pullback hwf_Γ hwf_ty' hlift_ty' hwf_t' h₂ hv'
      · contradiction
    · intros attr qty hfind_qty hreq
      cases qty with
      | optional ty' => contradiction
      | required ty' =>
      have := Map.find?_mapOnValues_some TermType.ofQualifiedType hfind_qty
      simp only [←heq_ty] at this
      have ⟨v, hfind_v, hv⟩ := Map.find?_mapOnValues_some' _ this
      simp only [TermType.ofQualifiedType] at hv
      have := Map.find?_mem_toList hfind_v
      have ⟨v', hfind_v', hv'⟩ := List.mapM_some_implies_all_some hval_rec (attr, v) this
      simp only at hv'
      unfold Term.value?.attrValue? at hv'
      split at hv'
      · simp only [Term.typeOf] at hv
        unfold TermType.ofType at hv
        split at hv
        all_goals contradiction
      · simp only [Term.typeOf] at hv
        unfold TermType.ofType at hv
        split at hv
        all_goals contradiction
      · simp only [bind, Option.bind] at hv'
        split at hv'
        contradiction
        rename_i v'' hv''
        simp only [Option.some.injEq] at hv'
        apply Map.in_list_implies_contains (v := v'')
        simp only [Map.kvs]
        apply List.mem_filterMap.mpr
        exists v'
        simp only [hfind_v', true_and]
        simp only [←hv', Option.map]
termination_by sizeOf t
decreasing_by
  · rename t = Term.set ts ty' => h₁
    rename ts = Set.mk ts_set => h₂
    simp [h₁, h₂]
    have := List.sizeOf_lt_of_mem hmem_t'
    omega
  · rename t = Term.record rec => h₃
    rename rec = Map.mk rec_map => h₄
    rename Term => t''
    simp [h₃, h₄]
    rename attr_t'.snd = _ => h₅
    rename _ = t'' => h₆
    simp only [h₆] at h₅ ⊢
    calc sizeOf t''
      _ < 1 + sizeOf t'' := by omega
      _ ≤ sizeOf t''.some := by simp
      _ = sizeOf attr_t'.snd := by simp [h₅]
      _ < sizeOf attr_t' := by
        cases attr_t'
        simp
        omega
      _ < 1 + (1 + sizeOf rec_map) := by
        have := List.sizeOf_lt_of_mem hmem_attr_t'
        omega
  · rename t = Term.record rec => h₃
    rename rec = Map.mk rec_map => h₄
    rename Term => t''
    simp [h₃, h₄]
    rename attr_t'.snd = t'' => h₅
    have := List.sizeOf_lt_of_mem hmem_attr_t'
    simp only [h₅] at ⊢ this
    calc sizeOf t''
      _ = sizeOf attr_t'.snd := by simp [h₅]
      _ < sizeOf attr_t' := by
        cases attr_t'
        simp
        omega
      _ < 1 + (1 + sizeOf rec_map) := by
        have := List.sizeOf_lt_of_mem hmem_attr_t'
        omega

theorem ofEnv_request_completeness
  {Γ : TypeEnv} {env : Env} {I : Interpretation}
  (hwf_Γ : Γ.WellFormed)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hsame_I : env ∼ SymEnv.interpret I (SymEnv.ofEnv Γ)) :
  InstanceOfRequestType env.request Γ
:= by
  have ⟨hwf_I_vars, _⟩ := hwf_I
  have ⟨⟨hsame_I_princ, hsame_I_act, hsame_I_res, hsame_I_ctx⟩, _⟩ := hsame_I
  have hwf_sym_req := ofEnv_request_is_swf hwf_Γ
  have ⟨⟨hwf_sym_princ, _, hwf_sym_act, _, hwf_sym_res, _, hwf_sym_ctx, _⟩, _⟩ := hwf_sym_req
  simp only [
    SymEnv.interpret,
    SymRequest.interpret,
  ] at hsame_I_princ hsame_I_act hsame_I_res hsame_I_ctx
  and_intros
  -- Well-formed symbolic principal => well-formed concrete principal
  · have ⟨_, hwt_I_princ⟩ := interpret_term_wf hwf_I hwf_sym_princ
    simp only [hsame_I_princ, Term.typeOf, TermPrim.typeOf] at hwt_I_princ
    simp only [
      SymEnv.ofEnv,
      SymRequest.ofRequestType,
      Term.typeOf,
      TermType.ofType,
    ] at hwt_I_princ
    simp only [TermType.prim.injEq, TermPrimType.entity.injEq] at hwt_I_princ
    simp [hwt_I_princ]
  · have ⟨hwf_I_princ, _⟩ := interpret_term_wf hwf_I hwf_sym_princ
    simp only [hsame_I_princ] at hwf_I_princ
    cases hwf_I_princ with | prim_wf hwf_I_princ =>
    cases hwf_I_princ with | entity_wf hwf_I_princ =>
    exact sym_entities_is_valid_entity_uid_implies_entity_uid_wf hwf_Γ hwf_I_princ
  -- Well-formed symbolic action => well-formed concrete action
  · simp only [
      Term.interpret,
      SymEnv.ofEnv,
      SymRequest.ofRequestType,
    ] at hsame_I_act
    simp only [Term.prim.injEq, TermPrim.entity.injEq] at hsame_I_act
    simp [hsame_I_act]
  -- Well-formed symbolic resource => well-formed concrete resource
  · have ⟨_, hwt_I_res⟩ := interpret_term_wf hwf_I hwf_sym_res
    simp only [hsame_I_res, Term.typeOf, TermPrim.typeOf] at hwt_I_res
    simp only [
      SymEnv.ofEnv,
      SymRequest.ofRequestType,
      Term.typeOf,
      TermType.ofType,
    ] at hwt_I_res
    simp only [TermType.prim.injEq, TermPrimType.entity.injEq] at hwt_I_res
    simp [hwt_I_res]
  · have ⟨hwf_I_res, _⟩ := interpret_term_wf hwf_I hwf_sym_res
    simp only [hsame_I_res] at hwf_I_res
    cases hwf_I_res with | prim_wf hwf_I_res =>
    cases hwf_I_res with | entity_wf hwf_I_res =>
    exact sym_entities_is_valid_entity_uid_implies_entity_uid_wf hwf_Γ hwf_I_res
  · have ⟨hwf_I_ctx, hwt_I_ctx⟩ := interpret_term_wf hwf_I hwf_sym_ctx
    simp only [
      SymEnv.ofEnv,
      SymRequest.ofRequestType,
      Term.typeOf,
    ] at hwt_I_ctx
    simp only [
      SameValues,
      SymEnv.ofEnv,
      SymRequest.ofRequestType,
    ] at hsame_I_ctx
    have ⟨_, _, _, hwt_ctx⟩ := wf_env_implies_wf_request hwf_Γ
    have hlifted_ctx := wf_env_implies_ctx_lifted hwf_Γ
    apply ofType_typeOf_pullback hwf_Γ hwt_ctx hlifted_ctx hwf_I_ctx hwt_I_ctx hsame_I_ctx

theorem ofEnv_entity_completeness_standard
  {Γ : TypeEnv} {I : Interpretation} {entities : Entities}
  {uid : EntityUID} {entry : StandardSchemaEntry}
  {δ δ' : SymEntityData} {data : EntityData}
  (hwf_Γ : Γ.WellFormed)
  (hwf_data : data.WellFormed entities)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hfind_uid : Γ.ets.find? uid.ty = .some (.standard entry))
  (hδ' : δ' = SymEntityData.ofEntityType uid.ty (.standard entry))
  (hδ : δ = SymEntityData.interpret I δ')
  (hsame_δ : SameEntityData uid data δ) :
  InstanceOfEntitySchemaEntry uid data Γ
:= by
  have ⟨hsame_attrs, _, _, hvalid_eid, _⟩ := hsame_δ
  have ⟨_, hwf_funs⟩ := hwf_I
  exists .standard entry
  simp only [hfind_uid, true_and]
  and_intros
  · simp only [IsValidEntityEID]
  · simp only [
      hδ, hδ',
      SymEntityData.ofEntityType,
      SymEntityData.ofStandardEntityType,
      SymEntityData.interpret,
      UnaryFunction.interpret,
      SymEntityData.ofStandardEntityType.attrsUUF,
    ] at hsame_attrs
    generalize huuf : ({
      id := UUF.attrsId uid.ty,
      arg := TermType.ofType (CedarType.entity uid.ty),
      out := TermType.ofType (CedarType.record entry.attrs)
    } : UUF) = uuf
    have hwf_uuf : uuf.WellFormed (SymEnv.ofEnv Γ).entities
    := by
      and_intros
      · simp only [←huuf]
        apply ofType_wf hwf_Γ
        constructor
        left
        apply Map.contains_iff_some_find?.mpr
        simp [hfind_uid]
      · simp only [←huuf]
        apply ofType_wf hwf_Γ
        apply wf_env_implies_wf_attrs (ety := uid.ty) hwf_Γ
        simp [EntitySchema.attrs?, hfind_uid, EntitySchemaEntry.attrs]
    have ⟨hwf_udf, hudf_arg, hudf_out⟩ := hwf_funs.1 uuf hwf_uuf
    have hwf_app :
      (Factory.app
        (UnaryFunction.udf (I.funs uuf))
        (Term.prim (TermPrim.entity uid))).WellFormed (SymEnv.ofEnv Γ).entities ∧
      (Factory.app
        (UnaryFunction.udf (I.funs uuf))
        (Term.prim (TermPrim.entity uid))).typeOf = (UnaryFunction.udf (I.funs uuf)).outType
    := by
      apply wf_app
      · constructor
        constructor
        simp only [SymEntities.isValidEntityUID]
        have :
          Map.find? (SymEnv.ofEnv Γ).entities uid.ty
          = some (SymEntityData.ofEntityType uid.ty (.standard entry))
        := by
          apply ofEnv_preserves_entity rfl
          exact hfind_uid
        simp only [this, SymEntityData.ofEntityType, SymEntityData.ofStandardEntityType]
      · simp only [UnaryFunction.argType, ←hudf_arg]
        simp only [←huuf, Term.typeOf, TermPrim.typeOf, TermType.ofType]
      · exact hwf_udf
    simp only [huuf] at hsame_attrs
    apply ofType_typeOf_pullback hwf_Γ _ _ _ _ hsame_attrs
    · apply wf_env_implies_wf_attrs (ety := uid.ty) hwf_Γ
      simp [EntitySchema.attrs?, hfind_uid]
    · apply wf_env_implies_attrs_lifted (ety := uid.ty) hwf_Γ
      simp [EntitySchema.attrs?, hfind_uid]
    · exact hwf_app.1
    · simp only [hwf_app.2, UnaryFunction.outType, ←hudf_out]
      simp only [←huuf]
      rfl
  · sorry
  · sorry

theorem ofEnv_entity_completeness_enum
  {Γ : TypeEnv} {I : Interpretation} {entities : Entities}
  {uid : EntityUID} {eids : Set String}
  {δ δ' : SymEntityData} {data : EntityData}
  (hwf_Γ : Γ.WellFormed)
  (hwf_data : data.WellFormed entities)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hfind_uid : Γ.ets.find? uid.ty = .some (.enum eids))
  (hδ' : δ' = SymEntityData.ofEntityType uid.ty (.enum eids))
  (hδ : δ = SymEntityData.interpret I δ')
  (hsame_δ : SameEntityData uid data δ) :
  InstanceOfEntitySchemaEntry uid data Γ
:= by
  have ⟨hsame_attrs, _, _, hvalid_eid, _⟩ := hsame_δ
  have ⟨_, hwf_funs⟩ := hwf_I
  exists .enum eids
  simp only [hfind_uid, true_and]
  and_intros
  · simp only [IsValidEntityEID]
    simp only [
      hδ, hδ',
      SymEntityData.interpret, SymEntityData.ofEntityType,
      SymEntityData.ofEnumEntityType, Option.map_none,
      Option.some.injEq, forall_eq',
    ] at hvalid_eid
    exact hvalid_eid
  · simp only [
      hδ, hδ',
      SymEntityData.ofEntityType,
      SymEntityData.ofStandardEntityType,
      SymEntityData.interpret,
      UnaryFunction.interpret,
      SymEntityData.ofEnumEntityType,
      SymEntityData.emptyAttrs,
      Factory.app,
      Term.isLiteral,
      ↓reduceIte,
      Map.empty,
      Map.find?,
      List.find?,
    ] at hsame_attrs
    simp only [EntitySchemaEntry.attrs]
    apply ofType_typeOf_pullback hwf_Γ _ _ _ _ hsame_attrs
    · constructor
      · exact Map.wf_empty
      · simp [Map.WellFormed, Map.make, Map.empty, List.canonicalize, Map.find?, List.find?, Map.toList]
    · constructor
      simp [Map.WellFormed, Map.make, Map.empty, List.canonicalize, Map.find?, List.find?, Map.toList, Map.kvs]
    · constructor
      · simp [Map.WellFormed, Map.make, Map.empty, List.canonicalize, Map.find?, List.find?, Map.toList, Map.kvs]
      · exact Map.wf_empty
    · simp [Term.typeOf, List.attach₃, TermType.ofType, Map.empty, TermType.ofRecordType]
  · sorry
  · sorry

theorem ofEnv_entity_completeness_ordinary
  {Γ : TypeEnv} {I : Interpretation} {entities : Entities}
  {uid : EntityUID} {entry : EntitySchemaEntry}
  {δ δ' : SymEntityData} {data : EntityData}
  (hwf_Γ : Γ.WellFormed)
  (hwf_data : data.WellFormed entities)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hfind_uid : Γ.ets.find? uid.ty = entry)
  (hδ' : δ' = SymEntityData.ofEntityType uid.ty entry)
  (hδ : δ = SymEntityData.interpret I δ')
  (hsame_δ : SameEntityData uid data δ) :
  InstanceOfEntitySchemaEntry uid data Γ
:= by
  cases entry with
  | standard entry =>
    exact ofEnv_entity_completeness_standard hwf_Γ hwf_data hwf_I hfind_uid hδ' hδ hsame_δ
  | enum eids =>
    exact ofEnv_entity_completeness_enum hwf_Γ hwf_data hwf_I hfind_uid hδ' hδ hsame_δ

  -- have ⟨hsame_attrs, _, _, hvalid_eid, _⟩ := hsame_δ
  -- have ⟨_, hwf_funs⟩ := hwf_I
  -- exists entry
  -- simp only [hfind_uid, true_and]
  -- and_intros
  -- · simp only [IsValidEntityEID]
  --   cases hentry : entry with
  --   | standard entry => simp
  --   | enum eids =>
  --     simp only
  --     simp only [
  --       hδ, hδ', hentry,
  --       SymEntityData.interpret, SymEntityData.ofEntityType,
  --       SymEntityData.ofEnumEntityType, Option.map_none,
  --       Option.some.injEq, forall_eq',
  --     ] at hvalid_eid
  --     exact hvalid_eid
  -- · cases hentry : entry with
  --   | standard entry =>
  --     simp only [
  --       hδ, hδ', hentry,
  --       SymEntityData.ofEntityType,
  --       SymEntityData.ofStandardEntityType,
  --       SymEntityData.interpret,
  --       UnaryFunction.interpret,
  --       SymEntityData.ofStandardEntityType.attrsUUF,
  --     ] at hsame_attrs
  --     generalize huuf : ({
  --       id := UUF.attrsId uid.ty,
  --       arg := TermType.ofType (CedarType.entity uid.ty),
  --       out := TermType.ofType (CedarType.record entry.attrs)
  --     } : UUF) = uuf
  --     have hwf_uuf : uuf.WellFormed (SymEnv.ofEnv Γ).entities
  --     := by
  --       and_intros
  --       · simp only [←huuf]
  --         apply ofType_wf hwf_Γ
  --         constructor
  --         left
  --         apply Map.contains_iff_some_find?.mpr
  --         simp [hfind_uid]
  --       · simp only [←huuf]
  --         apply ofType_wf hwf_Γ
  --         apply wf_env_implies_wf_attrs (ety := uid.ty) hwf_Γ
  --         simp [EntitySchema.attrs?, hfind_uid, hentry, EntitySchemaEntry.attrs]
  --     have ⟨hwf_udf, hudf_arg, hudf_out⟩ := hwf_funs.1 uuf hwf_uuf
  --     have hwf_app :
  --       (Factory.app
  --         (UnaryFunction.udf (I.funs uuf))
  --         (Term.prim (TermPrim.entity uid))).WellFormed (SymEnv.ofEnv Γ).entities ∧
  --       (Factory.app
  --         (UnaryFunction.udf (I.funs uuf))
  --         (Term.prim (TermPrim.entity uid))).typeOf = (UnaryFunction.udf (I.funs uuf)).outType
  --     := by
  --       apply wf_app
  --       · constructor
  --         constructor
  --         simp only [SymEntities.isValidEntityUID]
  --         have :
  --           Map.find? (SymEnv.ofEnv Γ).entities uid.ty
  --           = some (SymEntityData.ofEntityType uid.ty (.standard entry))
  --         := by
  --           apply ofEnv_preserves_entity rfl
  --           simp only [hentry] at hfind_uid
  --           exact hfind_uid
  --         simp only [this, SymEntityData.ofEntityType, SymEntityData.ofStandardEntityType]
  --       · simp only [UnaryFunction.argType, ←hudf_arg]
  --         simp only [←huuf, Term.typeOf, TermPrim.typeOf, TermType.ofType]
  --       · exact hwf_udf
  --     simp only [huuf] at hsame_attrs
  --     apply ofType_typeOf_pullback hwf_Γ _ _ _ _ hsame_attrs
  --     · apply wf_env_implies_wf_attrs (ety := uid.ty) hwf_Γ
  --       simp [EntitySchema.attrs?, hfind_uid, hentry]
  --     · apply wf_env_implies_attrs_lifted (ety := uid.ty) hwf_Γ
  --       simp [EntitySchema.attrs?, hfind_uid, hentry]
  --     · exact hwf_app.1
  --     · simp only [hwf_app.2, UnaryFunction.outType, ←hudf_out]
  --       simp only [←huuf]
  --       rfl
  --   | enum eids =>
  --     simp only [EntitySchemaEntry.attrs]
  --     sorry
  -- · sorry
  -- · sorry

theorem ofEnv_entity_completeness_action
  {Γ : TypeEnv} {I : Interpretation} {entities : Entities}
  {uid : EntityUID} {entry : ActionSchemaEntry}
  {δ δ' : SymEntityData} {data : EntityData}
  (hwf_Γ : Γ.WellFormed)
  (hwf_data : data.WellFormed entities)
  (hfind_uid : Γ.acts.find? uid = entry)
  (hδ' : δ' = SymEntityData.ofActionType uid.ty
    (List.map (λ x => x.fst.ty) (Map.toList Γ.acts)).eraseDups Γ.acts)
  (hδ : δ = SymEntityData.interpret I δ')
  (hsame_δ : SameEntityData uid data δ) :
  InstanceOfActionSchemaEntry uid data Γ
:= by
  have ⟨hsame_attrs, hanc₁, hanc₂, _, hsame_tags⟩ := hsame_δ
  have hwf_acts := wf_env_implies_wf_acts_map hwf_Γ
  and_intros
  · have : Map.mk [] = data.attrs
    := by
      simp [
        hδ, hδ',
        Factory.app, SymEntityData.interpret,
        UnaryFunction.interpret,
        SymEntityData.ofActionType,
        SymEntityData.emptyAttrs, Map.empty,
        Option.map_none,
        Term.isLiteral, ↓reduceIte, Map.find?,
        Map.kvs, List.find?_nil,
        SameValues,
        Term.value?,
        List.mapM₂,
        List.attach₂,
      ] at hsame_attrs
      exact hsame_attrs
    exact Eq.symm this
  · simp only [
      hδ, hδ',
      SameTags,
      Factory.app, SymEntityData.interpret,
      UnaryFunction.interpret,
      SymEntityData.ofActionType,
      SymEntityData.emptyAttrs, Map.empty,
      Option.map,
    ] at hsame_tags
    exact hsame_tags
  · exists entry
    simp only [hfind_uid, true_and]
    have hwf_data_anc : data.ancestors.WellFormed := hwf_data.2.1
    have hwf_entry_anc : entry.ancestors.WellFormed :=
      wf_env_implies_wf_action_ancestor_set hwf_Γ hfind_uid
    apply (Set.subset_iff_eq hwf_data_anc hwf_entry_anc).mp
    -- Prove that `data.ancestors = entry.ancestors`
    constructor
    · apply Set.subset_def.mpr
      intros anc hmem_data_anc
      have ⟨ancUF, hfind_ancUF, ⟨anc_ts, happ_ancUF, hmem_anc_ts⟩⟩ := hanc₁ anc hmem_data_anc
      simp only [hδ, hδ', SymEntityData.ofActionType, SymEntityData.interpret] at hfind_ancUF
      have ⟨ancUDF, hfind_ancUDF, hancUDF⟩ := Map.find?_mapOnValues_some' _ hfind_ancUF
      have := Map.make_mem_list_mem (Map.find?_mem_toList hfind_ancUDF)
      have ⟨ancTy, hmem_ancTy, hancTy⟩ := List.mem_map.mp this
      simp only [Prod.mk.injEq] at hancTy
      replace hmem_ancTy := List.mem_eraseDups_implies_mem hmem_ancTy
      have ⟨⟨act', entry'⟩, hmem_act'_entry', hact'_entry'⟩ := List.mem_map.mp hmem_ancTy
      simp only [Prod.mk.injEq] at hact'_entry'
      simp only [←hancTy.2, SymEntityData.ofActionType.ancsUDF, UnaryFunction.interpret] at hancUDF
      simp only [hancUDF, Factory.app, Term.isLiteral, ↓reduceIte] at happ_ancUF
      split at happ_ancUF
      · rename_i ts' hts'
        have := Map.make_mem_list_mem (Map.find?_mem_toList hts')
        have ⟨⟨act'', entry''⟩, hmem_act''_entry'', hact''_entry''⟩ := List.mem_filterMap.mp this
        simp only [bind, Option.bind] at hact''_entry''
        split at hact''_entry''
        contradiction
        rename_i tot htot
        simp only [Option.some.injEq, Prod.mk.injEq] at hact''_entry''
        simp only [
          SymEntityData.ofActionType.termOfType?,
          Option.ite_none_right_eq_some,
          Option.some.injEq,
        ] at htot
        simp only [←htot] at hact''_entry''
        have heq_act''_uid := hact''_entry''.1
        simp only [Term.prim.injEq, TermPrim.entity.injEq] at heq_act''_uid
        have heq_entry'' : entry'' = entry := by
          simp only [heq_act''_uid] at hmem_act''_entry''
          have := (Map.in_list_iff_find?_some hwf_acts).mp hmem_act''_entry''
          simp only [this, Option.some.injEq] at hfind_uid
          exact hfind_uid
        simp only [←hact''_entry''.2, SymEntityData.ofActionType.ancsTerm, Factory.setOf] at happ_ancUF
        simp only [Term.set.injEq] at happ_ancUF
        simp only [←happ_ancUF.1] at hmem_anc_ts
        simp only [heq_entry'', hancTy.1] at hmem_anc_ts
        replace hmem_anc_ts := (Set.make_mem _ _).mpr hmem_anc_ts
        have ⟨ancₜ, hmem_ancₜ, hancₜ⟩ := List.mem_filterMap.mp hmem_anc_ts
        simp only [
          SymEntityData.ofActionType.termOfType?,
          Option.ite_none_right_eq_some,
          Option.some.injEq, Term.prim.injEq,
          TermPrim.entity.injEq,
        ] at hancₜ
        simp only [hancₜ] at hmem_ancₜ
        exact hmem_ancₜ
      · simp at happ_ancUF
        simp only [←happ_ancUF, Set.empty] at hmem_anc_ts
        contradiction
    · apply Set.subset_def.mpr
      intros anc hmem_entry_anc
      have hcont_acts_anc := wf_env_implies_ancestors_of_action_is_action hwf_Γ hfind_uid anc hmem_entry_anc
      have ⟨anc_entry, hfind_anc⟩ := Map.contains_iff_some_find?.mp hcont_acts_anc
      have hδ_find_ancTy :
        δ.ancestors.find? anc.ty =
        some (UnaryFunction.interpret I (SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts anc.ty))
      := by
        simp only [hδ, hδ', SymEntityData.ofActionType, SymEntityData.interpret]
        apply Map.find?_mapOnValues_some
        apply Map.make_map_values_find
        apply List.mem_implies_mem_eraseDups
        apply List.mem_map.mpr
        exists (anc, anc_entry)
        simp [Map.find?_mem_toList hfind_anc]
      simp only [SymEntityData.ofActionType.ancsUDF, UnaryFunction.interpret] at hδ_find_ancTy
      have ⟨ts, happ_ancsUDF, hmem⟩ := hanc₂ anc.ty
        (SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts anc.ty) hδ_find_ancTy
      have :
        Factory.app (SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts anc.ty) (Term.prim (TermPrim.entity uid))
        = SymEntityData.ofActionType.ancsTerm anc.ty entry.ancestors.toList
      := by
        apply app_table_make_filterMap hfind_uid
        · simp [SymEntityData.ofActionType.termOfType?]
        · intros kv hkv
          have ⟨k, v⟩ := kv
          have ⟨v', hv'⟩ := hkv
          simp only [SymEntityData.ofActionType.termOfType?, Option.bind_eq_bind] at hv'
          split at hv'
          · simp only [
              Option.bind_some, Option.some.injEq,
              Prod.mk.injEq, Term.prim.injEq,
              TermPrim.entity.injEq,
            ] at hv'
            simp only [hv'.1]
          · contradiction
        · simp only [Term.isLiteral]
      simp only [this, SymEntityData.ofActionType.ancsTerm, Factory.setOf, Term.set.injEq] at happ_ancsUDF
      simp only [←happ_ancsUDF.1] at hmem
      specialize hmem (.prim (.entity anc))
      simp only [Term.prim.injEq, TermPrim.entity.injEq, exists_eq_left'] at hmem
      apply hmem
      apply (Set.make_mem _ _).mp
      apply List.mem_filterMap.mpr
      exists anc
      have := (Set.in_list_iff_in_set _ _).mpr hmem_entry_anc
      simp [Set.toList, this, true_and, SymEntityData.ofActionType.termOfType?]

theorem ofEnv_entity_completeness
  {Γ : TypeEnv} {I : Interpretation} {entities : Entities}
  {uid : EntityUID} {δ : SymEntityData} {data : EntityData}
  (hwf_Γ : Γ.WellFormed)
  (hwf_data : data.WellFormed entities)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hfind_δ : Map.find? (SymEnv.interpret I (SymEnv.ofEnv Γ)).entities uid.ty = some δ)
  (hsame_δ : SameEntityData uid data δ) :
  InstanceOfSchemaEntry uid data Γ
:= by
  simp only [
    SymEnv.interpret,
    SymEntities.interpret,
    SymEnv.ofEnv,
    SymEntities.ofSchema,
  ] at hfind_δ
  -- Exists a `SymEntityData` before interpretation
  have ⟨δ', hfind_δ', hδ'⟩ := Map.find?_mapOnValues_some' _ hfind_δ
  have := Map.find?_mem_toList hfind_δ'
  have := Map.make_mem_list_mem this
  have := List.mem_append.mp this
  cases this with
  -- Ordinary entity
  | inl hmem =>
    left
    have ⟨⟨ety, entry⟩, hmem_ety, hety⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at hety
    have hwf_ets := wf_env_implies_wf_ets_map hwf_Γ
    have hfind_ety := (Map.in_list_iff_find?_some hwf_ets).mp hmem_ety
    have := Eq.symm hety.2
    simp only [hety.1] at this hfind_ety
    exact ofEnv_entity_completeness_ordinary hwf_Γ hwf_data hwf_I hfind_ety this hδ' hsame_δ
  -- Action entity
  | inr hmem =>
    right
    have ⟨actTy, hmem_actTy, hactTy⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at hactTy
    have heq_δ' := hactTy.2
    simp only [hactTy.1] at heq_δ'
    replace hmem_actTy := List.mem_eraseDups_implies_mem hmem_actTy
    have ⟨⟨act, entry⟩, hmem_act, hact⟩ := List.mem_map.mp hmem_actTy
    simp only at hact
    have hwf_acts := wf_env_implies_wf_acts_map hwf_Γ
    have hfind_act := (Map.in_list_iff_find?_some hwf_acts).mp hmem_act
    have ⟨_, _, _, hmems, _⟩ := hsame_δ
    simp only [
      hδ', ←heq_δ', SymEntityData.ofActionType, SymEntityData.interpret,
    ] at hmems
    simp only [Option.some.injEq, forall_eq', SymEntityData.ofActionType.acts] at hmems
    have := (Set.make_mem _ _).mpr hmems
    have ⟨⟨uid', entry'⟩, hmem_uid', huid'⟩ := List.mem_filterMap.mp this
    have heq_uid' : uid' = uid := by
      cases uid'; cases uid
      simp at huid'
      congr <;> simp [huid']
    simp only [heq_uid'] at hmem_uid'
    have hfind_uid := (Map.in_list_iff_find?_some hwf_acts).mp hmem_uid'
    exact ofEnv_entity_completeness_action hwf_Γ hwf_data hfind_uid (Eq.symm heq_δ') hδ' hsame_δ

theorem enum_complete_implies_has_all_actions
  {Γ : TypeEnv} {env : Env}
  (hwf_Γ : Γ.WellFormed)
  (henum_comp : Env.EnumCompleteFor env (SymEnv.ofEnv Γ)) :
  Entities.HasAllActions env.entities Γ
:= by
  intros uid entry hfind_uid
  simp only [
    Env.EnumCompleteFor,
    SymEnv.ofEnv,
    SymEntities.ofSchema,
  ] at henum_comp
  specialize henum_comp uid
    (SymEntityData.ofActionType uid.ty (List.map (λ x => x.fst.ty) (Map.toList Γ.acts)).eraseDups Γ.acts)
    (Set.make (SymEntityData.ofActionType.acts uid.ty Γ.acts))
  apply henum_comp
  · apply Map.map_make_append_find_disjoint'
    have hwf_ets := wf_env_implies_wf_ets_map hwf_Γ
    have hwf_acts := wf_env_implies_wf_acts_map hwf_Γ
    · apply List.find?_eq_none.mpr
      intros x hmem_ety
      replace ⟨ety, entry⟩ := x
      have ⟨⟨ety', entry'⟩, hmem_ety', hety'⟩ := List.mem_map.mp hmem_ety
      simp only [Prod.mk.injEq] at hety'
      have hfind_ety := (Map.in_list_iff_find?_some hwf_ets).mp hmem_ety'
      simp only [hety'.1] at hfind_ety
      intros heq
      simp only [beq_iff_eq] at heq
      simp only [heq] at hfind_ety
      have := wf_env_disjoint_ets_acts hwf_Γ hfind_ety hfind_uid
      contradiction
    · apply List.find?_unique_entry
      · intros x hmem heq
        have ⟨ety, data⟩ := x
        have ⟨_, _, hdata⟩ := List.mem_map.mp hmem
        simp only [Prod.mk.injEq] at hdata
        simp only [beq_iff_eq] at heq
        simp only [heq] at hdata
        simp only [hdata.1] at hdata
        simp only [heq, ←hdata.2]
      · apply List.mem_map.mpr
        exists uid.ty
        simp only [and_true]
        apply List.mem_implies_mem_eraseDups
        apply List.mem_map.mpr
        exists (uid, entry)
        simp [Map.find?_mem_toList hfind_uid]
      · simp
    · intros x₁ x₂ hmem₁ hmem₂
      have ⟨ancTy₁, hmem_ancTy₁, hancTy₁⟩ := List.mem_map.mp hmem₁
      have ⟨ancTy₂, hmem_ancTy₂, hancTy₂⟩ := List.mem_map.mp hmem₂
      simp only [←hancTy₁, ←hancTy₂]
      intros heq
      simp only [heq]
  · rfl
  · apply (Set.make_mem _ _).mp
    simp only [SymEntityData.ofActionType.acts]
    apply List.mem_filterMap.mpr
    exists (uid, entry)
    simp only [↓reduceIte, and_true]
    exact Map.find?_mem_toList hfind_uid

theorem ofEnv_entities_completeness
  {Γ : TypeEnv} {env : Env} {I : Interpretation}
  (hwf_Γ : Γ.WellFormed)
  (hwf_env : env.StronglyWellFormed)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (henum_comp : Env.EnumCompleteFor env (SymEnv.ofEnv Γ))
  (hsame_I : env ∼ SymEnv.interpret I (SymEnv.ofEnv Γ)) :
  InstanceOfSchema env.entities Γ
:= by
  have ⟨_, hsame_ents⟩ := hsame_I
  constructor
  · intros uid data hfind_uid
    have ⟨δ, hfind_δ, hsame_δ⟩ := hsame_ents uid data hfind_uid
    have hwf_data := hwf_env.2.1.2 uid data hfind_uid
    exact ofEnv_entity_completeness hwf_Γ hwf_data hwf_I hfind_δ hsame_δ
  -- All action entities exist in `env.entities`
  · intros uid entry hfind_uid
    have := enum_complete_implies_has_all_actions hwf_Γ henum_comp
    exact this uid entry hfind_uid

theorem ofEnv_completeness
  {Γ : TypeEnv} {env : Env}
  (hwf_Γ : Γ.WellFormed)
  (hwf_env : env.StronglyWellFormed)
  (henum_comp : Env.EnumCompleteFor env (SymEnv.ofEnv Γ))
  (hinst : env ∈ᵢ SymEnv.ofEnv Γ) :
  InstanceOfWellFormedEnvironment env.request env.entities Γ
:= by
  constructor
  · exact hwf_Γ
  have ⟨I, hwf_I, hsame_I⟩ := hinst
  constructor
  · exact ofEnv_request_completeness hwf_Γ hwf_I hsame_I
  · exact ofEnv_entities_completeness hwf_Γ hwf_env hwf_I henum_comp hsame_I

end Cedar.Thm
