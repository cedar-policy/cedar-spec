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
import Cedar.Thm.SymCC.Env.Interpret
import Cedar.Thm.SymCC.Term.Interpret.WF
import Cedar.Thm.SymCC.Term.ofType

/-!
This file contains the completeness theorems of `Sym.ofEnv`
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
private theorem sym_entities_is_valid_entity_uid_implies_entity_uid_wf
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
      simp only [ActionSchema.contains, this, Option.isSome]
  · contradiction

/-- `TermPrim` case of `ofType_typeOf_pullback`. -/
private theorem ofType_typeOf_pullback_prim
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

private theorem value?_some_implies_typeOf_not_option
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
then the if the the term is concretizable (via `value?`),
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
private theorem ofType_typeOf_pullback
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
    cases hlift_ty with | set_lifted hlift_ty_ts =>
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
    cases hlift_ty with | record_lifted hlift_ty_rec =>
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
          simp only [h₁, Option.some.injEq] at h₂
          cases qty with
          | optional ty' =>
            simp only [TermType.ofQualifiedType] at h₂
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

private theorem ofEnv_request_completeness
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

private theorem ets_find_some_standard_entry_implies_valid_uid
  {Γ : TypeEnv} {uid : EntityUID} {entry : StandardSchemaEntry}
  (hfind_uid : Γ.ets.find? uid.ty = .some (.standard entry)) :
  (SymEnv.ofEnv Γ).entities.isValidEntityUID uid
:= by
  simp only [SymEntities.isValidEntityUID]
  have :
    Map.find? (SymEnv.ofEnv Γ).entities uid.ty
    = some (SymEntityData.ofEntityType uid.ty (.standard entry))
  := by
    apply ofEnv_preserves_entity rfl
    exact hfind_uid
  simp only [this, SymEntityData.ofEntityType, SymEntityData.ofStandardEntityType]

private theorem ets_find_some_standard_entry_implies_valid_uid_ty
  {Γ : TypeEnv} {uid : EntityUID} {entry : StandardSchemaEntry}
  (hfind_uid : Γ.ets.find? uid.ty = .some (.standard entry)) :
  (SymEnv.ofEnv Γ).entities.isValidEntityType uid.ty
:= by
  have hvalid_uid := ets_find_some_standard_entry_implies_valid_uid hfind_uid
  simp only [SymEntities.isValidEntityUID] at hvalid_uid
  split at hvalid_uid
  · rename_i heq
    simp only [SymEntities.isValidEntityType, Map.contains, heq, Option.isSome]
  · contradiction

private theorem ofEnv_entity_completeness_standard_inst_tags
  {Γ : TypeEnv} {I : Interpretation} {entities : Entities}
  {uid : EntityUID} {entry : StandardSchemaEntry}
  {δ δ' : SymEntityData} {data : EntityData}
  (hwf_Γ : Γ.WellFormed)
  (hwf_data : data.WellFormed entities)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hfind_uid : Γ.ets.find? uid.ty = .some (.standard entry))
  (hδ' : δ' = SymEntityData.ofEntityType uid.ty (.standard entry))
  (hδ : δ = SymEntityData.interpret I δ')
  (hsame_δ : SameEntityData uid data δ)
  (hfind_δ : Map.find? (SymEnv.interpret I (SymEnv.ofEnv Γ)).entities uid.ty = some δ) :
  InstanceOfEntityTags data (EntitySchemaEntry.standard entry) Γ
:= by
  have ⟨hsame_attrs, _, _, hvalid_eid, hsame_tags⟩ := hsame_δ
  have ⟨_, hwf_funs⟩ := hwf_I
  have hwf_ofEnv_Γ := ofEnv_is_wf hwf_Γ
  have ⟨_, ⟨_, hwf_I_ents⟩⟩ := interpret_εnv_wf hwf_ofEnv_Γ hwf_I
  have hwf_δ := hwf_I_ents uid.ty δ hfind_δ
  have ⟨_, _, _, _, _, hwf_τs, _⟩ := hwf_δ
  have hvalid_uid := ets_find_some_standard_entry_implies_valid_uid hfind_uid
  have hvalid_uid_ty := ets_find_some_standard_entry_implies_valid_uid_ty hfind_uid
  have hwf_tag_ty :
    TermType.WellFormed (SymEnv.ofEnv Γ).entities (TermType.tagFor uid.ty)
  := by
    simp only [TermType.tagFor, EntityTag.mk]
    constructor
    · intros a ty h
      simp [Map.find?, List.find?] at h
      split at h
      any_goals contradiction
      simp only [Option.some.injEq] at h
      simp only [h] at *
      rename_i heq
      split at heq
      · simp only [Option.some.injEq, Prod.mk.injEq] at heq
        simp only [←heq.2]
        constructor
        exact hvalid_uid_ty
      · split at heq
        any_goals contradiction
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        simp only [←heq.2]
        constructor
    · simp [
        Map.WellFormed, Map.make,
        List.canonicalize, Map.toList,
        Map.kvs, List.insertCanonical,
      ]
  cases htagTy : entry.tags with
  | none =>
    simp only [InstanceOfEntityTags, EntitySchemaEntry.tags?, htagTy]
    simp only [
      SameTags,
      Option.map,
      hδ, hδ', htagTy,
      SymEntityData.ofEntityType,
      SymEntityData.ofStandardEntityType,
      SymEntityData.interpret,
      UnaryFunction.interpret,
      Map.empty
    ] at hsame_tags
    exact hsame_tags
  | some tagTy =>
    simp only [
      SameTags,
      Option.map,
      hδ, hδ', htagTy,
      SymEntityData.ofEntityType,
      SymEntityData.ofStandardEntityType,
      SymEntityData.interpret,
      UnaryFunction.interpret
    ] at hsame_tags
    simp only [InstanceOfEntityTags, EntitySchemaEntry.tags?, htagTy]
    intros v hmem_v_tags
    have ⟨k, hmem_kv⟩ := Map.in_values_exists_key hmem_v_tags
    have hwf_tags : Map.WellFormed data.tags := by
      have ⟨_, _, _, h, _⟩ := hwf_data
      exact h
    have hwf_tagTy : CedarType.WellFormed Γ tagTy
    := by
      apply wf_env_implies_wf_tag_type (ety := uid.ty) hwf_Γ
      simp [EntitySchema.tags?, hfind_uid, htagTy, EntitySchemaEntry.tags?]
    have hfind_kv := (Map.in_list_iff_find?_some hwf_tags).mp hmem_kv
    have ⟨_, hsame_v⟩ := hsame_tags.2 k v hfind_kv
    have ⟨vals_uuf, hvals_uuf⟩ :
      ∃ uuf,
        (SymEntityData.ofStandardEntityType.symTags uid.ty tagTy).vals = .uuf uuf
    := by simp [SymEntityData.ofStandardEntityType.symTags]
    -- Rewrite the tag value lookup as `Term.interpret`
    have htag_lookup_as_interp :
      Factory.app
        (UnaryFunction.interpret I (SymEntityData.ofStandardEntityType.symTags uid.ty tagTy).vals)
        (Factory.tagOf (Term.entity uid) (Term.string k))
      = Term.interpret I (Factory.app
        (.uuf vals_uuf)
        (Factory.tagOf (Term.entity uid) (Term.string k)))
    := by
      simp only [
        Term.interpret, Op.interpret,
        List.attach_cons, List.attach_nil,
        List.map_nil,
        List.map_cons,
        UnaryFunction.interpret,
        hvals_uuf,
        Factory.app,
        Factory.tagOf,
        Factory.recordOf,
        Map.make,
        List.canonicalize,
        List.attach₃,
        List.pmap,
        List.insertCanonical,
      ]
      simp
    -- Prove that the tag lookup term is well-formed and well-typed
    have hwf_tag_lookup:
      Term.WellFormed (SymEnv.ofEnv Γ).entities
        ((SymTags.interpret I (SymEntityData.ofStandardEntityType.symTags uid.ty tagTy)).getTag!
          (Term.entity uid)
          (Term.string k)) ∧
      ((SymTags.interpret I (SymEntityData.ofStandardEntityType.symTags uid.ty tagTy)).getTag!
        (Term.entity uid)
        (Term.string k)).typeOf =
      (Factory.app
        (.uuf vals_uuf)
        (Factory.tagOf (Term.entity uid) (Term.string k))).typeOf
    := by
      simp only [
        SymTags.interpret,
        SymTags.getTag!,
      ]
      simp only [htag_lookup_as_interp]
      apply interpret_term_wf hwf_I _
      -- (UnaryFunction.uuf vals_uuf).outType
      apply (wf_app _ _ _).1
      · simp only [Factory.tagOf]
        constructor
        · intros a t h
          simp only [Map.toList, Map.kvs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
            or_false] at h
          cases h with
          | inl h =>
            simp only [h.2, Term.entity]
            repeat constructor
            exact hvalid_uid
          | inr h =>
            simp only [h.2, Term.string]
            repeat constructor
        · simp [
            Map.WellFormed, Map.make,
            List.canonicalize, Map.toList,
            Map.kvs, List.insertCanonical,
          ]
      · simp only [
          Factory.tagOf,
          Term.typeOf,
          List.attach₃,
          List.pmap,
          List.map,
          TermPrim.typeOf,
          ←hvals_uuf,
        ]
        simp only [
          SymEntityData.ofStandardEntityType.symTags,
          UnaryFunction.argType,
        ]
      · simp only [←hvals_uuf]
        simp only [
          SymEntityData.ofStandardEntityType.symTags,
          UnaryFunction.WellFormed,
          UUF.WellFormed,
        ]
        constructor
        · exact hwf_tag_ty
        · exact ofType_wf hwf_Γ hwf_tagTy
    apply ofType_typeOf_pullback hwf_Γ _ _ _ _ hsame_v
    · apply wf_env_implies_wf_tag_type (ety := uid.ty) hwf_Γ
      simp [EntitySchema.tags?, hfind_uid, htagTy, EntitySchemaEntry.tags?]
    · apply wf_env_implies_tag_type_lifted (ety := uid.ty) hwf_Γ
      simp [EntitySchema.tags?, hfind_uid, htagTy, EntitySchemaEntry.tags?]
    · exact hwf_tag_lookup.1
    · simp [hwf_tag_lookup.2, ←hvals_uuf]
      simp only [
        Factory.app,
        Term.typeOf,
        SymEntityData.ofStandardEntityType.symTags,
      ]

private theorem ofEnv_entity_completeness_standard
  {Γ : TypeEnv} {I : Interpretation} {entities : Entities}
  {uid : EntityUID} {entry : StandardSchemaEntry}
  {δ δ' : SymEntityData} {data : EntityData}
  (hwf_Γ : Γ.WellFormed)
  (hwf_data : data.WellFormed entities)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hfind_uid : Γ.ets.find? uid.ty = .some (.standard entry))
  (hδ' : δ' = SymEntityData.ofEntityType uid.ty (.standard entry))
  (hδ : δ = SymEntityData.interpret I δ')
  (hsame_δ : SameEntityData uid data δ)
  (hfind_δ : Map.find? (SymEnv.interpret I (SymEnv.ofEnv Γ)).entities uid.ty = some δ) :
  InstanceOfEntitySchemaEntry uid data Γ
:= by
  have ⟨hsame_attrs, hanc₁, _, hvalid_eid, hsame_tags⟩ := hsame_δ
  have ⟨_, hwf_funs⟩ := hwf_I
  have hwf_ofEnv_Γ := ofEnv_is_wf hwf_Γ
  have ⟨_, ⟨_, hwf_I_ents⟩⟩ := interpret_εnv_wf hwf_ofEnv_Γ hwf_I
  have hwf_δ := hwf_I_ents uid.ty δ hfind_δ
  have ⟨_, _, _, _, _, hwf_τs, _⟩ := hwf_δ
  have hvalid_uid := ets_find_some_standard_entry_implies_valid_uid hfind_uid
  have hvalid_uid_ty := ets_find_some_standard_entry_implies_valid_uid_ty hfind_uid
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
        exact hvalid_uid
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
  -- Ancestor type matches
  · intros anc hmem_data_anc
    simp only [EntitySchemaEntry.ancestors]
    have ⟨ancUF, hfind_ancUF, ⟨ts, happ_ancUF, hmem_ts⟩⟩ := hanc₁ anc hmem_data_anc
    simp only [
      hδ, hδ',
      SymEntityData.interpret,
      SymEntityData.ofEntityType,
      SymEntityData.ofStandardEntityType,
    ] at hfind_ancUF
    have ⟨f, hfind_f, _⟩ := Map.find?_mapOnValues_some' _ hfind_ancUF
    have := Map.find?_mem_toList hfind_f
    have := Map.make_mem_list_mem this
    have ⟨ancTy, hfind_ancTy, hancTy⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at hancTy
    simp only [hancTy.1] at hfind_ancTy
    exact hfind_ancTy
  · exact ofEnv_entity_completeness_standard_inst_tags
      hwf_Γ hwf_data hwf_I hfind_uid hδ' hδ hsame_δ hfind_δ

private theorem ofEnv_entity_completeness_enum
  {Γ : TypeEnv} {I : Interpretation}
  {uid : EntityUID} {eids : Set String}
  {δ δ' : SymEntityData} {data : EntityData}
  (hwf_Γ : Γ.WellFormed)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hfind_uid : Γ.ets.find? uid.ty = .some (.enum eids))
  (hδ' : δ' = SymEntityData.ofEntityType uid.ty (.enum eids))
  (hδ : δ = SymEntityData.interpret I δ')
  (hsame_δ : SameEntityData uid data δ):
  InstanceOfEntitySchemaEntry uid data Γ
:= by
  have ⟨hsame_attrs, hanc₁, _, hvalid_eid, hsame_tags⟩ := hsame_δ
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
      · simp only [Map.find?, Map.empty, List.find?, reduceCtorEq, false_implies, implies_true]
    · constructor
      simp only [Map.toList, Map.kvs, Map.empty, List.not_mem_nil, false_implies, implies_true]
    · constructor
      · simp only [Map.toList, Map.kvs, List.not_mem_nil, false_implies, implies_true]
      · exact Map.wf_empty
    · simp [Term.typeOf, List.attach₃, TermType.ofType, Map.empty, TermType.ofRecordType]
  · intros anc hmem_data_anc
    have := hanc₁ anc hmem_data_anc
    simp [
      SameEntityData.InSymAncestors,
      hδ, hδ',
      SymEntityData.ofEntityType,
      SymEntityData.ofEnumEntityType,
      SymEntityData.interpret,
      UnaryFunction.interpret,
      Map.empty,
      Map.mapOnValues,
      List.map,
      Map.find?,
      List.find?,
    ] at this
  · simp only [
      SameTags,
      Option.map,
      hδ, hδ',
      SymEntityData.ofEntityType,
      SymEntityData.ofEnumEntityType,
      SymEntityData.interpret,
      UnaryFunction.interpret,
      SymEntityData.emptyAttrs,
      Map.empty
    ] at hsame_tags
    simp only [InstanceOfEntityTags, EntitySchemaEntry.tags?]
    exact hsame_tags

private theorem ofEnv_entity_completeness_ordinary
  {Γ : TypeEnv} {I : Interpretation} {entities : Entities}
  {uid : EntityUID} {entry : EntitySchemaEntry}
  {δ δ' : SymEntityData} {data : EntityData}
  (hwf_Γ : Γ.WellFormed)
  (hwf_data : data.WellFormed entities)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hfind_uid : Γ.ets.find? uid.ty = entry)
  (hδ' : δ' = SymEntityData.ofEntityType uid.ty entry)
  (hδ : δ = SymEntityData.interpret I δ')
  (hsame_δ : SameEntityData uid data δ)
  (hfind_δ : Map.find? (SymEnv.interpret I (SymEnv.ofEnv Γ)).entities uid.ty = some δ) :
  InstanceOfEntitySchemaEntry uid data Γ
:= by
  cases entry with
  | standard entry =>
    exact ofEnv_entity_completeness_standard hwf_Γ hwf_data hwf_I hfind_uid hδ' hδ hsame_δ hfind_δ
  | enum eids =>
    exact ofEnv_entity_completeness_enum hwf_Γ hwf_I hfind_uid hδ' hδ hsame_δ

private theorem ofEnv_entity_completeness_action
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
      SymEntityData.interpret,
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
      simp only at hact'_entry'
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
      simp only [Set.toList, this, SymEntityData.ofActionType.termOfType?, ↓reduceIte, and_self]

private theorem ofEnv_entity_completeness
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
    exact ofEnv_entity_completeness_ordinary hwf_Γ hwf_data hwf_I hfind_ety this hδ' hsame_δ hfind_δ
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

private theorem enum_complete_implies_has_all_actions
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

private theorem ofEnv_entities_completeness
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
