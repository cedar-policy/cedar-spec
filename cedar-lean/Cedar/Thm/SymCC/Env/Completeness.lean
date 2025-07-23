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
  sorry

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

/--
If a term type is both the result of `TermType.ofType` and `Term.typeOf`
for some well-formed `CedarType`
and well-formed `Term`,
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
    · intros attr val qty hfind_val hfind_qty
      have hwf_ty' := hwf_ty_rec attr qty hfind_qty
      have hlift_ty' := hlift_ty_rec attr qty (Map.find?_mem_toList hfind_qty)
      cases qty with
      | optional ty' | required ty' =>
      cases hwf_ty'
      rename_i hwf_ty'
      cases hlift_ty'
      rename_i hlift_ty'
      have := Map.find?_mem_toList hfind_val
      have ⟨attr_v, hmem_attr_v, hattr_v⟩ := List.mem_filterMap.mp this
      have ⟨attr_t', hmem_attr_t', hattr_t'⟩ := List.mapM_some_implies_all_from_some hval_rec attr_v hmem_attr_v
      simp only [Option.map] at hattr_v
      have heq_attr : attr = attr_t'.fst := sorry
      sorry
      -- split at hattr_v
      -- · rename_i v hv
      --   unfold Term.value?.attrValue? at hattr_t'
      --   split at hattr_t'
      --   · simp only [bind, Option.bind] at hattr_t'
      --     split at hattr_t'
      --     contradiction
      --     rename_i v' hv'
      --     have hwf_t' := hwf_rec attr_t'.fst attr_t'.snd hmem_attr_t'
      --     simp only [Qualified.getType]
      --     simp only [Option.some.injEq] at hattr_t'
      --     simp only [←hattr_t', Option.some.injEq] at hv
      --     simp only [hv] at hv'
      --     simp only [Option.some.injEq, Prod.mk.injEq] at hattr_v
      --     simp only [hattr_v.2] at hv'
      --     apply ofType_typeOf_pullback hwf_Γ hwf_ty' hlift_ty' hwf_t' _ hv'
      --     sorry
      --   · simp only [Option.some.injEq] at hattr_t'
      --     simp [←hattr_t'] at hv
      --   · simp only [bind, Option.bind] at hattr_t'
      --     split at hattr_t'
      --     contradiction
      --     rename_i v' hv'
      --     have hwf_t' := hwf_rec attr_t'.fst attr_t'.snd hmem_attr_t'
      --     simp only [Qualified.getType]
      --     simp only [Option.some.injEq] at hattr_t'
      --     simp only [←hattr_t', Option.some.injEq] at hv
      --     simp only [hv] at hv'
      --     simp only [Option.some.injEq, Prod.mk.injEq] at hattr_v
      --     simp only [hattr_v.2] at hv'
      --     apply ofType_typeOf_pullback hwf_Γ hwf_ty' hlift_ty' hwf_t' _ hv'
      --     all_goals sorry
      -- · contradiction
    · sorry

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
    -- Ideally we should have the "commuting" diagram (modulo `.some`)
    --        cedarType?
    --          ----->
    --          ofType
    -- TermType <----- CedarType
    --    ^               ^
    --    |               |
    --    | typeOf        | InstanceOfType
    --    |               |
    --    |               |
    --  Term ---------> Value
    --         value?
    --       <---------
    --       symbolize?

theorem ofEnv_completeness
  {Γ : TypeEnv} {env : Env}
  (hwf : Γ.WellFormed)
  (hwf_env : env.StronglyWellFormed)
  (hinst : env ∈ᵢ SymEnv.ofEnv Γ) :
  InstanceOfWellFormedEnvironment env.request env.entities Γ
:= by
  constructor
  · exact hwf
  have ⟨I, hwf_I, hsame_I⟩ := hinst
  constructor
  · exact ofEnv_request_completeness hwf hwf_I hsame_I
  · sorry

end Cedar.Thm
