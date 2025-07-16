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

import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.SymCC.Concretizer
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymCC.Env.WF
import Cedar.SymCC.Concretizer
import Cedar.SymCC.Symbolizer
import Cedar.SymCC.Env

/-!
This file contains the soundness theorems of `Sym.ofEnv`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Spec
open Cedar.SymCC
open Cedar.Validation
open Cedar.Data

/-- The results of `symbolize?` has the correct type. -/
theorem value_symbolize?_well_typed
  {Γ : TypeEnv} {v : Value} {ty : CedarType} {t : Term}
  (hwf_ty : ty.WellFormed Γ)
  (hwt_v : InstanceOfType Γ v ty)
  (hsym : v.symbolize? ty = .some t) :
  t.typeOf = TermType.ofType ty
:= by
  cases hwt_v with
  | instance_of_bool | instance_of_int | instance_of_string =>
    simp only [Value.symbolize?, Prim.symbolize, Option.some.injEq] at hsym
    simp only [
      ←hsym, Term.typeOf,
      TermPrim.typeOf, TermType.ofType,
      Int64.toBitVec, BitVec.width,
    ]
  | instance_of_entity _ _ hwt_ety =>
    simp only [Value.symbolize?, Prim.symbolize, Option.some.injEq] at hsym
    simp only [
      ←hsym, Term.typeOf,
      TermPrim.typeOf, TermType.ofType,
      hwt_ety.1,
    ]
  | instance_of_set s =>
    simp only [
      Value.symbolize?, Prim.symbolize, Option.some.injEq,
      bind, Option.bind,
    ] at hsym
    split at hsym
    contradiction
    rename_i sym_elems hsym_elems
    simp only [Option.some.injEq] at hsym
    simp only [←hsym, Term.typeOf, TermType.ofType]
  | instance_of_record rec rty h₁ h₂ h₃ =>
    cases hwf_ty with | record_wf hwf_rty_map hwf_rty =>
    simp only [
      Value.symbolize?, Prim.symbolize, Option.some.injEq,
      bind, Option.bind,
    ] at hsym
    split at hsym
    contradiction
    rename_i sym_attrs hsym_attrs
    simp only [Option.some.injEq] at hsym
    simp only [←hsym, Term.typeOf, TermType.ofType]
    congr
    simp only [List.map_attach₃_snd]
    -- Rephrase `TermType.ofRecordType` as a map
    have (rty : List (Attr × QualifiedType)) :
      TermType.ofRecordType rty
      = rty.map λ (a, qty) => (a, TermType.ofQualifiedType qty)
    := by
      induction rty with
      | nil => simp [TermType.ofRecordType]
      | cons => simp [TermType.ofRecordType]; assumption
    simp only [this]
    have :
      List.Forall₂
        (λ rty_entry sym_attr =>
          rty_entry ∈ rty.toList ∧
          .some sym_attr = Value.symbolize?.symbolizeAttr? rec rty rty_entry)
        (Map.toList rty)
        sym_attrs
    := by
      apply List.mapM_implies_forall₂_option _ hsym_attrs
      intros _ _ _ h
      constructor
      · assumption
      · simp [h]
    apply Eq.symm
    apply List.forall₂_iff_map_eq.mp
    apply List.Forall₂.imp _ this
    intros rty_entry sym_attr hsym_attr
    simp only [Value.symbolize?.symbolizeAttr?] at hsym_attr
    have : rty_entry.fst = sym_attr.fst
    := by
      replace hsym_attr := hsym_attr.2
      split at hsym_attr
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsym_attr
        simp only [hsym_attr]
      · split at hsym_attr
        all_goals
          simp only [bind, Option.bind] at hsym_attr
          split at hsym_attr
          contradiction
          simp only [Option.some.injEq] at hsym_attr
          simp only [hsym_attr]
    simp only [this, Prod.mk.injEq, true_and]
    have hfind_rty := (Map.in_list_iff_find?_some hwf_rty_map).mp hsym_attr.1
    split at hsym_attr
    · simp only [Option.some.injEq, Prod.mk.injEq] at hsym_attr
      simp only [hsym_attr]
      cases hqty : rty_entry.snd with
      | optional =>
        simp only [TermType.ofQualifiedType, Qualified.getType, Term.typeOf]
      | required =>
        rename_i hnot_find_rec _
        have := h₃ rty_entry.fst rty_entry.snd hfind_rty
        simp only [Qualified.isRequired, hqty, forall_const] at this
        simp [Map.contains, hnot_find_rec, Option.isSome] at this
    · rename_i attr' hfind_rec
      split at hsym_attr
      all_goals
        rename_i ty' hqty
        simp only [bind, Option.bind] at hsym_attr
        split at hsym_attr
        · have := hsym_attr.2
          contradiction
        rename_i sym_attr' hsym_attr'
        simp only [Option.some.injEq] at hsym_attr
        simp only [hsym_attr, hqty, TermType.ofQualifiedType, Term.typeOf]
        congr
        have hwf_ty' : ty'.WellFormed Γ := by
          have := hwf_rty rty_entry.fst rty_entry.snd hfind_rty
          simp only [hqty] at this
          cases this
          assumption
        have hwt_v' : InstanceOfType Γ attr' ty' := by
          have := h₂ rty_entry.fst _ rty_entry.snd hfind_rec hfind_rty
          simp only [hqty, Qualified.getType] at this
          exact this
        have := value_symbolize?_well_typed
          hwf_ty' hwt_v' hsym_attr'
        simp [this]
  | instance_of_ext _ _ hwt_ext =>
    simp only [Value.symbolize?, Option.some.injEq] at hsym
    simp only [
      ←hsym, Term.typeOf,
      TermPrim.typeOf, TermType.ofType,
    ]
    simp only [InstanceOfExtType] at hwt_ext
    split at hwt_ext
    any_goals simp
    contradiction
termination_by sizeOf v
decreasing_by
  all_goals
    rename rec.find? rty_entry.fst = some _ => h₁
    simp [*]
    replace h₁ := Map.find?_mem_toList h₁
    cases rec
    have := List.sizeOf_lt_of_mem h₁
    simp [Map.toList, Map.kvs] at this ⊢
    omega

/-- The results of `symbolize?` is not Term.none. -/
theorem value_symbolize?_not_none
  {v : Value} {ty : CedarType} {t : Term} {ty' : TermType}
  (hsome : v.symbolize? ty = .some t) :
  t ≠ .none ty'
:= by
  intros ht_none
  simp only [ht_none] at hsome
  unfold Value.symbolize? at hsome
  split at hsome
  · rename_i p
    cases p
    simp only [Prim.symbolize] at hsome
    all_goals
      try simp at hsome
      try contradiction
  all_goals
    repeat
      simp [bind, Option.bind] at hsome
      split at hsome
    all_goals
      try simp at hsome
      try contradiction

/-- The results of `symbolize?` is not Term.some. -/
theorem value_symbolize?_not_some
  {v : Value} {ty : CedarType} {t : Term} {t' : Term}
  (hsome : v.symbolize? ty = .some t) :
  t ≠ .some t'
:= by
  intros ht_some
  simp only [ht_some] at hsome
  unfold Value.symbolize? at hsome
  split at hsome
  · rename_i p
    cases p
    simp only [Prim.symbolize] at hsome
    all_goals
      try simp at hsome
      try contradiction
  all_goals
    repeat
      simp [bind, Option.bind] at hsome
      split at hsome
    all_goals
      try simp at hsome
      try contradiction

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

/-- `mapM` preserves `SortedBy` if the keys are preserved -/
theorem mapM_preserves_SortedBy
  [LT γ]
  {l₁ : List α} {l₂ : List β}
  {f : α → Option β}
  {k₁ : α → γ}
  {k₂ : β → γ}
  (hsorted : List.SortedBy k₁ l₁)
  (hmapM : l₁.mapM f = .some l₂)
  (hkey : ∀ a b, f a = .some b → k₁ a = k₂ b) :
  List.SortedBy k₂ l₂
:= by
  have := List.mapM_some_iff_forall₂.mp hmapM
  induction this with
  | nil => constructor
  | cons hhd hrst ih =>
    rename_i hd₁ hd₂ tl₁ tl₂
    have hrst' := List.mapM_some_iff_forall₂.mpr hrst
    cases tl₂ with
    | nil => constructor
    | cons hd₂' tl₂' =>
      constructor
      · cases hrst with | cons h =>
        rename_i hd₁' _ _
        simp only [
          ←hkey _ _ hhd,
          ←hkey _ _ h
        ]
        cases hsorted
        assumption
      · apply ih
        · cases hsorted
          · constructor
          · assumption
        · exact hrst'

/-- The results of `symbolize?` is well-formed. -/
theorem value_symbolize?_wf
  {Γ : TypeEnv} {env : Env}
  {v : Value} {ty : CedarType} {t : Term}
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hwf_ty : ty.WellFormed Γ)
  (hwf_v : v.WellFormed env.entities)
  (hwt_v : InstanceOfType Γ v ty)
  (hsym : v.symbolize? ty = .some t) :
  t.WellFormed (SymEnv.ofEnv Γ).entities
:= by
  have ⟨hwf_Γ, _, _⟩ := hinst
  cases v with
  | prim p =>
    cases p with
    | bool | int | string =>
      simp only [Value.symbolize?, Prim.symbolize, Option.some.injEq] at hsym
      simp only [←hsym]
      repeat constructor
    | entityUID uid =>
      simp only [Value.symbolize?, Prim.symbolize, Option.some.injEq] at hsym
      simp only [←hsym]
      constructor
      constructor
      cases hwf_v with | prim_wf hwf_prim =>
      simp only [Prim.WellFormed] at hwf_prim
      exact env_valid_uid_implies_sym_env_valid_uid hinst hwf_prim
  | set s =>
    cases s with | mk elems =>
    cases hwf_v with | set_wf hwf_elems =>
    unfold Value.symbolize? at hsym
    split at hsym
    any_goals contradiction
    rename_i s' elem_ty heq
    simp only [Value.set.injEq] at heq
    simp only [Option.bind_eq_bind, bind, Option.bind] at hsym
    split at hsym
    contradiction
    rename_i sym_elems hsym_elems
    simp only [Option.some.injEq] at hsym
    simp only [←hsym]
    cases hwf_ty with | set_wf hwf_elem_ty =>
    -- Obligations of `Term.WellFormed` for `.set`
    constructor
    · intros t hmem_t
      simp only [List.mapM₁_eq_mapM (λ x => x.symbolize? elem_ty) s'.toList] at hsym_elems
      have ⟨elem, hmem_elem, hsym_elem⟩ := List.mapM_some_implies_all_from_some
        hsym_elems t ((Set.make_mem _ _).mpr hmem_t)
      simp only [←heq] at hmem_elem
      have hwf_elem := hwf_elems elem hmem_elem
      cases hwt_v with | instance_of_set _ _ hwt_elem =>
      specialize hwt_elem elem hmem_elem
      exact value_symbolize?_wf hinst hwf_elem_ty hwf_elem hwt_elem hsym_elem
    · intros t hmem_t
      simp only [List.mapM₁_eq_mapM (λ x => x.symbolize? elem_ty) s'.toList] at hsym_elems
      have ⟨elem, hmem_elem, hsym_elem⟩ := List.mapM_some_implies_all_from_some
        hsym_elems t ((Set.make_mem _ _).mpr hmem_t)
      simp only [←heq] at hmem_elem
      have hwf_elem := hwf_elems elem hmem_elem
      cases hwt_v with | instance_of_set _ _ hwt_elem =>
      specialize hwt_elem elem hmem_elem
      exact value_symbolize?_well_typed hwf_elem_ty hwt_elem hsym_elem
    · exact ofType_wf hwf_Γ hwf_elem_ty
    · exact Set.make_wf _
  | record rec =>
    cases rec with | mk attrs =>
    cases hwf_v with | record_wf hwf_attrs hwf_attrs_map =>
    unfold Value.symbolize? at hsym
    split at hsym
    any_goals contradiction
    rename_i rec' rty heq_rec'
    simp only [Value.record.injEq] at heq_rec'
    simp only [bind, Option.bind] at hsym
    split at hsym
    contradiction
    rename_i sym_attrs hsym_attrs
    simp only [Option.some.injEq] at hsym
    simp only [←hsym]
    cases hwf_ty with | record_wf hwf_rty_map hwf_rty =>
    cases rty with | mk rty_map =>
    -- Obligations of `Term.WellFormed` for `.record`
    constructor
    · intros attr t hmem_attr_t
      have ⟨attr_term, hmem_attr_term, hsym_attr_term⟩ :=
        List.mapM_some_implies_all_from_some hsym_attrs (attr, t) hmem_attr_t
      simp only [Value.symbolize?.symbolizeAttr?] at hsym_attr_term
      simp only [bind, Option.bind] at hsym_attr_term
      simp [Map.toList, Map.kvs] at hmem_attr_t
      split at hsym_attr_term
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsym_attr_term
        simp only [←hsym_attr_term.2]
        constructor
        have hfind_attr_term := (Map.in_list_iff_find?_some hwf_rty_map).mp hmem_attr_term
        have := hwf_rty _ _ hfind_attr_term
        cases hqty : attr_term.snd
        all_goals
          simp only [hqty] at this
          cases this
          simp only [Qualified.getType]
          apply ofType_wf hwf_Γ
          assumption
      · rename_i val hfind_rec'
        simp only [←heq_rec'] at hfind_rec'
        split at hsym_attr_term
        all_goals
          rename_i ty' hty'
          split at hsym_attr_term
          contradiction
          rename_i sym_val hsym_val
          simp only [Option.some.injEq, Prod.mk.injEq] at hsym_attr_term
          simp only [←hsym_attr_term.2]
          try constructor
          have hwf_ty' : CedarType.WellFormed Γ ty' := by
            have hfind_attr := (Map.in_list_iff_find?_some hwf_rty_map).mp hmem_attr_term
            have := hwf_rty _ _ hfind_attr
            simp only [hty'] at this
            cases this
            assumption
          have hwf_val : val.WellFormed env.entities := hwf_attrs _ _ hfind_rec'
          have hwt_val : InstanceOfType Γ val ty' := by
            cases hwt_v with | instance_of_record _ _ _ hwt_attr =>
            have hfind_rty_attr := (Map.in_list_iff_find?_some hwf_rty_map).mp hmem_attr_term
            simp only [hty'] at hfind_rty_attr
            exact hwt_attr _ _ _ hfind_rec' hfind_rty_attr
          exact value_symbolize?_wf hinst hwf_ty' hwf_val hwt_val hsym_val
    · apply Map.mk_wf
      have hsorted_rty_map :
        List.SortedBy Prod.fst rty_map
      := Map.wf_iff_sorted.mp hwf_rty_map
      -- TODO: merge this with `hsorted_sym_attrs`?
      apply mapM_preserves_SortedBy hsorted_rty_map hsym_attrs
      unfold Value.symbolize?.symbolizeAttr?
      intros a b
      split
      · simp only [Option.some.injEq]
        intros h
        simp [←h]
      · split
        all_goals
          simp only [bind, Option.bind]
          split
          · simp
          · simp only [Option.some.injEq]
            intros h
            simp [←h]
  | ext =>
    simp only [Value.symbolize?, Option.some.injEq] at hsym
    simp only [←hsym]
    repeat constructor
termination_by sizeOf v
decreasing_by
  any_goals
    rename v = Value.set s => h₁
    rename s = Set.mk elems => h₂
    simp [h₁, h₂]
    simp at *
    rename_i h₃ _ _ _ _ _
    simp [←h₃, Set.toList, Set.elts] at hmem_elem
    have := List.sizeOf_lt_of_mem hmem_elem
    omega
  any_goals
    rename v = Value.record rec => h₁
    rename rec = Map.mk attrs => h₂
    rename Value => v'
    rename Map.find? _ attr_term.fst = some _ => h₃
    rename Value.record (Map.mk attrs) = Value.record _ => h₄
    simp [h₁, h₂]
    simp at h₄
    simp [←h₄] at h₃
    have := Map.find?_mem_toList h₃
    simp [Map.toList, Map.kvs] at this
    have := List.sizeOf_lt_of_mem this
    simp at this
    omega

/--
`symbolize?` is the right inverse of `value?`,
on sufficiently well-formed inputs
-/
theorem value?_symbolize?_id
  {Γ : TypeEnv} {entities : Entities}
  {v : Value} {ty : CedarType}
  (hwf_Γ : Γ.WellFormed)
  (hwf_ty : ty.WellFormed Γ)
  (hwf_v : v.WellFormed entities)
  (hwt_v : InstanceOfType Γ v ty) :
  ∃ t,
    v.symbolize? ty = .some t ∧
    t.value? = .some v
:= by
  cases hwt_v with
  | instance_of_bool
  | instance_of_string
  | instance_of_entity
  | instance_of_ext
  | instance_of_int =>
    simp [
      Value.symbolize?, Prim.symbolize,
      Same.same, SameValues,
      Term.value?, TermPrim.value?, BitVec.int64?,
    ]
  | instance_of_set elems elem_ty hwt_elem =>
    cases hwf_ty with | set_wf hwf_elem_ty =>
    cases hwf_v with | set_wf hwf_elem hwf_set_elems =>
    simp only [Value.symbolize?]
    -- Some facts about calling `symbolize?` on the elements
    have hsym_elem_ok (elem : Value) (hmem_elem : elem ∈ elems.toList) :
      ∃ sym_elem,
        elem.symbolize? elem_ty = .some sym_elem
    := by
      have ⟨sym_elem, hsym_elem, _⟩ := value?_symbolize?_id hwf_Γ hwf_elem_ty (hwf_elem elem hmem_elem) (hwt_elem elem hmem_elem)
      exists sym_elem
    have ⟨sym_elems, hsym_elems, hval_sym_elems_id⟩ :
      ∃ sym_elems,
        elems.toList.mapM (λ x => x.symbolize? elem_ty)
        = .some sym_elems ∧
        ∀ sym_elem ∈ sym_elems,
          ∃ elem ∈ elems, sym_elem.value? = .some elem
    := by
      have ⟨sym_elems, hsym_elems⟩ := List.all_some_implies_mapM_some hsym_elem_ok
      simp only [hsym_elems, Option.some.injEq, exists_eq_left']
      intros sym_elem hmem_sym_elem
      have ⟨elem, hmem_elem, hsym_elem⟩ := List.mapM_some_implies_all_from_some hsym_elems sym_elem hmem_sym_elem
      simp only [Set.toList] at hmem_elem
      exists elem
      simp only [(Set.in_list_iff_in_set _ _).mp hmem_elem, true_and]
      have ⟨sym_elem', hsym_elem', hval_sym_elem'⟩ := value?_symbolize?_id hwf_Γ hwf_elem_ty (hwf_elem elem hmem_elem) (hwt_elem elem hmem_elem)
      have : sym_elem' = sym_elem := by
        simp only [hsym_elem', Option.some.injEq] at hsym_elem
        exact hsym_elem
      simp only [this] at hval_sym_elem'
      exact hval_sym_elem'
    -- Some facts about calling `value?` on the symbolized elements
    have hval_sym_elem_ok
      (sym_elem : Term) (hmem_sym_elem : sym_elem ∈ (Set.make sym_elems)) :
        ∃ val_sym_elem,
          sym_elem.value? = .some val_sym_elem
      := by
        have hmem_sym_elem := (Set.make_mem _ _).mpr hmem_sym_elem
        have ⟨elem, hmem_elem, hsym_elem⟩ := List.mapM_some_implies_all_from_some hsym_elems sym_elem hmem_sym_elem
        exists elem
        have ⟨sym_elem', hsym_elem', hval_sym_elem'⟩ := value?_symbolize?_id hwf_Γ hwf_elem_ty (hwf_elem elem hmem_elem) (hwt_elem elem hmem_elem)
        have : sym_elem' = sym_elem := by
          simp only [hsym_elem', Option.some.injEq] at hsym_elem
          exact hsym_elem
        simp only [this] at hval_sym_elem'
        exact hval_sym_elem'
    have ⟨val_sym_elems, hval_sym_elems, hval_sym_elem_inv⟩ :
      ∃ val_sym_elems,
        (Set.make sym_elems).1.mapM Term.value?
        = .some val_sym_elems ∧
        ∀ val_sym_elem ∈ val_sym_elems,
          ∃ sym_elem ∈ sym_elems, val_sym_elem = sym_elem.value?
    := by
      have ⟨val_sym_elems, hval_sym_elems⟩
        := List.all_some_implies_mapM_some hval_sym_elem_ok
      simp only [hval_sym_elems, Option.some.injEq, exists_eq_left']
      intros val_sym_elem hmem_val_sym_elem
      have ⟨sym_elem', hmem_sym_elem', hval_sym_elem'⟩ := List.mapM_some_implies_all_from_some hval_sym_elems val_sym_elem hmem_val_sym_elem
      exists sym_elem'
      simp only [(Set.make_mem _ _).mpr hmem_sym_elem', true_and]
      simp [hval_sym_elem']
    -- Simplify the goal with the facts above
    simp only [
      List.mapM₁_eq_mapM (λ x => x.symbolize? elem_ty) elems.toList,
      hsym_elems,
    ]
    simp only [Option.bind_some_fun, Option.some.injEq, exists_eq_left']
    unfold Term.value?
    simp only [hval_sym_elems, List.mapM₁_eq_mapM _ _]
    simp only [Option.bind_some_fun, Option.some.injEq, Value.set.injEq]
    -- Prove that the sets of values before and after `value? ∘ symbolize?` are equal
    apply (Set.subset_iff_eq (Set.make_wf _) hwf_set_elems).mp
    constructor
    · apply Set.subset_def.mpr
      intros val_sym_elem hmem_val_sym_elem
      replace hmem_val_sym_elem := (Set.make_mem _ _).mpr hmem_val_sym_elem
      have ⟨sym_elem, hmem_sym_elem, hval_sym_elem⟩ := hval_sym_elem_inv val_sym_elem hmem_val_sym_elem
      have ⟨elem', hmem_elem', hval_sym_elem'⟩ := hval_sym_elems_id sym_elem hmem_sym_elem
      simp only [hval_sym_elem', Option.some.injEq] at hval_sym_elem
      simp only [hval_sym_elem, hmem_elem']
    · apply Set.subset_def.mpr
      intros elem hmem_elem
      have ⟨sym_elem, hmem_sym_elem, hsym_elem⟩ := List.mapM_some_implies_all_some hsym_elems elem hmem_elem
      replace hmem_sym_elem := (Set.make_mem _ _).mp hmem_sym_elem
      have ⟨val_sym_elem, hmem_val_sym_elem, hval_sym_elem⟩ := List.mapM_some_implies_all_some hval_sym_elems sym_elem hmem_sym_elem
      have ⟨sym_elem', hsym_elem', hval_sym_elem'⟩ := value?_symbolize?_id hwf_Γ hwf_elem_ty (hwf_elem elem hmem_elem) (hwt_elem elem hmem_elem)
      have : sym_elem' = sym_elem := by
        simp only [hsym_elem', Option.some.injEq] at hsym_elem
        exact hsym_elem
      have : val_sym_elem = elem := by
        simp only [this] at hval_sym_elem'
        simp only [hval_sym_elem', Option.some.injEq] at hval_sym_elem
        simp [hval_sym_elem]
      simp only [this] at hmem_val_sym_elem
      exact (Set.make_mem _ _).mp hmem_val_sym_elem
  | instance_of_record rec rty hrec_mem_implies_rty_mem hwt_rec hrec_required =>
    cases hwf_ty with | record_wf hwf_rty_map hwf_rty =>
    cases hwf_v with | record_wf hwf_rec hwf_rec_map =>
    cases rec with | mk rec_map =>
    cases rty with | mk rty_map =>
    unfold Value.symbolize?
    simp only [Option.bind_eq_bind]
    -- Show that the theorem holds for each attribute
    have value?_symbolize?_attr_id
      {attr : Attr × QualifiedType}
      (hmem_attr : attr ∈ rty_map) :
      ∃ sym_attr opt_val_sym_attrs,
        Value.symbolize?.symbolizeAttr? (Map.mk rec_map) (Map.mk rty_map) attr = some sym_attr ∧
        Term.value?.attrValue? sym_attr.fst sym_attr.snd = some opt_val_sym_attrs ∧
        opt_val_sym_attrs.fst = attr.fst ∧
        ∀ v, opt_val_sym_attrs.snd = some v ↔ (attr.fst, v) ∈ rec_map
    := by
      simp only [Value.symbolize?.symbolizeAttr?]
      split
      · rename_i hfind_rec_attr
        simp only [Option.some.injEq, exists_and_left, Prod.exists, exists_eq_left',
          Term.value?.attrValue?, Prod.mk.injEq]
        exists attr.fst, none
        simp only [and_self, reduceCtorEq, false_iff, true_and]
        intros v hmem_attr
        have := (Map.in_list_iff_find?_some hwf_rec_map).mp hmem_attr
        simp only [this] at hfind_rec_attr
        contradiction
      · rename_i attr_val hfind_rec_attr
        have hwf_attr_val : attr_val.WellFormed entities :=
          hwf_rec attr.fst attr_val hfind_rec_attr
        split
        · rename_i ty' hopt_qty
          have hwf_ty' : ty'.WellFormed Γ := by
            have hfind_attr := (Map.in_list_iff_find?_some hwf_rty_map).mp hmem_attr
            have := hwf_rty attr.fst attr.snd hfind_attr
            simp only [hopt_qty] at this
            cases this
            assumption
          have hwt_attr_val : InstanceOfType Γ attr_val ty' := by
            have hfind_rty_attr := (Map.in_list_iff_find?_some hwf_rty_map).mp hmem_attr
            simp only [hopt_qty] at hfind_rty_attr
            exact hwt_rec attr.fst attr_val (Qualified.optional ty') hfind_rec_attr hfind_rty_attr
          have ⟨sym_attr_val, hsym_attr_val, hval_sym_attr_val⟩ := value?_symbolize?_id hwf_Γ hwf_ty' hwf_attr_val hwt_attr_val
          simp only [hsym_attr_val, Option.bind_some_fun, Option.some.injEq, exists_and_left,
            Prod.exists, exists_eq_left', Term.value?.attrValue?, hval_sym_attr_val, Prod.mk.injEq]
          exists attr.fst, some attr_val
          simp only [and_self, Option.some.injEq, true_and]
          intros v
          constructor
          · intros hv
            simp only [←hv]
            exact (Map.in_list_iff_find?_some hwf_rec_map).mpr hfind_rec_attr
          · intros hmem_v
            have := (Map.in_list_iff_find?_some hwf_rec_map).mp hmem_v
            simp only [hfind_rec_attr, Option.some.injEq] at this
            exact this
        · rename_i ty' hreq_qty
          have hwf_ty' : ty'.WellFormed Γ := by
            have hfind_attr := (Map.in_list_iff_find?_some hwf_rty_map).mp hmem_attr
            have := hwf_rty attr.fst attr.snd hfind_attr
            simp only [hreq_qty] at this
            cases this
            assumption
          have hwt_attr_val : InstanceOfType Γ attr_val ty' := by
            have hfind_rty_attr := (Map.in_list_iff_find?_some hwf_rty_map).mp hmem_attr
            simp only [hreq_qty] at hfind_rty_attr
            exact hwt_rec attr.fst attr_val (Qualified.required ty') hfind_rec_attr hfind_rty_attr
          have ⟨sym_attr_val, hsym_attr_val, hval_sym_attr_val⟩ := value?_symbolize?_id hwf_Γ hwf_ty' hwf_attr_val hwt_attr_val
          simp only [hsym_attr_val, Option.bind_some_fun, Option.some.injEq, exists_and_left,
            Prod.exists, exists_eq_left', Term.value?.attrValue?, Prod.mk.injEq]
          unfold Term.value?.attrValue?
          split
          · have := value_symbolize?_not_some hsym_attr_val (Eq.refl _)
            contradiction
          · have := value_symbolize?_not_none hsym_attr_val (Eq.refl _)
            contradiction
          · simp only [hval_sym_attr_val, Option.bind_some_fun, Option.some.injEq, Prod.mk.injEq]
            exists attr.fst, some attr_val
            simp only [and_self, Option.some.injEq, true_and]
            intros v
            constructor
            · intros hv
              simp only [←hv]
              exact (Map.in_list_iff_find?_some hwf_rec_map).mpr hfind_rec_attr
            · intros hmem_v
              have := (Map.in_list_iff_find?_some hwf_rec_map).mp hmem_v
              simp only [hfind_rec_attr, Option.some.injEq] at this
              exact this
    -- A variation of `value?_symbolize?_attr_id`
    have value?_symbolize?_attr_id'
      {attr : Attr × QualifiedType}
      {sym_attr : Attr × Term}
      {opt_val_sym_attrs : Attr × Option Value}
      (hmem_attr : attr ∈ rty_map)
      (hattr : Value.symbolize?.symbolizeAttr? (Map.mk rec_map) (Map.mk rty_map) attr = some sym_attr)
      (hsym_attr : Term.value?.attrValue? sym_attr.fst sym_attr.snd = some opt_val_sym_attrs) :
      opt_val_sym_attrs.fst = attr.fst ∧
      ∀ v, opt_val_sym_attrs.snd = some v ↔ (attr.fst, v) ∈ rec_map
    := by
      have ⟨sym_attr', opt_val_sym_attrs', h₁, h₂, h₃⟩ := value?_symbolize?_attr_id hmem_attr
      simp only [hattr, Option.some.injEq] at h₁
      simp only [h₁] at hsym_attr
      simp only [hsym_attr, Option.some.injEq] at h₂
      simp [h₁, h₂, h₃]
    have ⟨sym_attrs, hsym_attrs⟩ :
      ∃ sym_attrs,
        List.mapM (Value.symbolize?.symbolizeAttr? (Map.mk rec_map) (Map.mk rty_map)) rty_map
        = .some sym_attrs
    := by
      apply List.all_some_implies_mapM_some
      intros attr hmem_attr
      have ⟨sym_attr, opt_val_sym_attrs, h, _⟩ := value?_symbolize?_attr_id hmem_attr
      simp [h]
    simp only [
      Option.bind, Map.toList, Map.kvs, hsym_attrs,
      Option.some.injEq, exists_eq_left',
      Term.value?,
    ]
    have ⟨val_sym_attrs, hval_sym_attrs⟩ :
      ∃ avs,
        List.mapM (fun x => Term.value?.attrValue? x.fst x.snd) sym_attrs
        = .some avs
    := by
      apply List.all_some_implies_mapM_some
      intros sym_attr hmem_sym_attr
      have ⟨attr, hmem_attr, hsym_attr⟩ := List.mapM_some_implies_all_from_some hsym_attrs sym_attr hmem_sym_attr
      have ⟨sym_attr, opt_val_sym_attrs, h₁, h₂, _⟩ := value?_symbolize?_attr_id hmem_attr
      simp only [hsym_attr, Option.some.injEq] at h₁
      simp only [h₁]
      simp [h₂]
    simp only [
      List.mapM₂_eq_mapM (λ x => Term.value?.attrValue? x.fst x.snd) _,
      hval_sym_attrs,
      Option.bind_some_fun,
      Option.some.injEq, Value.record.injEq,
    ]
    congr
    have hsorted_rty_map :
      List.SortedBy Prod.fst rty_map
    := Map.wf_iff_sorted.mp hwf_rty_map
    have hsorted_sym_attrs :
      List.SortedBy Prod.fst sym_attrs
    := by
      apply mapM_preserves_SortedBy hsorted_rty_map hsym_attrs
      unfold Value.symbolize?.symbolizeAttr?
      intros a b
      split
      · simp only [Option.some.injEq]
        intros h
        simp [←h]
      · split
        all_goals
          simp only [bind, Option.bind]
          split
          · simp
          · simp only [Option.some.injEq]
            intros h
            simp [←h]
    -- `val_sym_attrs`'s keys are still sorted after two `mapM`s
    have hsorted_val_sym_attrs :
      List.SortedBy Prod.fst val_sym_attrs
    := by
      apply mapM_preserves_SortedBy hsorted_sym_attrs hval_sym_attrs
      unfold Term.value?.attrValue?
      intros a b
      split
      any_goals
        simp only [bind, Option.bind]
        split
        · simp
        · intros h
          simp only [Option.some.injEq] at h
          simp [←h]
      · simp only [Option.some.injEq]
        intros h
        simp [←h]
    -- `val_sym_attrs`'s keys are sorted after a `filterMap`
    have hsorted_filt_val_sym_attrs :
      List.SortedBy Prod.fst
      (List.filterMap (fun x => Option.map (Prod.mk x.fst) x.snd) val_sym_attrs)
    := by
      apply List.filterMap_sortedBy _ hsorted_val_sym_attrs
      simp
    -- `rec_map`'s keys are sorted by well-formedness
    have hsorted_rec_map :
      List.SortedBy Prod.fst rec_map
    := Map.wf_iff_sorted.mp hwf_rec_map
    have hequiv :
      (List.filterMap (fun x => Option.map (Prod.mk x.fst) x.snd) val_sym_attrs)
      ≡ rec_map
    := by
      constructor
      · simp only [Subset, List.Subset]
        intros val_sym_attr hmem_val_sym_attr
        have ⟨opt_val_sym_attrs, hmem_opt_val_sym_attr, hopt_val_sym_attrs⟩ := List.mem_filterMap.mp hmem_val_sym_attr
        simp only [Option.map_eq_some_iff] at hopt_val_sym_attrs
        have ⟨val_sym_attrs', hsome_val_sym_attrs, hval_sym_attrs'⟩ := hopt_val_sym_attrs
        have ⟨sym_attr, hmem_sym_attr, hsym_attr⟩ :=
          List.mapM_some_implies_all_from_some hval_sym_attrs opt_val_sym_attrs hmem_opt_val_sym_attr
        have ⟨attr, hmem_attr, hattr⟩ :=
          List.mapM_some_implies_all_from_some hsym_attrs sym_attr hmem_sym_attr
        have ⟨heq, h⟩ := value?_symbolize?_attr_id' hmem_attr hattr hsym_attr
        have := (h val_sym_attrs').mp hsome_val_sym_attrs
        simp only [←hval_sym_attrs', heq, this]
      · simp only [Subset, List.Subset]
        intros attr hmem_attr
        apply List.mem_filterMap.mpr
        have : (Map.mk rec_map).contains attr.fst
        := Map.find?_some_implies_contains ((Map.in_list_iff_find?_some hwf_rec_map).mp hmem_attr)
        have := hrec_mem_implies_rty_mem attr.fst this
        have ⟨attr', hfind_attr'⟩ := Map.contains_iff_some_find?.mp this
        have hmem_attr' := (Map.in_list_iff_find?_some hwf_rty_map).mpr hfind_attr'
        simp only [Map.kvs] at hmem_attr'
        have ⟨sym_attr, hmem_sym_attr, hsym_attr⟩ :=
          List.mapM_some_implies_all_some hsym_attrs (attr.fst, attr') hmem_attr'
        have ⟨val_sym_attr, hmem_val_sym_attr, hval_sym_attr⟩ :=
          List.mapM_some_implies_all_some hval_sym_attrs sym_attr hmem_sym_attr
        have ⟨heq, h⟩ := value?_symbolize?_attr_id' hmem_attr' hsym_attr hval_sym_attr
        have := (h attr.snd).mpr hmem_attr
        exists val_sym_attr
        simp [hmem_val_sym_attr, this, heq]
    exact List.sortedBy_equiv_implies_eq Prod.fst hsorted_filt_val_sym_attrs hsorted_rec_map hequiv
termination_by sizeOf v
decreasing_by
  any_goals
    rename v = Value.set elems => h
    simp [h]
    have := List.sizeOf_lt_of_mem hmem_elem
    cases elems
    simp [Set.toList, Set.elts] at this ⊢
    omega
  any_goals
    rename Value => v'
    rename v = Value.record rec => h₁
    rename rec = Map.mk rec_map => h₂
    rename (Map.mk rec_map).find? attr.fst = some v' => h₃
    simp [h₁, h₂]
    have := Map.find?_mem_toList h₃
    simp only [Map.toList, Map.kvs] at this
    have := List.sizeOf_lt_of_mem this
    simp at this
    omega

theorem env_symbolize?_same_request
  {Γ : TypeEnv} {env : Env}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env.request ∼ ((SymEnv.ofEnv Γ).interpret (env.symbolize? Γ)).request
:= by
  have hwf := hinst.wf_env
  simp only [
    SymEnv.interpret,
    Env.symbolize?,
    SymEnv.ofEnv,
    SymRequest.ofRequestType,
    SymRequest.interpret,
    Request.symbolize?,
    Value.symbolize?,
    Prim.symbolize,
  ]
  and_intros
  all_goals
    simp only [
      beq_iff_eq, Option.bind_eq_bind,
      Term.interpret, TermVar.mk.injEq,
      String.reduceEq,
      false_and, ↓reduceIte,
    ]
  -- Actions match
  · have ⟨_, ⟨_, h, _, _⟩, _⟩ := hinst
    simp [h]
  -- Same context after interpretation
  · have hwf_ctx_ty : (CedarType.record Γ.reqty.context).WellFormed Γ := by
      have ⟨_, _, _, h⟩ := wf_env_implies_wf_request hwf
      exact h
    have hwt_ctx : InstanceOfType Γ env.request.context (.record Γ.reqty.context) := by
      have ⟨_, ⟨_, _, _, h⟩, _⟩ := hinst
      exact h
    have hwf_ctx : (Value.record env.request.context).WellFormed env.entities := by
      have ⟨⟨_, _, _, h⟩, _⟩ := hwf_env
      exact h
    have ⟨sym_ctx, hsym_ctx, hsame_sym_ctx⟩ := value?_symbolize?_id hwf hwf_ctx_ty hwf_ctx hwt_ctx
    simp only [Value.symbolize?, Option.bind_eq_bind] at hsym_ctx

    simp only [Option.bind_eq_bind, hsym_ctx]
    exact hsame_sym_ctx

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

theorem make_map_values_find
  [DecidableEq α] [LT α] [DecidableLT α]
  [Cedar.Data.StrictLT α]
  {l : List α}
  {f : α → β}
  {k : α}
  (hfind : k ∈ l) :
  (Map.make (l.map (λ x => (x, f x)))).find? k =
  .some (f k)
:= by
  apply Map.find?_implies_make_find?
  simp only [List.find?_map, Option.map_eq_some_iff, Prod.mk.injEq]
  unfold Function.comp
  simp only
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp only [List.mem_cons] at hfind
    cases hfind with
    | inl hfind =>
      exists x
      simp [hfind]
    | inr hfind =>
      simp only [List.find?]
      split
      · rename_i heq
        simp only [beq_iff_eq] at heq
        exists x
        simp [heq]
      · exact ih hfind

theorem find?_unique_entry
  {l : List α}
  {f : α → Bool}
  {v : α}
  (hf : ∀ x ∈ l, f x → x = v)
  (hmem : v ∈ l)
  (hv : f v) :
  List.find? f l = .some v
:= by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.mem_cons] at hmem
    simp only [List.find?]
    cases hmem with
    | inl hmem =>
      simp only [hmem] at hv
      simp only [hv, hmem]
    | inr hmem =>
      split
      · rename_i h
        have := hf hd
        simp only [List.mem_cons, true_or, forall_const] at this
        specialize this h
        simp [this]
      · apply ih
        · intros x hmem_x_tl
          have : x ∈ hd :: tl := by simp [hmem_x_tl]
          exact hf x this
        · exact hmem

theorem find?_id
  [BEq α] [LawfulBEq α]
  {l : List α}
  {k : α}
  (hmem : k ∈ l) :
  List.find? (λ x => x == k) l = .some k
:= by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.mem_cons] at hmem
    simp only [List.find?]
    cases hmem with
    | inl hmem => simp [hmem]
    | inr hmem =>
      split
      · rename_i heq
        simp only [beq_iff_eq] at heq
        simp only [heq]
      · exact ih hmem

theorem list_findSome?_unique
  [BEq α] [LawfulBEq α]
  {l : List α} {x : α} {y : β}
  {f : α → Option β}
  (hfind : x ∈ l)
  (hf : ∀ x', (∃ y', f x' = .some y') → x' = x)
  (hx : f x = .some y) :
  l.findSome? f = .some y
:= by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.findSome?]
    simp only [List.mem_cons] at hfind
    cases hfind with
    | inl hfind =>
      simp only [←hfind, hx]
    | inr hfind =>
      split
      · rename_i v' hhd
        simp only [←hx, ←hhd]
        congr
        apply hf
        exists v'
      · exact ih hfind

theorem map_toList_findSome?
  [BEq α] [LawfulBEq α]
  {m : Map α β} {k : α} {v : β} {v' : γ}
  {f : α × β → Option γ}
  (hfind : Map.find? m k = .some v)
  (hf : ∀ kv, (∃ v', f kv = .some v') → kv.1 = k)
  (hkv : f (k, v) = .some v') :
  m.toList.findSome? f = .some v'
:= by
  cases m with | mk m =>
  simp only [Map.toList, Map.kvs, Map.find?] at hfind ⊢
  split at hfind
  · rename_i heq
    simp only [Option.some.injEq] at hfind
    simp [hfind] at heq
    induction m with
    | nil => contradiction
    | cons hd tl ih =>
      simp only [List.findSome?]
      simp only [List.find?] at heq
      split
      · rename_i fhd heq'
        split at heq
        · rename_i heq''
          simp only [Option.some.injEq] at heq
          simp only [beq_iff_eq, heq] at heq''
          simp only [heq''] at heq
          simp only [heq] at heq'
          simp only [heq'] at hkv
          simp [hkv]
        · rename_i heq''
          simp only [beq_eq_false_iff_ne, ne_eq] at heq''
          apply False.elim
          apply heq''
          apply hf
          exists fhd
      · split at heq
        · rename_i h₁ _ h₂
          simp only [beq_iff_eq] at h₂
          simp only [Option.some.injEq] at heq
          simp only [heq] at h₂
          simp only [h₂] at heq
          simp only [heq] at h₁
          simp only [hkv] at h₁
          contradiction
        · exact ih heq
  · contradiction

theorem uuf_attrs_id_inj
  {ety₁ ety₂} :
  UUF.attrs_id ety₁ = UUF.attrs_id ety₂ ↔ ety₁ = ety₂
:= sorry

theorem uuf_ancs_id_inj
  {ety₁ ety₂ ancTy₁ ancTy₂} :
  UUF.ancs_id ety₁ ancTy₁ = UUF.ancs_id ety₂ ancTy₂ ↔ ety₁ = ety₂ ∧ ancTy₁ = ancTy₂
:= sorry

theorem uuf_tag_keys_id_inj
  {ety₁ ety₂} :
  UUF.tag_keys_id ety₁ = UUF.tag_keys_id ety₂ ↔ ety₁ = ety₂
:= sorry

theorem uuf_tag_vals_id_inj
  {ety₁ ety₂} :
  UUF.tag_vals_id ety₁ = UUF.tag_vals_id ety₂ ↔ ety₁ = ety₂
:= sorry

theorem uuf_attrs_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.attrs_id ety₁ ≠ UUF.ancs_id ety₂ ancTy
:= sorry

theorem uuf_attrs_tag_keys_no_confusion
  {ety₁ ety₂} :
  UUF.attrs_id ety₁ ≠ UUF.tag_keys_id ety₂
:= sorry

theorem uuf_attrs_tag_vals_no_confusion
  {ety₁ ety₂} :
  UUF.attrs_id ety₁ ≠ UUF.tag_vals_id ety₂
:= sorry

theorem uuf_tag_vals_tag_keys_no_confusion
  {ety₁ ety₂} :
  UUF.tag_vals_id ety₁ ≠ UUF.tag_keys_id ety₂
:= sorry

theorem uuf_tag_keys_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.tag_keys_id ety₁ ≠ UUF.ancs_id ety₂ ancTy
:= sorry

theorem uuf_tag_vals_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.tag_vals_id ety₁ ≠ UUF.ancs_id ety₂ ancTy
:= sorry

theorem env_symbolize?_lookup_attrs_udf
  {Γ : TypeEnv} {env : Env}
  {ety : EntityType} {entry : StandardSchemaEntry}
  (hfind : Γ.ets.find? ety = .some (.standard entry)) :
  (env.symbolize? Γ).funs {
    id  := UUF.attrs_id ety,
    arg := TermType.ofType (.entity ety),
    out := TermType.ofType (.record entry.attrs),
  } = Entities.symbolizeAttrs?.udf env.entities Γ ety (EntitySchemaEntry.standard entry)
:= by
  simp only [Env.symbolize?, Entities.symbolize?]
  rw [map_toList_findSome? hfind _ _]
  · intros kv hkv
    have ⟨v, hv⟩ := hkv
    simp [
      Entities.symbolizeAttrs?,
      Entities.symbolizeTags?,
      uuf_attrs_id_inj,
      uuf_tag_keys_id_inj,
      uuf_attrs_tag_keys_no_confusion,
      ne_comm.mp uuf_attrs_tag_keys_no_confusion,
      uuf_tag_vals_tag_keys_no_confusion,
      ne_comm.mp uuf_tag_vals_tag_keys_no_confusion,
      uuf_attrs_tag_vals_no_confusion,
      ne_comm.mp uuf_attrs_tag_vals_no_confusion,
    ] at hv
    cases hv with
    | inl hv => simp [hv.1]
    | inr hv =>
      replace hv := hv.2
      simp only [Entities.symbolizeAncs?] at hv
      have ⟨_, _, _, _, h⟩ := List.findSome?_eq_some_iff.mp hv
      simp [uuf_attrs_ancs_no_confusion] at h
  · simp [Entities.symbolizeAttrs?, EntitySchemaEntry.attrs]

theorem env_symbolize?_lookup_tag_keys
  {Γ : TypeEnv} {env : Env}
  {ety : EntityType} {entry : StandardSchemaEntry}
  {tagTy : CedarType}
  (hfind : Γ.ets.find? ety = .some (.standard entry))
  (htags : entry.tags = .some tagTy) :
  (env.symbolize? Γ).funs {
    id := UUF.tag_keys_id ety,
    arg := TermType.ofType (CedarType.entity ety),
    out := TermType.ofType CedarType.string.set,
  } = Entities.symbolizeTags?.keysUDF env.entities Γ ety
:= by
  simp only [Env.symbolize?, Entities.symbolize?]
  rw [map_toList_findSome? hfind _ _]
  · intros kv hkv
    have ⟨v, hv⟩ := hkv
    simp [
      Entities.symbolizeAttrs?,
      Entities.symbolizeTags?,
      uuf_tag_keys_id_inj,
      ne_comm.mp uuf_attrs_tag_keys_no_confusion,
      ne_comm.mp uuf_tag_vals_tag_keys_no_confusion,
    ] at hv
    cases hv with
    | inl hv =>
      simp only [bind, Option.bind] at hv
      split at hv
      contradiction
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hv
      simp [hv.1]
    | inr hv =>
      replace hv := hv.2
      simp only [Entities.symbolizeAncs?] at hv
      have ⟨_, _, _, _, h⟩ := List.findSome?_eq_some_iff.mp hv
      simp [uuf_tag_keys_ancs_no_confusion] at h
  · simp [
      Entities.symbolizeAttrs?,
      Entities.symbolizeTags?,
      EntitySchemaEntry.tags?,
      htags,
      ne_comm.mp uuf_attrs_tag_keys_no_confusion,
    ]

theorem env_symbolize?_lookup_tag_vals
  {Γ : TypeEnv} {env : Env}
  {ety : EntityType} {tagTy : CedarType} {entry : StandardSchemaEntry}
  (hfind : Γ.ets.find? ety = .some (.standard entry))
  (hfind_tagTy : entry.tags = .some tagTy) :
  (env.symbolize? Γ).funs {
    id := UUF.tag_vals_id ety,
    arg := TermType.tagFor ety,
    out := TermType.ofType tagTy
  } = Entities.symbolizeTags?.valsUDF env.entities Γ ety tagTy
:= by
  simp only [Env.symbolize?, Entities.symbolize?]
  rw [map_toList_findSome? hfind _ _]
  · intros kv hkv
    have ⟨v, hv⟩ := hkv
    simp [
      Entities.symbolizeAttrs?,
      Entities.symbolizeTags?,
      uuf_tag_vals_id_inj,
      ne_comm.mp uuf_attrs_tag_keys_no_confusion,
      ne_comm.mp uuf_attrs_tag_vals_no_confusion,
      uuf_tag_vals_tag_keys_no_confusion,
    ] at hv
    cases hv with
    | inl hv =>
      simp only [bind, Option.bind] at hv
      split at hv
      contradiction
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hv
      simp [hv.1]
    | inr hv =>
      replace hv := hv.2
      simp only [Entities.symbolizeAncs?] at hv
      have ⟨_, _, _, _, h⟩ := List.findSome?_eq_some_iff.mp hv
      simp [uuf_tag_vals_ancs_no_confusion] at h
  · simp [
      Entities.symbolizeAttrs?,
      Entities.symbolizeTags?,
      ne_comm.mp uuf_attrs_tag_vals_no_confusion,
      uuf_tag_vals_tag_keys_no_confusion,
      hfind_tagTy,
      EntitySchemaEntry.tags?,
    ]

theorem env_symbolize?_lookup_ancs
  {Γ : TypeEnv} {env : Env}
  {ety : EntityType} {ancTy : EntityType}
  {entry : StandardSchemaEntry}
  (hfind : Γ.ets.find? ety = .some (.standard entry))
  (hfind_ancTy : ancTy ∈ entry.ancestors) :
  (env.symbolize? Γ).funs {
    id := UUF.ancs_id ety ancTy,
    arg := TermType.ofType (CedarType.entity ety),
    out := TermType.ofType (CedarType.entity ancTy).set,
  } = Entities.symbolizeAncs?.udf env.entities Γ ety ancTy
:= by
  simp only [Env.symbolize?, Entities.symbolize?]
  rw [map_toList_findSome? hfind _ _]
  · intros kv hkv
    have ⟨v, hv⟩ := hkv
    simp [
      Entities.symbolizeAttrs?,
      Entities.symbolizeTags?,
      Entities.symbolizeAncs?,
      uuf_tag_vals_id_inj,
      ne_comm.mp uuf_attrs_tag_keys_no_confusion,
      ne_comm.mp uuf_attrs_tag_vals_no_confusion,
      ne_comm.mp uuf_attrs_ancs_no_confusion,
      ne_comm.mp uuf_tag_keys_ancs_no_confusion,
      ne_comm.mp uuf_tag_vals_ancs_no_confusion,
      uuf_tag_vals_tag_keys_no_confusion,
    ] at hv
    have ⟨_, _, _, _, h, _⟩ := List.findSome?_eq_some_iff.mp hv
    split at h
    · rename_i heq
      have := uuf_ancs_id_inj.mp heq.1
      simp [this.1]
    · contradiction
  · simp [
      Entities.symbolizeAttrs?,
      Entities.symbolizeTags?,
      Entities.symbolizeAncs?,
      ne_comm.mp uuf_attrs_tag_vals_no_confusion,
      ne_comm.mp uuf_attrs_ancs_no_confusion,
      ne_comm.mp uuf_tag_keys_ancs_no_confusion,
      ne_comm.mp uuf_tag_vals_ancs_no_confusion,
    ]
    apply list_findSome?_unique hfind_ancTy
    · intros ancTy' hancTy'_mem
      simp only [
        Option.ite_none_right_eq_some,
        Option.some.injEq,
        exists_and_left, exists_eq',
        and_true,
      ] at hancTy'_mem
      simp [uuf_ancs_id_inj.mp hancTy'_mem.1]
    · simp

theorem find?_stronger_pred
  {l : List α} {v : α}
  {f : α → Bool}
  {g : α → Bool}
  (hfind : List.find? f l = .some v)
  (hg : ∀ x ∈ l, g x → f x)
  (hv : g v) :
  List.find? g l = .some v
:= by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.find?]
    cases h : g hd with
    | false =>
      simp only [List.find?] at hfind
      apply ih
      · split at hfind
        · simp only [Option.some.injEq] at hfind
          simp only [hfind, hv] at h
          contradiction
        · exact hfind
      · intros x hmem_x h
        apply hg
        · simp [hmem_x]
        · exact h
    | true =>
      simp only [Option.some.injEq]
      have := hg hd List.mem_cons_self h
      simp only [List.find?] at hfind
      simp only [this, Option.some.injEq] at hfind
      exact hfind

theorem map_find?_to_list_find?
  [BEq α] [LawfulBEq α]
  {m : Map α β} {k : α} {v : β}
  (hfind : Map.find? m k = .some v) :
  List.find? (λ x => x.fst == k) (Map.toList m) = .some (k, v)
:= by
  simp only [Map.find?] at hfind
  split at hfind
  · rename_i heq
    simp only [Option.some.injEq] at hfind
    simp only [Map.toList, heq, hfind]
    have := List.find?_some heq
    simp only [beq_iff_eq] at this
    simp [this]
  · contradiction

theorem map_find?_implies_find?_weaker_pred
  [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
  {m : Map α β} {k : α} {v : β} {f : α × β → Bool}
  (hfind : Map.find? m k = .some v)
  (hf : ∀ kv, f kv → kv.1 = k)
  (hkv : f (k, v)) :
  List.find? f (Map.toList m) = .some (k, v)
:= by
  replace hfind := map_find?_to_list_find? hfind
  cases m with | mk m =>
  simp only [Map.toList, Map.kvs] at hfind ⊢
  induction m with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.find?]
    split
    · rename_i heq
      have := hf hd heq
      simp only [List.find?, this, BEq.rfl, Option.some.injEq] at hfind
      simp [hfind]
    · rename_i heq
      apply ih
      simp only [List.find?] at hfind
      split at hfind
      · simp only [Option.some.injEq] at hfind
        simp only [←hfind] at hkv
        simp [hkv] at heq
      · exact hfind

/--
A technical lemma useful for simplifying `Factory.app`
on some of the `UDF`s in `Env.symbolize?`.
-/
theorem map_make_filterMap_find?
  [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β]
  [DecidableEq γ] [LT γ] [DecidableLT γ] [StrictLT γ]
  {m : Map α β}
  {k : α} {v : β} {k' : γ} {v' : κ}
  {f : α × β → Option (γ × κ)}
  (hfind : m.find? k = .some v)
  (hkv : f (k, v) = .some (k', v'))
  (hf : ∀ kv, (∃ v'', f kv = .some (k', v'')) → kv.1 = k) :
  (Map.make (m.toList.filterMap f)).find? k' = .some v'
:= by
  apply Map.find?_implies_make_find?
  simp only [List.find?_filterMap]
  have :
    List.find? (fun a => Option.any (fun x => x.fst == k') (f a)) m.toList
    = .some (k, v)
  := by
    apply map_find?_implies_find?_weaker_pred hfind
    · intros kv h
      simp only [Option.any] at h
      split at h
      · rename_i f_out heq
        simp at h
        apply hf kv
        exists f_out.snd
        simp only [heq, ←h]
      · contradiction
    · simp [
        Option.any,
        hkv,
      ]
  simp [this, hkv]

theorem map_make_filterMap_flatten_find?
  [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β]
  [DecidableEq γ] [LT γ] [DecidableLT γ] [StrictLT γ]
  {m : Map α β}
  {k : α} {v : β} {k' : γ} {v' : κ}
  {f : α × β → Option (List (γ × κ))}
  (hfind : m.find? k = .some v)
  (hkv : ∃ l, f (k, v) = .some l ∧ l.find? (λ x => x.1 == k') = .some (k', v'))
  (hf : ∀ kv, (∃ l, f kv = .some l ∧ (l.find? (λ x => x.1 == k')).isSome) → kv.1 = k) :
  (Map.make (m.toList.filterMap f).flatten).find? k' = .some v'
:= by
  apply Map.find?_implies_make_find?
  simp only [List.find?_flatten]
  cases m with | mk l =>
  simp only [Map.toList, Map.kvs, Map.find?] at *
  split at hfind
  rotate_left; contradiction
  rename_i heq
  simp only [Option.some.injEq] at hfind
  simp only [hfind] at heq
  have := List.find?_some heq
  simp only [beq_iff_eq] at this
  simp only [this] at heq
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.find?] at heq
    split at heq
    · simp only [Option.some.injEq] at heq
      have ⟨fkv, hfkv, hfind_fkv⟩ := hkv
      simp only [List.filterMap, heq, hfkv]
      simp only [List.findSome?, hfind_fkv]
    · rename_i hne_hd_key
      simp only [List.filterMap]
      split
      · exact ih heq
      · rename_i l' hhd
        simp only [beq_eq_false_iff_ne, ne_eq] at hne_hd_key
        have := hf hd
        have :
          (∃ l, f hd = some l ∧ (List.find? (fun x => x.fst == k') l).isSome = true) → False
        := by
          intros h
          apply hne_hd_key
          apply this h
        simp only [
          beq_iff_eq, Prod.exists,
          exists_and_right, exists_eq_right,
          imp_false, not_exists, not_and,
        ] at this
        have hfind_l' := this l' hhd
        simp only [List.findSome?]
        split
        · rename_i heq
          simp only [heq] at hfind_l'
          simp at hfind_l'
        · exact ih heq

theorem app_table_make_filterMap
  [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β]
  {arg : TermType} {out : TermType} {default : Term}
  {m : Map α β} {k : α} {v : β}
  {t : Term} {r : Term}
  {f : α × β → Option (Term × Term)}
  (hfind : m.find? k = .some v)
  (hkv : f (k, v) = .some (t, r))
  (hf : ∀ kv, (∃ v'', f kv = .some (t, v'')) → kv.1 = k)
  (hlit : t.isLiteral) :
  Factory.app
    (.udf {
      arg := arg,
      out := out,
      table := Map.make (m.toList.filterMap f),
      default := default,
    }) t
  = r
:= by
  simp only [
    Factory.app,
    UnaryFunction.interpret,
    hlit,
    ↓reduceIte,
  ]
  have := map_make_filterMap_find? hfind hkv hf
  simp only [this, Option.some.injEq]

theorem map_keys_empty_implies_map_empty
  {m : Map α β}
  (h : m.keys.toList = []) :
  m = (Map.mk [])
:= by
  cases m with | mk m =>
  cases m with
  | nil => rfl
  | cons hd tl =>
    simp only [Map.keys, Map.kvs, List.map, Set.toList, Set.elts] at h
    contradiction

theorem not_contains_prop_bool_equiv [DecidableEq α] {v : α} {s : Set α} :
  s.contains v = false ↔ v ∉ s
:= by
  constructor
  · intros h hn
    have := Set.contains_prop_bool_equiv.mpr hn
    simp [h] at this
  · intros h
    cases hn : s.contains v with
    | true =>
      have := h (Set.contains_prop_bool_equiv.mp hn)
      contradiction
    | false =>
      rfl

theorem list_mem_implies_find?
  {l : List α} {k : α} {f : α → Bool}
  (hmem : k ∈ l)
  (hk : f k)
  (hf : ∀ k', f k' → k' = k) :
  List.find? f l = .some k
:= by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.mem_cons] at hmem
    simp only [List.find?_cons_eq_some, Bool.not_eq_eq_eq_not, Bool.not_true]
    cases hmem with
    | inl hmem =>
      apply Or.inl
      simp [←hmem, hk]
    | inr hmem =>
      cases hhd : f hd with
      | true =>
        apply Or.inl
        simp [hhd, hf hd hhd]
      | false =>
        apply Or.inr
        simp only [true_and]
        exact ih hmem

theorem env_symbolize?_same_entity_data_standard_same_tag
  {Γ : TypeEnv} {env : Env}
  {uid : EntityUID} {data : EntityData} {entry : StandardSchemaEntry}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hinst_data : InstanceOfEntitySchemaEntry uid data Γ)
  (hfind_entry : Map.find? Γ.ets uid.ty = some (.standard entry))
  (hfind_data : Map.find? env.entities uid = some data) :
  SameTags uid data
    (SymEntityData.interpret
      (env.symbolize? Γ)
      (SymEntityData.ofStandardEntityType uid.ty entry))
:= by
  have ⟨_, ⟨hwf_entities, _⟩⟩ := hwf_env
  have ⟨hwf_data_attrs, _, _, hwf_data_tags_map, hwf_data_tags⟩ := hwf_entities.2 uid data hfind_data
  have ⟨hwf_Γ, _, _⟩ := hinst
  have ⟨entry', hfind_entry', _, hwt_data_attrs, hwt_data_ancs, hwt_data_tags⟩ := hinst_data
  simp only [hfind_entry, Option.some.injEq] at hfind_entry'
  simp only [←hfind_entry', EntitySchemaEntry.attrs] at hwt_data_attrs hwt_data_tags
  simp only [
    SymEntityData.ofStandardEntityType,
    SymEntityData.interpret,
  ]
  simp only [
    SameTags,
    SymEntityData.ofStandardEntityType.symTags,
  ]
  cases hentry_tags : entry.tags with
  | none =>
    simp only [Option.map_none]
    simp only [InstanceOfEntityTags, EntitySchemaEntry.tags?, hentry_tags] at hwt_data_tags
    exact hwt_data_tags
  | some tagTy =>
    have happ_tag_keys :
      Factory.app (UnaryFunction.udf (Entities.symbolizeTags?.keysUDF env.entities Γ uid.ty)) (Term.entity uid)
      = .set (Set.make (data.tags.keys.toList.map λ k => .prim (.string k))) .string
    := by
      apply app_table_make_filterMap hfind_data
      · simp
      · simp
      · simp [Term.isLiteral]
    have hkeys_set_is_literal :
      (Term.set
        (Set.make (List.map (fun k => Term.prim (TermPrim.string k)) data.tags.keys.toList))
        TermType.string).isLiteral
    := by
      unfold Term.isLiteral
      apply List.all_eq_true.mpr
      intros x hmem_x
      have hmem_x := x.property
      have := (Set.make_mem _ _).mpr hmem_x
      have ⟨_, _, hx⟩ := List.mem_map.mp this
      simp [←hx, Term.isLiteral]
    simp only [Option.map_some]
    constructor
    -- Tag key exists iff the symbolic tag key is true
    · intros tag
      simp only [
        SymTags.hasTag,
        SymTags.interpret,
        UnaryFunction.interpret,
        SymEntityData.ofStandardEntityType.symTags,
        env_symbolize?_lookup_tag_keys hfind_entry hentry_tags,
      ]
      simp only [happ_tag_keys, Factory.set.member]
      constructor
      · intros hno_tag
        split
        · rfl
        · rename_i s _ hs_not_emp heq
          simp only [Term.set.injEq] at heq
          replace heq := heq.1
          simp only [
            Term.isLiteral, hkeys_set_is_literal, Bool.and_self,
            ↓reduceIte, Term.prim.injEq,
            TermPrim.bool.injEq,
          ]
          simp only [←heq]
          have :
            ¬((Set.make (List.map (fun k => Term.prim (TermPrim.string k)) data.tags.keys.toList)).contains (Term.string tag) = true)
          := by
            intros h
            have := Set.contains_prop_bool_equiv.mp h
            have := (Set.make_mem _ _).mpr this
            have ⟨_, hmem, heq⟩ := List.mem_map.mp this
            simp only [Term.prim.injEq, TermPrim.string.injEq] at heq
            simp only [heq] at hmem
            have ⟨_, hfind⟩ := Map.in_keys_exists_value hmem
            have := (Map.in_list_iff_find?_some hwf_data_tags_map).mp hfind
            simp only [hno_tag] at this
            contradiction
          simp only [this]
        · rename_i h
          have := h
            (Set.make (List.map (fun k => Term.prim (TermPrim.string k)) data.tags.keys.toList))
            TermType.string
            rfl
          contradiction
      · split
        · rename_i heq
          simp only [Term.set.injEq] at heq
          replace heq := heq.1
          simp only [forall_const]
          have :
            List.map (fun k => Term.prim (TermPrim.string k)) data.tags.keys.toList = []
          := by
            apply (Set.make_empty _).mpr
            simp [heq, Set.isEmpty, Set.empty]
          have := List.map_eq_nil_iff.mp this
          have := map_keys_empty_implies_map_empty this
          simp only [this, Map.find?, List.find?]
        · rename_i s _ _ heq
          simp only [Term.set.injEq] at heq
          replace heq := heq.1
          simp only [
            Term.isLiteral, hkeys_set_is_literal,
            Bool.and_self, ↓reduceIte,
            Term.prim.injEq, TermPrim.bool.injEq,
          ]
          simp only [←heq]
          intros hnot_contains
          have {v} (h : data.tags.find? tag = .some v) :
            False
          := by
            have :
              Term.string tag ∈ Set.make (List.map (fun k => Term.prim (TermPrim.string k)) data.tags.keys.toList)
            := by
              apply (Set.make_mem _ _).mp
              apply List.mem_map.mpr
              exists tag
              simp only [and_true]
              apply Map.in_list_in_keys
              apply (Map.in_list_iff_find?_some hwf_data_tags_map).mpr h
            have := not_contains_prop_bool_equiv.mp hnot_contains this
            contradiction
          cases h : data.tags.find? tag with
          | none => rfl
          | some =>
            have := this h
            contradiction
        · rename_i h
          have := h
            (Set.make (List.map (fun k => Term.prim (TermPrim.string k)) data.tags.keys.toList))
            TermType.string
            rfl
          contradiction
    -- Tag values match
    · intros tag val hfind_tag
      constructor
      · simp only [
          SymTags.hasTag,
          SymTags.interpret,
          UnaryFunction.interpret,
          SymEntityData.ofStandardEntityType.symTags,
          env_symbolize?_lookup_tag_keys hfind_entry hentry_tags,
        ]
        simp only [
          happ_tag_keys,
          Factory.set.member,
        ]
        split
        · rename_i heq
          simp only [Term.set.injEq] at heq
          replace heq := heq.1
          have :
            List.map (fun k => Term.prim (TermPrim.string k)) data.tags.keys.toList = []
          := by
            apply (Set.make_empty _).mpr
            simp [heq, Set.isEmpty, Set.empty]
          have := List.map_eq_nil_iff.mp this
          have := map_keys_empty_implies_map_empty this
          simp [this, Map.find?, List.find?] at hfind_tag
        · rename_i s _ _ heq
          simp only [Term.set.injEq] at heq
          replace heq := heq.1
          simp only [
            Term.isLiteral, hkeys_set_is_literal,
            Bool.and_self, ↓reduceIte,
            Term.prim.injEq, TermPrim.bool.injEq,
          ]
          simp only [←heq]
          simp only [Set.contains_prop_bool_equiv]
          apply (Set.make_mem _ _).mp
          apply List.mem_map.mpr
          exists tag
          simp only [and_true]
          apply Map.in_list_in_keys
          apply (Map.in_list_iff_find?_some hwf_data_tags_map).mpr hfind_tag
        · rename_i h
          have := h
            (Set.make (List.map (fun k => Term.prim (TermPrim.string k)) data.tags.keys.toList))
            TermType.string
            rfl
          contradiction
      · simp only [
          SymEntityData.ofStandardEntityType.symTags,
          SymTags.interpret,
          SymTags.getTag!,
          UnaryFunction.interpret,
          env_symbolize?_lookup_tag_vals hfind_entry hentry_tags,
          Entities.symbolizeTags?.valsUDF,
          SameValues,
        ]
        have hwf_val := hwf_data_tags tag val hfind_tag
        simp only [InstanceOfEntityTags, EntitySchemaEntry.tags?, hentry_tags] at hwt_data_tags
        have hwt_val := hwt_data_tags val (Map.find?_some_implies_in_values hfind_tag)
        have hwf_tagTy : tagTy.WellFormed Γ
        := by
          apply wf_env_implies_wf_tag_type hwf_Γ (ety := uid.ty)
          simp only [EntitySchema.tags?, hfind_entry, Option.map, EntitySchemaEntry.tags?]
          congr
        have ⟨sym_val, hsym_val, hval_sym_val⟩ := value?_symbolize?_id hwf_Γ hwf_tagTy hwf_val hwt_val
        simp only [←hval_sym_val]
        congr
        simp only [
          Factory.app, Factory.tagOf,
          Term.isLiteral, List.cons.sizeOf_spec,
          Prod.mk.sizeOf_spec,
          Term.prim.sizeOf_spec,
          TermPrim.entity.sizeOf_spec,
          TermPrim.string.sizeOf_spec,
          List.nil.sizeOf_spec, List.attach₃,
          List.pmap, List.all_cons,
          List.all, Bool.and_self,
          ↓reduceIte, Option.bind_eq_bind,
        ]
        rw [map_make_filterMap_flatten_find? (v' := sym_val) hfind_data]
        · simp
          have hsym_tag_val_id :
            ∀ tag val,
              (tag, val) ∈ data.tags.toList →
              ∃ sym_val,
                val.symbolize? tagTy = .some sym_val ∧
                sym_val.value? = .some val
          := by
            intros tag val hmem_tag_val
            have hfind_tag_val := (Map.in_list_iff_find?_some hwf_data_tags_map).mp hmem_tag_val
            have hwf_tag_val := hwf_data_tags _ _ hfind_tag_val
            have hwt_tag_val := hwt_data_tags _ (Map.find?_some_implies_in_values hfind_tag_val)
            exact value?_symbolize?_id hwf_Γ hwf_tagTy hwf_tag_val hwt_tag_val
          have ⟨sym_tags, hsym_tags⟩ :
            ∃ sym_tags,
              data.tags.toList.mapM
                (λ x => do
                  some (
                    Term.record (Map.mk [
                      ("entity", Term.prim (TermPrim.entity uid)),
                      ("tag", Term.prim (TermPrim.string x.fst)),
                    ]),
                    ← x.snd.symbolize? tagTy))
              = .some sym_tags
          := by
            apply List.all_some_implies_mapM_some
            intros tag_val hmem_tag_val
            have ⟨sym_tag_val, hsym_tag_val, hval_sym_tag_val⟩ := hsym_tag_val_id tag_val.1 tag_val.2 hmem_tag_val
            simp [hsym_tag_val]
          exists sym_tags
          simp only [Option.bind_eq_bind] at hsym_tags
          simp only [hsym_tags, true_and]
          apply find?_unique_entry
          · simp only [beq_iff_eq, Prod.forall, Prod.mk.injEq]
            intros tag' val' hmem_tag'_val' htag'
            have ⟨_, _, h⟩ := List.mapM_some_implies_all_from_some hsym_tags (tag', val') hmem_tag'_val'
            rename_i tag_val' hmem_tag_val'
            simp only [
              bind, Option.bind,
            ] at h
            split at h
            contradiction
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            simp only [
              ←h.1, Term.record.injEq, Map.mk.injEq,
              List.cons.injEq, Prod.mk.injEq,
              Term.prim.injEq, TermPrim.string.injEq,
              true_and, and_true,
            ]
            rename_i heq
            simp only [h.2] at heq
            have ⟨sym_val', h₁, h₂⟩ := hsym_tag_val_id tag_val'.1 tag_val'.2 hmem_tag_val'
            have heq_tag : tag_val'.fst = tag
            := by
              simp only [htag'] at h
              replace h := h.1
              simp only [
                Term.record.injEq, Map.mk.injEq, List.cons.injEq, Prod.mk.injEq,
                Term.prim.injEq, TermPrim.string.injEq, true_and, and_true,
              ] at h
              exact h
            have heq_val : tag_val'.snd = val
            := by
              have := (Map.in_list_iff_find?_some hwf_data_tags_map).mp hmem_tag_val'
              simp only [heq_tag, hfind_tag, Option.some.injEq] at this
              simp [this]
            simp only [heq_val, hsym_val, Option.some.injEq] at heq
            simp [heq_tag, heq]
          · have := (Map.in_list_iff_find?_some hwf_data_tags_map).mpr hfind_tag
            have ⟨y, hmem_y, hy⟩ := List.mapM_some_implies_all_some hsym_tags (tag, val) this
            simp only [hsym_val, Option.bind_some, Option.some.injEq] at hy
            simp only [←hy] at hmem_y
            exact hmem_y
          · simp
        · intros kv hkv
          have ⟨l, h₁, h₂⟩ := hkv
          simp only [Option.ite_none_right_eq_some] at h₁
          replace h₁ := h₁.2
          have ⟨x, hmem_x, hx⟩ := List.find?_isSome.mp h₂
          have ⟨_, _, h⟩ := List.mapM_some_implies_all_from_some h₁ x hmem_x
          simp only [bind, Option.bind] at h
          split at h
          contradiction
          simp only [Option.some.injEq] at h
          simp only [←h] at hx
          simp only [
            beq_iff_eq, Term.record.injEq, Map.mk.injEq,
            List.cons.injEq, Prod.mk.injEq,
            Term.prim.injEq, TermPrim.entity.injEq, true_and,
            TermPrim.string.injEq, and_true,
          ] at hx
          exact hx.1

theorem env_symbolize?_same_entity_data_standard
  {Γ : TypeEnv} {env : Env}
  {uid : EntityUID} {data : EntityData} {entry : StandardSchemaEntry}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hinst_data : InstanceOfEntitySchemaEntry uid data Γ)
  (hfind_entry : Map.find? Γ.ets uid.ty = some (.standard entry))
  (hfind_data : Map.find? env.entities uid = some data) :
  SameEntityData uid data
    (SymEntityData.interpret
      (env.symbolize? Γ)
      (SymEntityData.ofStandardEntityType uid.ty entry))
:= by
  have ⟨_, ⟨hwf_entities, _⟩⟩ := hwf_env
  have ⟨hwf_data_attrs, _, hwf_data_ancs, hwf_data_tags, _⟩ := hwf_entities.2 uid data hfind_data
  have ⟨hwf_Γ, _, _⟩ := hinst
  have ⟨entry', hfind_entry', _, hwt_data_attrs, hwt_data_ancs, hwt_data_tags⟩ := hinst_data
  simp only [hfind_entry, Option.some.injEq] at hfind_entry'
  simp only [←hfind_entry', EntitySchemaEntry.attrs] at hwt_data_attrs hwt_data_ancs hwt_data_tags
  simp only [
    SymEntityData.ofStandardEntityType,
    SymEntityData.interpret,
  ]
  -- Proof obgligations of `SameEntityData`
  and_intros
  · simp only [
      SymEntityData.ofStandardEntityType.attrsUUF,
      UnaryFunction.interpret,
      env_symbolize?_lookup_attrs_udf hfind_entry,
      Entities.symbolizeAttrs?.udf,
      SameValues,
    ]
    have hwf_attrs_ty : (CedarType.record entry.attrs).WellFormed Γ
    := by
      have : Γ.ets.attrs? uid.ty = some entry.attrs := by
        simp [EntitySchema.attrs?, hfind_entry, EntitySchemaEntry.attrs]
      apply wf_env_implies_wf_attrs hwf_Γ this
    have ⟨sym_attrs, hsym_attrs, hval_sym_attrs⟩ := value?_symbolize?_id hwf_Γ hwf_attrs_ty hwf_data_attrs hwt_data_attrs
    simp only [←hval_sym_attrs]
    congr
    apply app_table_make_filterMap hfind_data
    · simp [EntitySchemaEntry.attrs, hsym_attrs]
    · intros kv hkv
      simp only [
        EntitySchemaEntry.attrs, Option.bind_eq_bind,
        Option.ite_none_right_eq_some,
        exists_and_left,
        bind, Option.bind,
      ] at hkv
      replace ⟨_, ⟨_, hkv⟩⟩ := hkv
      split at hkv
      · contradiction
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq, Term.prim.injEq, TermPrim.entity.injEq] at hkv
        simp [hkv.1]
    · simp [Term.isLiteral]
  · intros anc hmem_anc
    simp only [SameEntityData.InSymAncestors]
    have hfind_ancTy := hwt_data_ancs anc hmem_anc
    simp only [EntitySchemaEntry.ancestors] at hfind_ancTy
    exists UnaryFunction.interpret (env.symbolize? Γ) (SymEntityData.ofStandardEntityType.ancsUUF uid.ty anc.ty)
    constructor
    · apply Map.find?_mapOnValues_some
      apply Map.find?_implies_make_find?
      simp only [List.find?_map]
      unfold Function.comp
      simp only
      have : List.find? (λ x => x == anc.ty) entry.ancestors.toList = .some anc.ty
      := by apply list_mem_implies_find? hfind_ancTy <;> simp
      simp only [this, Option.map]
    · simp only [
        SymEntityData.ofStandardEntityType.ancsUUF,
        UnaryFunction.interpret,
        env_symbolize?_lookup_ancs hfind_entry hfind_ancTy,
        Entities.symbolizeAncs?.udf,
      ]
      exists (Set.make (List.filterMap
        (λ anc' =>
          if anc'.ty = anc.ty then
            .some (.prim (.entity anc'))
          else
            .none)
        data.ancestors.toList))
      constructor
      · apply app_table_make_filterMap hfind_data
        · simp
        · simp
        · simp only [Term.isLiteral]
      · apply (Set.make_mem _ _).mp
        apply List.mem_filterMap.mpr
        exists anc
        constructor
        · exact hmem_anc
        · simp
  · simp only
    intros ancTy ancUF hancUF
    simp only [
      SameEntityData.InAncestors,
    ]
    have ⟨uuf, huuf, hancUF⟩ := Map.find?_mapOnValues_some' _ hancUF
    have := (Map.in_list_iff_find?_some (Map.make_wf _)).mpr huuf
    have := Map.make_mem_list_mem this
    have ⟨_, hmem_ancTy, heq⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq
    replace huuf := heq.2
    simp only [heq.1] at huuf hmem_ancTy
    simp only [←huuf] at hancUF
    simp only [
      hancUF,
      SymEntityData.ofStandardEntityType.ancsUUF,
      UnaryFunction.interpret,
      env_symbolize?_lookup_ancs hfind_entry hmem_ancTy,
      Entities.symbolizeAncs?.udf,
    ]
    exists (Set.make (List.filterMap
      (λ anc =>
        if anc.ty = ancTy then
          .some (.prim (.entity anc))
        else
          .none)
      data.ancestors.toList))
    constructor
    · apply app_table_make_filterMap hfind_data
      · simp
      · simp
      · simp only [Term.isLiteral]
    · intros anc_term hmem_anc_term
      have := (Set.make_mem _ _).mpr hmem_anc_term
      have ⟨anc', hmem_anc', heq⟩ := List.mem_filterMap.mp this
      exists anc'
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at heq
      simp only [←heq, true_and]
      exact hmem_anc'
  · exact env_symbolize?_same_entity_data_standard_same_tag
      hwf_env hinst hinst_data hfind_entry hfind_data

theorem env_symbolize?_same_entity_data_enum
  {Γ : TypeEnv} {env : Env}
  {uid : EntityUID} {data : EntityData} {eids : Set String}
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hinst_data : InstanceOfEntitySchemaEntry uid data Γ)
  (hfind_entry : Map.find? Γ.ets uid.ty = some (.enum eids)) :
  SameEntityData uid data
    (SymEntityData.interpret
      (env.symbolize? Γ)
      (SymEntityData.ofEnumEntityType uid.ty eids))
:= by
  have ⟨hwf_Γ, _, _⟩ := hinst
  have ⟨entry', hfind_entry', _, hwt_data_attrs, hwt_data_ancs, hwt_data_tags⟩ := hinst_data
  simp only [hfind_entry, Option.some.injEq] at hfind_entry'
  simp only [←hfind_entry'] at hwt_data_attrs hwt_data_ancs hwt_data_tags
  simp only [
    SymEntityData.interpret,
    SymEntityData.ofEnumEntityType,
  ]
  have hemp_data_ancs : data.ancestors = (Set.mk [])
  := by
    simp only [EntitySchemaEntry.ancestors, Set.empty] at hwt_data_ancs
    cases h : data.ancestors with | mk ancs =>
    cases ancs with
    | nil => rfl
    | cons anc ancs =>
      simp only [h] at hwt_data_ancs
      have : anc ∈ Set.mk (anc :: ancs) := by
        apply Set.mem_cons_self
      have := hwt_data_ancs anc this
      contradiction
  -- Proof obgligations of `SameEntityData`
  and_intros
  · simp only [
      SymEntityData.emptyAttrs,
      UnaryFunction.interpret,
      Factory.app,
      Term.isLiteral,
      ↓reduceIte,
      Map.empty,
      Map.find?,
      List.find?
    ]
    simp only [EntitySchemaEntry.attrs, Map.empty] at hwt_data_attrs
    cases hwt_data_attrs with | instance_of_record rec rty h₁ h₂ h₃ =>
    have hemp_data_attrs : data.attrs = (Map.mk [])
    := by
      cases h : data.attrs with | mk attrs =>
      cases attrs with
      | nil => rfl
      | cons attr attrs =>
        simp only [h] at h₁
        have := h₁ attr.1
        simp [Map.contains, Map.find?, List.find?] at this
    simp [
      hemp_data_attrs,
      SameValues,
      Term.value?,
      List.mapM₂,
      List.attach₂,
    ]
  · simp only [hemp_data_ancs]
    intros anc hmem_anc
    contradiction
  · intros ancTy ancUF
    simp [Map.empty, Map.mapOnValues, List.map, Map.find?, List.find?]
  · simp only [SameTags, Option.map_none]
    simp only [InstanceOfEntityTags, EntitySchemaEntry.tags?] at hwt_data_tags
    exact hwt_data_tags

theorem env_symbolize?_same_entities_ordinary
  {Γ : TypeEnv} {env : Env}
  {uid : EntityUID} {data : EntityData}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hinst_data : InstanceOfEntitySchemaEntry uid data Γ)
  (hfind_data : Map.find? env.entities uid = some data) :
  ∃ δ,
    Map.find?
      (SymEnv.interpret (env.symbolize? Γ) (SymEnv.ofEnv Γ)).entities
      uid.ty = some δ ∧
    SameEntityData uid data δ
:= by
  have ⟨hwf_Γ, _, _⟩ := hinst
  have ⟨entry, hfind_entry, _⟩ := hinst_data
  have := ofSchema_find?_ets hfind_entry
  simp only [
    SymEnv.interpret,
    SymEnv.ofEnv,
    SymEntities.interpret,
    SymEntities.ofSchema,
  ]
  have hfind_interp_entry :
    (Map.mapOnValues
      (SymEntityData.interpret (env.symbolize? Γ))
      (Map.make
        (
          List.map (λ x => (x.fst, SymEntityData.ofEntityType x.fst x.snd)) (Map.toList Γ.ets) ++
          List.map
            (λ actTy =>
              (actTy,
                SymEntityData.ofActionType actTy (List.map (λ x => x.fst.ty) (Map.toList Γ.acts)).eraseDups
                  Γ.acts))
            (List.map (λ x => x.fst.ty) (Map.toList Γ.acts)).eraseDups
        )
      )
    ).find? uid.ty = .some (SymEntityData.interpret (env.symbolize? Γ) (SymEntityData.ofEntityType uid.ty entry))
  := by
    simp only [← Map.find?_mapOnValues, Option.map_eq_some_iff]
    exists SymEntityData.ofEntityType uid.ty entry
  simp only [hfind_interp_entry, Option.some.injEq, exists_eq_left']
  simp only [SymEntityData.ofEntityType]
  have hwf_entry := wf_env_implies_wf_entity_entry hwf_Γ hfind_entry
  cases entry with
  | standard entry =>
    simp only
    exact env_symbolize?_same_entity_data_standard hwf_env hinst hinst_data hfind_entry hfind_data
  | enum es =>
    simp only
    exact env_symbolize?_same_entity_data_enum hinst hinst_data hfind_entry

theorem env_symbolize?_same_entities_action
  {Γ : TypeEnv} {env : Env}
  {uid : EntityUID} {data : EntityData}
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hinst_data : InstanceOfActionSchemaEntry uid data Γ) :
  ∃ δ,
    Map.find?
      (SymEnv.interpret (env.symbolize? Γ) (SymEnv.ofEnv Γ)).entities
      uid.ty = some δ ∧
    SameEntityData uid data δ
:= by
  have ⟨hwf_Γ, _, _⟩ := hinst
  have ⟨hattrs_emp, htags_emp, ⟨entry, hfind_entry, heq_ancs⟩⟩ := hinst_data
  simp only [
    SymEnv.interpret,
    SymEntities.interpret,
    SymEnv.ofEnv,
  ]
  simp only [←(Map.find?_mapOnValues _ _ _)]
  have hwf_acts := wf_env_implies_wf_acts_map hwf_Γ
  have := ofSchema_find?_acts hwf_Γ hfind_entry
  simp only [this, Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [
    SymEntityData.ofActionType,
    SymEntityData.interpret,
    UnaryFunction.interpret,
    SymEntityData.emptyAttrs,
    Option.map,
  ]
  -- Simplifying terms like `(SymEntityData.ofActionType.ancsUDF _ _).table.find? ...`
  have hf_ancs_find {ancTy : EntityType} :
    (Map.make
      (List.filterMap
        (λ x : EntityUID × ActionSchemaEntry =>
          (SymEntityData.ofActionType.termOfType? uid.ty x.fst).bind
          λ t => some (t, SymEntityData.ofActionType.ancsTerm ancTy x.snd.ancestors.toList))
        (Map.toList Γ.acts))).find?
      (Term.prim (TermPrim.entity uid))
    = .some (.set
      (Set.make (List.filterMap (SymEntityData.ofActionType.termOfType? ancTy) entry.ancestors.toList))
      (TermType.entity ancTy))
  := by
    apply Map.find?_implies_make_find?
    simp only [List.find?_filterMap]
    have :
      (List.find?
        (λ a => Option.any
          (λ x => x.fst == Term.prim (TermPrim.entity uid))
          ((SymEntityData.ofActionType.termOfType? uid.ty a.fst).bind
            λ t => some (t, SymEntityData.ofActionType.ancsTerm ancTy a.snd.ancestors.toList)))
        (Map.toList Γ.acts))
      = .some (uid, entry)
    := by
      apply find?_unique_entry
      · intros x hmem_x hfilter
        simp only [
          SymEntityData.ofActionType.termOfType?,
          Option.any,
        ] at hfilter
        split at hfilter
        · rename_i v hv
          split at hv
          · rename_i heq_ty
            simp only [Option.bind_some, Option.some.injEq] at hv
            cases v
            rename_i v₁ v₂
            simp only [beq_iff_eq] at hfilter
            simp only [
              hfilter,
              Prod.mk.injEq, Term.prim.injEq,
              TermPrim.entity.injEq,
            ] at hv
            cases x
            rename_i x₁ x₂
            have := (Map.in_list_iff_find?_some hwf_acts).mp hmem_x
            simp only at hv
            simp only [hv.1] at this
            simp only [hfind_entry, Option.some.injEq] at this
            simp only [←this, hv.1]
          · contradiction
        · contradiction
      · exact (Map.in_list_iff_find?_some hwf_acts).mpr hfind_entry
      · simp [
          SymEntityData.ofActionType.termOfType?,
        ]
    simp only [this, Option.bind_some]
    simp [
      SymEntityData.ofActionType.termOfType?,
      SymEntityData.ofActionType.ancsTerm,
      Factory.setOf,
        TermType.ofType,
    ]
  -- Prove obligations of `SameEntityData`
  and_intros
  · simp only [
      Factory.app,
      Map.empty,
      Map.find?,
      List.find?,
      Term.isLiteral,
      ↓reduceIte,
    ]
    simp [
      hattrs_emp,
      SameValues,
      Term.value?,
      List.attach₂,
      List.mapM₂,
      Map.empty,
    ]
  -- Same ancestor map
  · intros anc hmem_anc
    simp only [SameEntityData.InSymAncestors]
    simp only [←(Map.find?_mapOnValues _ _ _)]
    have :
      (Map.make
        (List.map
          (λ ancTy => (ancTy, SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts ancTy))
          (List.map (λ x => x.fst.ty)
            (Map.toList Γ.acts)).eraseDups)).find?
          anc.ty
      = .some (SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts anc.ty)
    := by
      apply make_map_values_find
      apply List.mem_implies_mem_eraseDups
      apply List.mem_map.mpr
      simp only [heq_ancs] at hmem_anc
      have ⟨anc_entry, hfind_anc, _⟩ := wf_env_implies_wf_action_entity_ancestor hwf_Γ hfind_entry hmem_anc
      exists (anc, anc_entry)
      constructor
      · apply (Map.in_list_iff_find?_some hwf_acts).mpr
        exact hfind_anc
      · simp
    simp only [this]
    simp only [
      Option.map, UnaryFunction.interpret,
      SymEntityData.ofActionType.ancsUDF,
      Option.bind_eq_bind, Option.some.injEq,
      exists_eq_left',
      Factory.app,
      Term.isLiteral,
      ↓reduceIte,
    ]
    -- generalize hf_ancs_term : (λ x : EntityUID × ActionSchemaEntry =>
    --   (SymEntityData.ofActionType.termOfType? uid.ty x.fst).bind
    --   fun t => some (t, SymEntityData.ofActionType.ancsTerm anc.ty x.snd.ancestors.toList)) = f_ancs_term
    exists Set.make (entry.ancestors.toList.filterMap
      (SymEntityData.ofActionType.termOfType? anc.ty))
    simp only [hf_ancs_find, true_and]
    apply (Set.make_mem _ _).mp
    apply List.mem_filterMap.mpr
    exists anc
    constructor
    · simp only [heq_ancs] at hmem_anc
      exact hmem_anc
    · simp only [SymEntityData.ofActionType.termOfType?, ↓reduceIte]
  · simp only
    intros ancTy ancUF hancUF
    have hancUF :
      ancUF = SymEntityData.ofActionType.ancsUDF uid.ty Γ.acts ancTy
    := by
      simp only [←Map.find?_mapOnValues] at hancUF
      simp only [Option.map_eq_some_iff] at hancUF
      have ⟨ancUF', hancUF', heq_ancUF⟩ := hancUF
      have := Map.find?_mem_toList hancUF'
      have := Map.make_mem_list_mem this
      have ⟨_, _, h⟩ := List.mem_map.mp this
      simp only [Prod.mk.injEq] at h
      simp only [h.1, true_and] at h
      simp only [h]
      simp only [←h] at heq_ancUF
      simp only [UnaryFunction.interpret] at heq_ancUF
      split at heq_ancUF
      · rename_i heq
        simp only [SymEntityData.ofActionType.ancsUDF] at heq
        contradiction
      · rename_i heq
        simp only [h] at heq
        simp only [heq_ancUF] at heq
        simp [heq]
    simp only [
      SameEntityData.InAncestors,
      hancUF,
      Factory.app,
      SymEntityData.ofActionType.ancsUDF,
      Term.isLiteral,
      ↓reduceIte,
    ]
    simp only [Option.bind_eq_bind, hf_ancs_find, Term.set.injEq, and_true, exists_eq_left']
    intros anc_term hmem_anc_term
    have hmem_anc_term := (Set.make_mem _ _).mpr hmem_anc_term
    have ⟨anc, hmem_anc, hanc_term⟩ := List.mem_filterMap.mp hmem_anc_term
    exists anc
    simp only [
      SymEntityData.ofActionType.termOfType?,
      Option.ite_none_right_eq_some,
      Option.some.injEq,
    ] at hanc_term
    simp only [hanc_term.2, true_and, heq_ancs]
    exact hmem_anc
  · simp only [SameTags, htags_emp]

theorem env_symbolize?_same_entities
  {Γ : TypeEnv} {env : Env}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env.entities ∼ ((SymEnv.ofEnv Γ).interpret (env.symbolize? Γ)).entities
:= by
  intros uid data hfind_uid_data
  have ⟨hwf_Γ, _, ⟨hinst_data, _⟩⟩ := hinst
  specialize hinst_data uid data hfind_uid_data
  cases hinst_data with
  | inl hinst_data =>
    exact env_symbolize?_same_entities_ordinary hwf_env hinst hinst_data hfind_uid_data
  | inr hinst_data =>
    exact env_symbolize?_same_entities_action hinst hinst_data

theorem env_symbolize?_same
  {Γ : TypeEnv} {env : Env}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env ∼ (SymEnv.ofEnv Γ).interpret (env.symbolize? Γ)
:= by
  constructor
  · exact env_symbolize?_same_request hwf_env hinst
  · exact env_symbolize?_same_entities hwf_env hinst

/--
`Decoder.defaultLit` is well-formed if given
sufficiently well-formed `eidOf` and `ty`.
-/
theorem default_lit_wf
  {εs : SymEntities}
  {eidOf : EntityType → String} {ty : TermType}
  (hwf_ty : ty.WellFormed εs)
  (hwf_eidOf : ∀ ety, εs.isValidEntityType ety → εs.isValidEntityUID { ty := ety, eid := eidOf ety }) :
  (Decoder.defaultLit eidOf ty).WellFormed εs
:= by
  cases ty with
  | prim p =>
    simp only [Decoder.defaultLit]
    constructor
    cases p with
    | bool | bitvec | string =>
      simp only [Decoder.defaultPrim]
      constructor
    | entity uid =>
      simp only [Decoder.defaultPrim]
      constructor
      apply hwf_eidOf
      cases hwf_ty
      assumption
    | ext e =>
      cases e
      all_goals
        simp only [Decoder.defaultPrim, Decoder.defaultExt]
        constructor
  | option ty' =>
    simp only [Decoder.defaultLit]
    constructor
    cases hwf_ty
    assumption
  | set ty' =>
    simp only [Decoder.defaultLit]
    constructor
    · intros t ht
      simp only [Set.empty, Membership.mem, Set.elts] at ht
      contradiction
    · intros t ht
      simp only [Set.empty, Membership.mem, Set.elts] at ht
      contradiction
    · cases hwf_ty
      assumption
    · exact Set.empty_wf
  | record rty =>
    cases rty with | mk attrs =>
    cases hwf_ty with | record_wf hwf_rty hwf_rty_map =>
    simp only [Decoder.defaultLit]
    constructor
    · intros attr t hmem_attr_t
      simp only [Map.toList, Map.kvs] at hmem_attr_t
      have ⟨attr_ty, hmem_attr_ty, h⟩ := List.mem_map.mp hmem_attr_t
      simp only [Prod.mk.injEq] at h
      simp only [←h.2]
      apply default_lit_wf _ hwf_eidOf
      apply hwf_rty attr_ty.1.1
      simp only [List.attach₂] at hmem_attr_ty
      have ⟨attr_ty₁, hmem_attr_ty₁, heq⟩ := List.mem_pmap.mp hmem_attr_ty
      cases attr_ty₁ with | mk a b =>
      simp only [←heq]
      exact (Map.in_list_iff_find?_some hwf_rty_map).mp hmem_attr_ty₁
    · simp only [List.map_attach₂ (λ x => (x.fst, Decoder.defaultLit eidOf x.snd))]
      apply Map.mapOnValues_wf.mp
      exact hwf_rty_map
termination_by sizeOf ty
decreasing_by
  have : ty = TermType.record rty := by assumption
  simp only [this]
  have : rty = Map.mk attrs := by assumption
  simp only [this]
  simp
  have h := attr_ty.property
  calc
    sizeOf attr_ty.1.snd < 1 + sizeOf attrs := by assumption
    _ < 1 + (1 + sizeOf attrs) := by omega

theorem default_lit_is_lit
  {eidOf : EntityType → String} {ty : TermType} :
  (Decoder.defaultLit eidOf ty).isLiteral
:= by
  cases ty with
  | prim p =>
    cases p
    all_goals
      simp only [Decoder.defaultLit, Decoder.defaultPrim, Term.isLiteral]
  | record rty =>
    cases rty with | mk attrs =>
    simp only [Decoder.defaultLit, Term.isLiteral]
    rw [List.map_attach₂ (λ x => (x.fst, Decoder.defaultLit eidOf x.snd))]
    simp only [List.attach₃]
    rw [List.all_pmap_subtype
      (λ x => x.snd.isLiteral)
      (List.map (fun x => (x.fst, Decoder.defaultLit eidOf x.snd)) attrs)]
    apply List.all_eq_true.mpr
    intros attr_term hmem_attr_term
    have ⟨attr, hmem_attr, hattr_term⟩ := List.mem_map.mp hmem_attr_term
    simp only [←hattr_term]
    exact default_lit_is_lit
  | _ => simp [Decoder.defaultLit, Term.isLiteral, Set.empty]
termination_by sizeOf ty
decreasing_by
  simp
  have := List.sizeOf_lt_of_mem hmem_attr
  cases attr
  simp at this ⊢
  omega

theorem list_map_id_eq
  {l : List α}
  {f : α → α}
  (hf : ∀ x ∈ l, f x = x) :
  l.map f = l
:= by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · apply hf x
      simp
    · apply ih
      intros x hmem_x
      apply hf
      simp [hmem_x]

theorem default_lit_well_typed
  {eidOf : EntityType → String} {ty : TermType} :
  (Decoder.defaultLit eidOf ty).typeOf = ty
:= by
  cases ty with
  | prim p =>
    cases p with
    | ext x =>
      cases x
      all_goals
        simp only [Decoder.defaultLit, Decoder.defaultPrim, Term.typeOf, TermPrim.typeOf, Decoder.defaultExt]
    | _ =>
      simp only [Decoder.defaultLit, Decoder.defaultPrim, Term.typeOf, TermPrim.typeOf, BitVec.width]
  | option =>
    simp only [Decoder.defaultLit, Decoder.defaultPrim, Term.typeOf]
  | set =>
    simp only [Decoder.defaultLit, Decoder.defaultPrim, Term.typeOf]
  | record rty =>
    cases rty with | mk attrs =>
    simp only [Decoder.defaultLit, Decoder.defaultPrim, Term.typeOf]
    congr
    rw [List.map_attach₂ (λ x => (x.fst, Decoder.defaultLit eidOf x.snd))]
    simp only [List.map_attach₃_snd]
    simp only [List.map_map]
    unfold Function.comp
    simp only
    apply list_map_id_eq
    intros x hmem_x
    cases x with | mk a b =>
    simp only [Prod.mk.injEq, true_and]
    exact default_lit_well_typed
termination_by sizeOf ty
decreasing_by
  simp
  have := List.sizeOf_lt_of_mem hmem_x
  simp at this ⊢
  omega

theorem default_lit_wf'
  {Γ : TypeEnv} {ty : TermType}
  (hwf_Γ : Γ.WellFormed)
  (hwf_ty : ty.WellFormed (SymEnv.ofEnv Γ).entities) :
  (defaultLit' Γ ty).WellFormed (SymEnv.ofEnv Γ).entities
:= by
  apply default_lit_wf hwf_ty
  intros ety hety
  simp only [SymEntities.isValidEntityType, Map.contains, Option.isSome] at hety
  split at hety
  · rename_i δ hfind_δ
    simp only [SymEntities.isValidEntityUID, hfind_δ, defaultEidOf]
    split
    · rename_i eids hmembers
      simp only [hmembers]
      split
      · rename_i hempty_eids
        replace hempty_eids : eids = (Set.mk []) := by
          cases eids with | mk eids' =>
          simp only [Set.toList, Set.elts] at hempty_eids
          simp [hempty_eids]
        -- `eids` should not be empty
        simp only [SymEnv.ofEnv, SymEntities.ofSchema] at hfind_δ
        have := Map.make_mem_list_mem (Map.find?_mem_toList hfind_δ)
        have := List.mem_append.mp this
        cases this with
        | inl hmem_ets =>
          have ⟨⟨ety', entry'⟩, hmem_ety', h⟩ := List.mem_map.mp hmem_ets
          simp only [Prod.mk.injEq] at h
          cases entry' with
          | standard =>
            replace h := h.2
            simp only [
              SymEntityData.ofEntityType,
              SymEntityData.ofStandardEntityType,
            ] at h
            simp only [←h] at hmembers
            contradiction
          | enum eids' =>
            simp only [
              ←h.2, h.1,
              SymEntityData.ofEntityType,
              SymEntityData.ofEnumEntityType,
              Option.some.injEq,
              hempty_eids,
            ] at hmembers
            have := (Map.in_list_iff_find?_some (wf_env_implies_wf_ets_map hwf_Γ)).mp hmem_ety'
            have := wf_env_implies_wf_entity_entry hwf_Γ this
            simp only [EntitySchemaEntry.WellFormed, Bool.not_eq_true] at this
            have h := this.2
            simp [hmembers, Set.isEmpty, Set.empty] at h
        | inr hmem_acts =>
          have ⟨ety', hmem_ety', h⟩ := List.mem_map.mp hmem_acts
          simp only [Prod.mk.injEq] at h
          simp only [
            ←h.2, h.1,
            SymEntityData.ofActionType,
            SymEntityData.ofActionType.acts,
            Option.some.injEq,
            hempty_eids,
          ] at hmembers
          have hemp :
            List.filterMap (fun x => if x.fst.ty = ety then some x.fst.eid else none) (Map.toList Γ.acts)
            = []
          := by
            apply (Set.make_empty _).mpr
            simp only [Set.isEmpty, Set.empty, beq_iff_eq, hmembers]
          have := List.mem_eraseDups_implies_mem hmem_ety'
          have ⟨act, hmem_act, hact_ty⟩ := List.mem_map.mp this
          simp only [h.1] at hact_ty
          have := List.filterMap_empty_iff_all_none.mp hemp act hmem_act
          simp only [hact_ty, ↓reduceIte] at this
          contradiction
      · rename_i eid _ hhead
        simp only [Set.toList] at hhead
        simp [Set.contains, hhead]
    · rfl
  · contradiction

theorem value_symbolize?_is_lit
  {v : Value} {ty : CedarType} {t : Term}
  (hsym : v.symbolize? ty = .some t) :
  t.isLiteral
:= by
  cases v with
  | prim p =>
    cases p with
    | bool | int | string | entityUID =>
      simp only [Value.symbolize?, Prim.symbolize, Option.some.injEq] at hsym
      simp only [←hsym, Term.isLiteral]
  | set elems =>
    unfold Value.symbolize? at hsym
    split at hsym
    any_goals contradiction
    rename_i elems' ty' helems'
    simp only [bind, Option.bind] at hsym
    split at hsym
    any_goals contradiction
    simp only [Option.some.injEq] at hsym
    rename_i sym_elems hsym_elems
    cases hsym_elems_set : Set.make sym_elems with | mk sym_elems_set =>
    simp only [←hsym, hsym_elems_set, Term.isLiteral]
    apply List.all_eq_true.mpr
    intros x hmem_x
    replace hmem_x := x.property
    simp only [List.mapM₁_eq_mapM (fun x => x.symbolize? ty') elems'.toList] at hsym_elems
    replace hmem_x := (Set.in_list_iff_in_mk _ _).mp hmem_x
    simp only [←hsym_elems_set] at hmem_x
    replace hmem_x := (Set.make_mem _ _).mpr hmem_x
    have ⟨sym_elem, _, hsym_elem⟩ := List.mapM_some_implies_all_from_some hsym_elems x.val hmem_x
    exact value_symbolize?_is_lit hsym_elem
  | record rec =>
    unfold Value.symbolize? at hsym
    split at hsym
    any_goals contradiction
    rename_i attrs' rty hattrs'
    simp only [bind, Option.bind] at hsym
    split at hsym
    any_goals contradiction
    simp only [Option.some.injEq] at hsym
    rename_i sym_attrs hsym_attrs
    simp only [←hsym, Term.isLiteral]
    apply List.all_eq_true.mpr
    intros x hmem_x
    simp only [List.attach₃] at hmem_x
    replace ⟨_, hmem_x, h⟩ := List.mem_pmap.mp hmem_x
    replace hmem_x : x.val ∈ sym_attrs := by simp only [←h, hmem_x]
    have ⟨sym_elem, _, hsym_elem⟩ := List.mapM_some_implies_all_from_some hsym_attrs x.val hmem_x
    simp only [Value.symbolize?.symbolizeAttr?] at hsym_elem
    split at hsym_elem
    · simp only [Option.some.injEq] at hsym_elem
      simp only [←hsym_elem, Term.isLiteral]
    · split at hsym_elem
      all_goals
        simp only [bind, Option.bind] at hsym_elem
        split at hsym_elem
        contradiction
        rename_i hsym_elem'
        simp only [Option.some.injEq] at hsym_elem
        simp only [←hsym_elem, Term.isLiteral]
        exact value_symbolize?_is_lit hsym_elem'
  | ext =>
    simp only [Value.symbolize?, Option.some.injEq] at hsym
    simp only [←hsym, Term.isLiteral]
termination_by sizeOf v
decreasing_by
  · rename v = Value.set elems => h₁
    rename Value.set elems = Value.set _ => h₂
    rename sym_elem ∈ Set.toList _ => h₃
    rename Set Value => elems'
    simp at h₂
    simp only [←h₂] at h₃
    simp only [h₁, h₃]
    cases elems
    simp [Set.toList, Set.elts] at h₃ ⊢
    have := List.sizeOf_lt_of_mem h₃
    omega
  any_goals
    rename v = Value.record rec => h₁
    rename Value.record rec = Value.record _ => h₂
    rename Value => v'
    rename Map.find? _ sym_elem.fst = some _ => h₃
    simp at h₂
    simp only [←h₂] at h₃ ⊢
    simp only [h₁]
    have := Map.find?_mem_toList h₃
    cases rec
    have := List.sizeOf_lt_of_mem this
    simp [Map.toList, Map.kvs] at this ⊢
    omega

theorem env_symbolize?_wf_vars
  {Γ : TypeEnv} {env : Env} {var : TermVar}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hwf_var : TermVar.WellFormed (SymEnv.ofEnv Γ).entities var) :
  Interpretation.WellFormed.WellFormedVarInterpretation
    (SymEnv.ofEnv Γ).entities
    var
    ((env.symbolize? Γ).vars var)
:= by
  have ⟨⟨hwf_princ, hwf_action, hwf_resource, hwf_context⟩, _⟩ := hwf_env
  have ⟨hwf_Γ, _, _⟩ := hinst
  have ⟨hwf_princ_ty, hcontains_action, hwf_resource_ty, hwf_context_ty⟩ := wf_env_implies_wf_request hwf_Γ
  replace hwf_princ_ty :
    (CedarType.entity Γ.reqty.principal).WellFormed Γ
  := by constructor; exact hwf_princ_ty
  replace hwf_resource_ty :
    (CedarType.entity Γ.reqty.resource).WellFormed Γ
  := by constructor; exact hwf_resource_ty
  have hwf_action_ty :
    (CedarType.entity Γ.reqty.action.ty).WellFormed Γ
  := by
    constructor
    apply Or.inr
    simp only [ActionSchema.IsActionEntityType]
    exists Γ.reqty.action
  have ⟨_, ⟨hinst_princ, hinst_action, hinst_resource, hinst_context⟩, _⟩ := hinst
  replace hinst_princ :
    InstanceOfType Γ (Value.prim (Prim.entityUID env.request.principal)) (CedarType.entity Γ.reqty.principal)
  := by constructor; exact hinst_princ
  replace hinst_resource :
    InstanceOfType Γ (Value.prim (Prim.entityUID env.request.resource)) (CedarType.entity Γ.reqty.resource)
  := by constructor; exact hinst_resource
  replace hinst_action :
    InstanceOfType Γ (Value.prim (Prim.entityUID env.request.action)) (CedarType.entity Γ.reqty.action.ty)
  := by
    constructor
    simp only [InstanceOfEntityType, hinst_action, true_and]
    apply Or.inr
    exact hcontains_action
  simp only [Env.symbolize?, Request.symbolize?]
  constructor
  · constructor
    · split
      · repeat
          rename_i heq
          split at heq
          · apply value_symbolize?_wf hinst _ _ _ heq
            repeat first
            | exact hwf_princ_ty
            | exact hwf_action_ty
            | exact hwf_resource_ty
            | exact hwf_context_ty
            | constructor; exact hwf_princ
            | constructor; exact hwf_action
            | constructor; exact hwf_resource
            | exact hwf_context
            | exact hinst_princ
            | exact hinst_action
            | exact hinst_resource
            | exact hinst_context
        contradiction
      · exact default_lit_wf' hwf_Γ hwf_var
    · split
      · repeat
          rename_i heq
          split at heq
          apply value_symbolize?_is_lit heq
        contradiction
      · exact default_lit_is_lit
  · split
    · rename_i heq
      repeat
        split at heq
        rename_i heq heq_var
        simp only [beq_iff_eq] at heq_var
        simp only [heq_var]
        apply value_symbolize?_well_typed (Γ := Γ) _ _ heq
        repeat first
        | exact hwf_princ_ty
        | exact hwf_action_ty
        | exact hwf_resource_ty
        | exact hwf_context_ty
        | exact hinst_princ
        | exact hinst_action
        | exact hinst_resource
        | exact hinst_context
      contradiction
    · exact default_lit_well_typed

theorem default_udf_wf
  {Γ : TypeEnv} {uuf : UUF}
  (hwf_Γ : Γ.WellFormed)
  (hwf_uuf : UUF.WellFormed (SymEnv.ofEnv Γ).entities uuf) :
  Interpretation.WellFormed.WellFormedUUFInterpretation (SymEnv.ofEnv Γ).entities uuf
    (Decoder.defaultUDF (defaultEidOf Γ) uuf)
:= by
  simp only [Decoder.defaultUDF]
  and_intros
  · simp only
    exact default_lit_wf' hwf_Γ hwf_uuf.2
  · simp only
    exact default_lit_is_lit
  · simp only
    exact default_lit_well_typed
  · simp [Map.empty, Map.WellFormed, Map.toList, Map.kvs, Map.make, List.canonicalize]
  · simp only
    intros _ _ h
    simp [Map.empty, Map.toList, Map.kvs] at h
  · simp only
  · simp only

theorem env_symbolize?_attrs_wf
  {Γ : TypeEnv} {env : Env}
  {ety : EntityType} {entry : EntitySchemaEntry}
  {uuf : UUF} {udf : UDF}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hfind_entry : Map.find? Γ.ets ety = some entry)
  (hudf : env.entities.symbolizeAttrs? Γ ety entry uuf = some udf) :
  Interpretation.WellFormed.WellFormedUUFInterpretation
    (SymEnv.ofEnv Γ).entities uuf udf
:= by
  have ⟨_, ⟨hwf_entities, _⟩⟩:= hwf_env
  have ⟨hwf_Γ, _, hwf_sch⟩ := hinst
  simp only [
    Entities.symbolizeAttrs?, beq_iff_eq,
    Option.ite_none_right_eq_some,
    Option.some.injEq,
  ] at hudf
  simp only [←hudf.2]
  simp only [Entities.symbolizeAttrs?.udf]
  have hfind_attrs : Γ.ets.attrs? ety = .some entry.attrs := by
    simp [EntitySchema.attrs?, hfind_entry]
  and_intros
  · simp only
    apply default_lit_wf' hwf_Γ
    apply ofType_wf hwf_Γ
    exact wf_env_implies_wf_attrs hwf_Γ hfind_attrs
  · simp only
    exact default_lit_is_lit
  · simp only
    exact default_lit_well_typed
  · simp only
    exact Map.make_wf _
  -- Well-formed `UDF.table`
  · simp only
    intros tᵢ tₒ hmem
    have hmem := Map.make_mem_list_mem hmem
    have ⟨⟨uid, data⟩, hmem_uid_data, hio⟩ := List.mem_filterMap.mp hmem
    have hfind_uid_data := (Map.in_list_iff_find?_some hwf_entities.1).mp hmem_uid_data
    have ⟨hwf_attrs, _⟩ := hwf_entities.2 uid data hfind_uid_data
    simp only [bind, Option.bind, Option.ite_none_right_eq_some] at hio
    have ⟨heq_ety, hio⟩ := hio
    split at hio
    contradiction
    rename_i sym_attrs hsym_attrs
    simp at hio
    simp only [←hio]
    have hwt_attrs : InstanceOfType Γ (Value.record data.attrs) (CedarType.record entry.attrs) := by
      have := hwf_sch.1 uid data hfind_uid_data
      simp only [←heq_ety] at hfind_entry
      cases this with
      | inl this =>
        have ⟨_, hfind, _, h, _⟩ := this
        simp only [hfind_entry, Option.some.injEq] at hfind
        simp only [←hfind] at h
        exact h
      | inr this =>
        have ⟨_, _, ⟨_, h, _⟩⟩ := this
        have := wf_env_disjoint_ets_acts hwf_Γ hfind_entry h
        contradiction
    have hwf_attrs_ty : CedarType.WellFormed Γ (CedarType.record entry.attrs)
    := wf_env_implies_wf_attrs hwf_Γ hfind_attrs
    and_intros
    · constructor
      constructor
      apply env_valid_uid_implies_sym_env_valid_uid hinst
      exact Map.in_list_implies_contains hmem_uid_data
    · simp only [←hio.1, Term.isLiteral]
    · simp only [Term.typeOf, TermPrim.typeOf, TermType.ofType, heq_ety]
    · apply value_symbolize?_wf hinst hwf_attrs_ty hwf_attrs hwt_attrs hsym_attrs
    · apply value_symbolize?_is_lit hsym_attrs
    · apply value_symbolize?_well_typed hwf_attrs_ty hwt_attrs hsym_attrs
  · simp only [hudf.1]
  · simp only [hudf.1]

theorem env_symbolize?_tags_wf
  {Γ : TypeEnv} {env : Env}
  {ety : EntityType} {entry : EntitySchemaEntry}
  {uuf : UUF} {udf : UDF}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hfind_entry : Map.find? Γ.ets ety = some entry)
  (hudf : env.entities.symbolizeTags? Γ ety entry uuf = some udf) :
  Interpretation.WellFormed.WellFormedUUFInterpretation
    (SymEnv.ofEnv Γ).entities uuf udf
:= by
  have ⟨_, ⟨hwf_entities, _⟩⟩:= hwf_env
  have ⟨hwf_Γ, _, hwf_sch⟩ := hinst
  simp only [Entities.symbolizeTags?, beq_iff_eq, Option.bind_eq_bind] at hudf
  cases htagTy : entry.tags? with
  | none => simp [htagTy] at hudf
  | some tagTy =>
    have htagTy' : Γ.ets.tags? ety = .some (.some tagTy) := by
      simp only [EntitySchema.tags?, Option.map_eq_some_iff]
      exists entry
    simp only [htagTy, Option.bind_some] at hudf
    split at hudf
    -- Tag keys
    · rename_i hudf_tag_keys
      simp only [Option.some.injEq] at hudf
      simp only [
        ←hudf,
        Entities.symbolizeTags?.keysUDF,
      ]
      and_intros
      · simp only
        apply default_lit_wf' hwf_Γ
        apply ofType_wf hwf_Γ
        repeat constructor
      · simp only
        exact default_lit_is_lit
      · simp only
        exact default_lit_well_typed
      · simp only
        exact Map.make_wf _
      -- Well-formed `UDF.table`
      · simp only
        intros tᵢ tₒ hmem
        have hmem := Map.make_mem_list_mem hmem
        have ⟨⟨uid, data⟩, hmem_uid_data, hio⟩ := List.mem_filterMap.mp hmem
        have hfind_uid_data := (Map.in_list_iff_find?_some hwf_entities.1).mp hmem_uid_data
        have ⟨hwf_attrs, _⟩ := hwf_entities.2 uid data hfind_uid_data
        simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hio
        have ⟨heq_ety, hio⟩ := hio
        simp only [← hio]
        and_intros
        · constructor
          constructor
          apply env_valid_uid_implies_sym_env_valid_uid hinst
          exact Map.in_list_implies_contains hmem_uid_data
        · simp only [Term.isLiteral]
        · simp only [Term.typeOf, TermPrim.typeOf, TermType.ofType, heq_ety]
        · constructor
          · intros t hmem_t
            replace hmem_t := (Set.make_mem _ _).mpr hmem_t
            have ⟨_, _, h⟩ := List.mem_map.mp hmem_t
            simp only [←h]
            constructor
            constructor
          · intros t hmem_t
            replace hmem_t := (Set.make_mem _ _).mpr hmem_t
            have ⟨_, _, h⟩ := List.mem_map.mp hmem_t
            simp only [←h]
            simp only [Term.typeOf, TermPrim.typeOf]
          · constructor
          · exact Set.make_wf _
        · unfold Term.isLiteral
          apply List.all_eq_true.mpr
          intros x hmem_x
          simp only
          replace hmem_x := x.property
          have hmem_x := (Set.make_mem _ _).mpr hmem_x
          have ⟨_, _, h⟩ := List.mem_map.mp hmem_x
          simp only [←h, Term.isLiteral]
        · simp only [Term.typeOf, TermType.ofType]
      · simp only [hudf_tag_keys]
      · simp only [hudf_tag_keys]
    -- Tag values
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hudf
      have hudf_tag_vals := hudf.1
      replace hudf := hudf.2
      simp only [
        ←hudf,
        Entities.symbolizeTags?.valsUDF,
      ]
      and_intros
      · simp only
        apply default_lit_wf' hwf_Γ
        apply ofType_wf hwf_Γ
        apply wf_env_implies_wf_tag_type hwf_Γ htagTy'
      · simp only
        exact default_lit_is_lit
      · simp only
        exact default_lit_well_typed
      · simp only
        exact Map.make_wf _
      · simp only
        intros tᵢ tₒ hmem
        have hmem := Map.make_mem_list_mem hmem
        have ⟨l, hmem_l, hmem⟩ := List.mem_flatten.mp hmem
        have ⟨⟨uid, data⟩, hmem_uid_data, hl⟩ := List.mem_filterMap.mp hmem_l
        simp only [Option.bind_eq_bind, Option.ite_none_right_eq_some] at hl
        have ⟨heq_ety, hl⟩ := hl
        have ⟨⟨tag, val⟩, hmem_tag_val, htag_val⟩ :=
          List.mapM_some_implies_all_from_some hl (tᵢ, tₒ) hmem
        simp only [bind, Option.bind] at htag_val
        split at htag_val
        contradiction
        rename_i sym_val hsym_val
        simp only [Option.some.injEq, Prod.mk.injEq] at htag_val
        simp only [←htag_val]
        have hwf_tagTy : tagTy.WellFormed Γ
        := wf_env_implies_wf_tag_type hwf_Γ htagTy'
        have hfind_uid_data := (Map.in_list_iff_find?_some hwf_entities.1).mp hmem_uid_data
        have ⟨_, _, _, hwf_tags_map, hwf_tags⟩ := hwf_entities.2 uid data hfind_uid_data
        have hwf_val : val.WellFormed env.entities := by
          have := (Map.in_list_iff_find?_some hwf_tags_map).mp hmem_tag_val
          exact hwf_tags tag val this
        have hwt_val : InstanceOfType Γ val tagTy := by
          have := hwf_sch.1 uid data hfind_uid_data
          cases this with
          | inl this =>
            have ⟨entry', hfind_entry', _, _, _, h⟩ := this
            simp only [←heq_ety] at hfind_entry
            simp only [hfind_entry, Option.some.injEq] at hfind_entry'
            simp only [InstanceOfEntityTags, ←hfind_entry', htagTy] at h
            exact h val (Map.in_list_in_values hmem_tag_val)
          | inr this =>
            have ⟨_, htag_emp, _⟩ := this
            simp [htag_emp, Map.empty, Map.toList, Map.kvs] at hmem_tag_val
        and_intros
        · constructor
          · intros a t hmem_a_t
            simp only [
              Map.toList, Map.kvs,
              List.mem_cons, Prod.mk.injEq,
              List.not_mem_nil, or_false,
            ] at hmem_a_t
            cases hmem_a_t with
            | inl hmem_a_t =>
              simp only [hmem_a_t]
              constructor
              constructor
              apply env_valid_uid_implies_sym_env_valid_uid hinst
              exact Map.in_list_implies_contains hmem_uid_data
            | inr hmem_a_t =>
              simp only [hmem_a_t]
              constructor
              constructor
          · simp [
              Map.WellFormed, Map.make,
              List.canonicalize, Map.toList,
              Map.kvs, List.insertCanonical,
            ]
        · simp [Term.isLiteral, List.all, List.attach₃, List.pmap]
        · simp only [
            Term.typeOf, TermPrim.typeOf,
            TermType.ofType, heq_ety,
            TermType.tagFor, EntityTag.mk,
            List.attach₃, List.map, List.pmap,
          ]
        · apply value_symbolize?_wf hinst hwf_tagTy hwf_val hwt_val hsym_val
        · apply value_symbolize?_is_lit hsym_val
        · apply value_symbolize?_well_typed hwf_tagTy hwt_val hsym_val
      · simp only [hudf_tag_vals]
      · simp only [hudf_tag_vals]

theorem env_symbolize?_ancs_wf
  {Γ : TypeEnv} {env : Env}
  {ety : EntityType} {entry : EntitySchemaEntry}
  {uuf : UUF} {udf : UDF}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hfind_entry : Map.find? Γ.ets ety = some entry)
  (hudf : env.entities.symbolizeAncs? Γ ety entry uuf = some udf) :
  Interpretation.WellFormed.WellFormedUUFInterpretation
    (SymEnv.ofEnv Γ).entities uuf udf
:= by
  have ⟨_, ⟨hwf_entities, _⟩⟩:= hwf_env
  have ⟨hwf_Γ, _, hwf_sch⟩ := hinst
  simp only [Entities.symbolizeAncs?, beq_iff_eq, Option.bind_eq_bind] at hudf
  have ⟨_, anc, _, heq, hudf, _⟩ := List.findSome?_eq_some_iff.mp hudf
  have hmem_ancs : anc ∈ entry.ancestors := by
    apply (Set.in_list_iff_in_set _ _).mp
    simp only [Set.toList] at heq
    simp [heq]
  simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hudf
  simp only [←hudf, Entities.symbolizeAncs?.udf]
  and_intros
  · simp only
    apply default_lit_wf' hwf_Γ
    apply ofType_wf hwf_Γ
    constructor
    constructor
    exact wf_env_implies_wf_ancestor hwf_Γ hfind_entry hmem_ancs
  · simp only
    exact default_lit_is_lit
  · simp only
    exact default_lit_well_typed
  · simp only
    exact Map.make_wf _
  · simp only
    intros tᵢ tₒ hmem
    have hmem := Map.make_mem_list_mem hmem
    have ⟨⟨uid, data⟩, hmem_uid_data, hio⟩ := List.mem_filterMap.mp hmem
    have hfind_uid_data := (Map.in_list_iff_find?_some hwf_entities.1).mp hmem_uid_data
    have ⟨_, _, hwf_ancs, _⟩ := hwf_entities.2 uid data hfind_uid_data
    simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hio
    have ⟨heq_ety, hio⟩ := hio
    simp only [← hio]
    and_intros
    · constructor
      constructor
      apply env_valid_uid_implies_sym_env_valid_uid hinst
      exact Map.in_list_implies_contains hmem_uid_data
    · simp only [Term.isLiteral]
    · simp only [Term.typeOf, TermPrim.typeOf, TermType.ofType, heq_ety]
    · constructor
      · intros t hmem_t
        replace hmem_t := (Set.make_mem _ _).mpr hmem_t
        have ⟨anc, hmem_anc, h⟩ := List.mem_filterMap.mp hmem_t
        simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
        simp only [←h]
        constructor
        constructor
        apply env_valid_uid_implies_sym_env_valid_uid hinst
        exact hwf_ancs anc hmem_anc
      · intros t hmem_t
        replace hmem_t := (Set.make_mem _ _).mpr hmem_t
        have ⟨anc, hmem_anc, h⟩ := List.mem_filterMap.mp hmem_t
        simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
        simp only [←h, Term.typeOf, TermPrim.typeOf]
      · constructor
        apply ofEnv_wf_entity hwf_Γ
        apply wf_env_implies_wf_ancestor hwf_Γ hfind_entry hmem_ancs
      · exact Set.make_wf _
    · unfold Term.isLiteral
      apply List.all_eq_true.mpr
      intros x hmem_x
      simp only
      replace hmem_x := x.property
      have hmem_x := (Set.make_mem _ _).mpr hmem_x
      have ⟨anc, hmem_anc, h⟩ := List.mem_filterMap.mp hmem_x
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
      simp only [←h, Term.isLiteral]
    · simp only [Term.typeOf, TermType.ofType]
  · simp only [hudf]
  · simp only [hudf]

theorem env_symbolize?_wf_funs
  {Γ : TypeEnv} {env : Env} {uuf : UUF}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hwf_uuf : UUF.WellFormed (SymEnv.ofEnv Γ).entities uuf) :
  Interpretation.WellFormed.WellFormedUUFInterpretation
    (SymEnv.ofEnv Γ).entities
    uuf
    ((env.symbolize? Γ).funs uuf)
:= by
  have ⟨hwf_Γ, _, _⟩ := hinst
  simp only [Env.symbolize?, Entities.symbolize?]
  split
  · rename_i udf hfind_udf
    have ⟨_, ⟨ety, entry⟩, _, heq, hudf, _⟩ := List.findSome?_eq_some_iff.mp hfind_udf
    have hmem_entry : (ety, entry) ∈ Γ.ets.toList := by simp [heq]
    have hfind_entry := (Map.in_list_iff_find?_some (wf_env_implies_wf_ets_map hwf_Γ)).mp hmem_entry
    simp only [Option.orElse_eq_orElse, Option.orElse_eq_or, Option.or_eq_some_iff] at hudf
    cases hudf with
    | inl hudf_attrs => exact env_symbolize?_attrs_wf hwf_env hinst hfind_entry hudf_attrs
    | inr hudf =>
      cases hudf.2 with
      | inl hudf_tags => exact env_symbolize?_tags_wf hwf_env hinst hfind_entry hudf_tags
      | inr hudf_ancs =>
        replace hudf_ancs := hudf_ancs.2
        exact env_symbolize?_ancs_wf hwf_env hinst hfind_entry hudf_ancs
  · exact default_udf_wf hwf_Γ hwf_uuf

theorem env_symbolize?_wf
  {Γ : TypeEnv} {env : Env}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  (env.symbolize? Γ).WellFormed (SymEnv.ofEnv Γ).entities
:= by
  have ⟨hwf_Γ, _, _⟩ := hinst
  and_intros
  · intros var hwf_var
    exact env_symbolize?_wf_vars hwf_env hinst hwf_var
  · intros uuf hwf_uuf
    exact env_symbolize?_wf_funs hwf_env hinst hwf_uuf
  · intros t ht
    simp only [Env.symbolize?, defaultLit']
    constructor
    · constructor
      · exact default_lit_wf' hwf_Γ (wfp_term_implies_wf_ty ht)
      · exact default_lit_is_lit
    · exact default_lit_well_typed

theorem ofEnv_soundness
  {Γ : TypeEnv} {env : Env}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env ∈ᵢ SymEnv.ofEnv Γ
:= by
  have ⟨hwf, hinst_req, hinst_sch⟩ := hinst
  exists env.symbolize? Γ
  constructor
  · exact env_symbolize?_wf hwf_env hinst
  . exact env_symbolize?_same hwf_env hinst

end Cedar.Thm
