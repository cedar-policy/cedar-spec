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
import Cedar.Thm.SymCC.Term.ofType
import Cedar.SymCC.Concretizer
import Cedar.SymCC.Symbolizer

/-! Theorems that `Value.symbolizer?` produces well-formed, well-typed literals. -/

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
    simp only [ofRecordType_as_map]
    have :
      List.Forall₂
        (λ rty_entry sym_attr =>
          rty_entry ∈ rty.toList ∧
          .some sym_attr = Value.symbolize?.symbolizeAttr? rec rty_entry.1 rty_entry.2)
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
      apply List.mapM_preserves_SortedBy hsorted_rty_map hsym_attrs
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
        Value.symbolize?.symbolizeAttr? (Map.mk rec_map) attr.fst attr.snd = some sym_attr ∧
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
      (hattr : Value.symbolize?.symbolizeAttr? (Map.mk rec_map) attr.fst attr.snd = some sym_attr)
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
        List.mapM (λ (a, qty) => Value.symbolize?.symbolizeAttr? (Map.mk rec_map) a qty) rty_map
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
      apply List.mapM_preserves_SortedBy hsorted_rty_map hsym_attrs
      unfold Value.symbolize?.symbolizeAttr?
      intros a b
      simp only [Option.bind_eq_bind]
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
      apply List.mapM_preserves_SortedBy hsorted_sym_attrs hval_sym_attrs
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

end Cedar.Thm
