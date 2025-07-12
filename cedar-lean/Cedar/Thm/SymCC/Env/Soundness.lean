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

/--
`symbolize?` is the right inverse of `value?`.
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
    unfold Value.symbolize?
    simp only [Option.bind_eq_bind]
    have ⟨sym_attrs, hsym_attrs, hsym_attrs_forall₂⟩ :
      ∃ sym_attrs,
        List.mapM (Value.symbolize?.symbolizeAttr? (Map.mk rec_map) rty) rec_map
        = .some sym_attrs ∧
        List.Forall₂ (λ x y =>
          x.fst = y.fst ∧
          (∃ attr_ty z,
            rty.find? x.fst = .some attr_ty ∧
            x.snd.symbolize? attr_ty.getType = .some z ∧
            y.snd = Term.some z ∧
            Term.value?.attrValue? y.fst y.snd = .some (x.fst, Option.some x.snd))
        ) rec_map sym_attrs
    := by
      have ⟨sym_attrs, hsym_attrs⟩ :
        ∃ sym_attrs,
          List.mapM (Value.symbolize?.symbolizeAttr? (Map.mk rec_map) rty) rec_map
          = .some sym_attrs
      := by
        apply List.all_some_implies_mapM_some
        intros attr_val hmem_attr_val
        simp only [Value.symbolize?.symbolizeAttr?]
        have hfind_attr := (Map.in_list_iff_find?_some hwf_rec_map).mp hmem_attr_val
        have := hrec_mem_implies_rty_mem attr_val.1
        simp only [
          Map.contains, hfind_attr,
          Option.isSome_some, forall_const,
          Option.isSome,
        ] at this
        split at this
        rotate_left; contradiction
        rename_i qty hfind_attr_qty
        simp only [
          hfind_attr_qty, Option.bind_eq_bind,
          Option.bind_some_fun, Prod.exists,
        ]
        have := hwf_rty attr_val.1 qty hfind_attr_qty
        have hwf_qty := qty_wf_implies_type_of_wf this
        have hwf_val := hwf_rec attr_val.1 attr_val.2 hfind_attr
        have hwt_val := hwt_rec attr_val.1 attr_val.2 qty hfind_attr hfind_attr_qty
        have ⟨sym_attr_val, hsym_attr_val, hval_sym_attr_val⟩ := value?_symbolize?_id hwf_Γ hwf_qty hwf_val hwt_val
        exists attr_val.fst, (.some sym_attr_val)
        simp [hsym_attr_val]
      exists sym_attrs
      simp only [hsym_attrs, true_and]
      apply List.mapM_implies_forall₂_option _ hsym_attrs
      intros attr_val attr_sym_val hmem_attr_val hsym_attr_val
      simp only [
        Value.symbolize?.symbolizeAttr?, Option.bind_eq_bind,
        bind, Option.bind,
      ] at hsym_attr_val
      split at hsym_attr_val
      contradiction
      rename_i qty hfind_attr_qty
      simp only at hsym_attr_val
      split at hsym_attr_val
      contradiction
      rename_i sym_attr_val' hsym_attr_val'
      simp only [Option.some.injEq] at hsym_attr_val
      simp only [← hsym_attr_val, true_and]
      exists qty, sym_attr_val'
      simp only [
        hfind_attr_qty, hsym_attr_val',
        Option.some.injEq, true_and,
        Term.value?.attrValue?,
      ]
      -- TODO: there's a similar chunk above, maybe merge somehow?
      have hfind_attr := (Map.in_list_iff_find?_some hwf_rec_map).mp hmem_attr_val
      have := hwf_rty attr_val.1 qty hfind_attr_qty
      have hwf_qty := qty_wf_implies_type_of_wf this
      have hwf_val := hwf_rec attr_val.1 attr_val.2 hfind_attr
      have hwt_val := hwt_rec attr_val.1 attr_val.2 qty hfind_attr hfind_attr_qty
      have ⟨sym_attr_val, hsym_attr_val, hval_sym_attr_val⟩ := value?_symbolize?_id hwf_Γ hwf_qty hwf_val hwt_val
      have heq : sym_attr_val' = sym_attr_val := by
        simp only [hsym_attr_val', Option.some.injEq] at hsym_attr_val
        exact hsym_attr_val
      simp [heq, hval_sym_attr_val, Option.bind_some_fun]
    have ⟨val_sym_attrs, hval_sym_attrs, hval_sym_attrs_forall₂⟩ :
      ∃ val_sym_attrs,
        List.mapM (fun x => Term.value?.attrValue? x.fst x.snd) sym_attrs
        = .some val_sym_attrs ∧
        List.Forall₂ (λ x y =>
          x.fst = y.fst ∧
          x.snd = .some y.snd) val_sym_attrs rec_map
    := by
      have ⟨val_sym_attrs, hval_sym_attrs⟩ :
        ∃ val_sym_attrs,
          List.mapM (fun x => Term.value?.attrValue? x.fst x.snd) sym_attrs
          = .some val_sym_attrs
      := by
        apply List.all_some_implies_mapM_some
        intros attr_term hmem_attr_term
        have ⟨x, _, _, ⟨attr, z, _, _, _, h⟩⟩ := List.forall₂_implies_all_right hsym_attrs_forall₂ attr_term hmem_attr_term
        simp [h]
      exists val_sym_attrs
      simp only [hval_sym_attrs, true_and]
      apply List.forall₂_swap
      apply List.forall₂_compose_mapM_right hsym_attrs_forall₂ hval_sym_attrs
      intros a b hab
      have ⟨h₁, ⟨attr, z, h₂, h₃, h₄, h₅⟩⟩ := hab
      simp [h₅]
    simp only [
      Map.toList, Map.kvs,
      List.mapM₂_eq_mapM _ _, hsym_attrs,
      Option.bind_some,
      Option.some.injEq,
      exists_eq_left',
      Term.value?,
    ]
    simp only [
      Map.toList, Map.kvs,
      List.mapM₂_eq_mapM (λ x => Term.value?.attrValue? x.fst x.snd) _,
      hval_sym_attrs,
      Option.bind_some_fun,
      Option.some.injEq,
      Value.record.injEq,
      Map.mk.injEq,
    ]
    apply List.forall₂_eq_implies_filterMap hval_sym_attrs_forall₂
    intros a b h
    have ⟨ha, hb⟩ := h
    simp [Option.map, hb, ha]
termination_by sizeOf v
decreasing_by
  any_goals
    rename_i s _ _ _ _ _
    simp [*]
    have h := List.sizeOf_lt_of_mem hmem_elem
    cases s
    simp only [Set.toList, Set.elts] at h
    rename_i h'
    simp only [←h']
    calc
      sizeOf elem < sizeOf elems.1 := by assumption
      _ < 1 + sizeOf elems := by
        cases elems
        simp
        omega
  any_goals
    simp [*]
    have h := List.sizeOf_lt_of_mem hmem_elem
    simp only [Set.toList, Set.elts] at h
    rename_i h' _ _
    simp only [←h']
    calc
      sizeOf elem < sizeOf elems.1 := by assumption
      _ < 1 + sizeOf elems := by
        cases elems
        simp
        omega
  any_goals
    have : v = Value.record rec := by assumption
    simp only [this]
    have : rec = Map.mk rec_map := by assumption
    simp only [this]
    simp_wf
    have h := List.sizeOf_lt_of_mem hmem_attr_val
    calc
      sizeOf attr_val.snd < sizeOf attr_val := by
        cases attr_val
        simp
        omega
      _ < 1 + (1 + sizeOf rec_map) := by
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
    simp only [Term.interpret]
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

theorem env_symbolize?_same_entities
  {Γ : TypeEnv} {env : Env}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env.entities ∼ ((SymEnv.ofEnv Γ).interpret (env.symbolize? Γ)).entities
:= by
  sorry

theorem env_symbolize?_same
  {Γ : TypeEnv} {env : Env}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env ∼ (SymEnv.ofEnv Γ).interpret (env.symbolize? Γ)
:= by
  constructor
  · exact env_symbolize?_same_request hwf_env hinst
  · exact env_symbolize?_same_entities hwf_env hinst

theorem ofEnv_soundness
  {Γ : TypeEnv} {env : Env}
  (hwf_env : env.StronglyWellFormed)
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env ∈ᵢ SymEnv.ofEnv Γ
:= by
  have ⟨hwf, hinst_req, hinst_sch⟩ := hinst
  exists env.symbolize? Γ
  constructor
  · sorry
  . exact env_symbolize?_same hwf_env hinst

end Cedar.Thm
