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

theorem filterMap_mapM_combine
  {l₁ : List α} {l₂ : List β}
  {f : α → Option β}
  {g : β → Option γ}
  (h : l₁.mapM f = .some l₂) :
  -- (hh : ∀ x ∈ l₁, ∃ y, (f x).bind g = .some y) :
  l₂.filterMap g = l₁.filterMap (λ x => (f x).bind g)
:= by
  sorry

theorem filterMap_partial_inverse
  {l : List α}
  {f : α → Option α}
  (h : ∀ x ∈ l, f x = .some x) :
  l.filterMap f = l
:= sorry

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
    have ⟨sym_elems, hsym_elems, hval_sym_elems_id⟩ :
      ∃ sym_elems,
        elems.toList.mapM (λ x => x.symbolize? elem_ty)
        = .some sym_elems ∧
        ∀ sym_elem ∈ sym_elems,
          ∃ elem ∈ elems, sym_elem.value? = .some elem
    := by
      have (elem : Value) (hmem_elem : elem ∈ elems.toList) :
        ∃ sym_elem,
          elem.symbolize? elem_ty = .some sym_elem
      := by
        have ⟨sym_elem, hsym_elem, _⟩ := value?_symbolize?_id hwf_Γ hwf_elem_ty (hwf_elem elem hmem_elem) (hwt_elem elem hmem_elem)
        exists sym_elem
      have ⟨sym_elems, hsym_elems⟩ := List.all_some_implies_mapM_some this
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
    have ⟨val_sym_elems, hval_sym_elems, hval_sym_elem_inv⟩ :
      ∃ val_sym_elems,
        (Set.make sym_elems).1.mapM Term.value?
        = .some val_sym_elems ∧
        ∀ val_sym_elem ∈ val_sym_elems,
          ∃ sym_elem ∈ sym_elems, val_sym_elem = sym_elem.value?
    := by
      have (sym_elem : Term) (hmem_sym_elem : sym_elem ∈ (Set.make sym_elems)) :
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
      have ⟨val_sym_elems, hval_sym_elems⟩ := List.all_some_implies_mapM_some this
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
    unfold Value.symbolize?
    simp only [Option.bind_eq_bind]
    simp only [List.mapM₂_eq_mapM _ _]

    have :
      ∃ sym_attrs,
        List.mapM (Value.symbolize?.symbolizeAttr? rec rty) rec.toList
        = .some sym_attrs
    := by
      sorry

    -- generalize (Value.symbolize?.symbolizeAttr? rec rty) = xxx
    -- have f (x : { x: Attr × Value // sizeOf x.snd < 1 + sizeOf rec.toList }) :=
    --   (Map.find? rty x.val.fst).bind fun __do_lift =>
    --     match __do_lift with
    --     | Qualified.optional ty =>
    --       (x.val.snd.symbolize? ty).bind fun __do_lift => Option.some (x.val.fst, Term.some __do_lift)
    --     | Qualified.required ty =>
    --       (x.val.snd.symbolize? ty).bind fun __do_lift => Option.some (x.val.fst, __do_lift)

    -- rw [h]
    sorry

-- /--
-- `Value.symbolize?` is a partial inverse of `Term.value?`.
-- -/
-- theorem value?_symbolize?_id
--   {Γ : TypeEnv} {entities : Entities} {v : Value} {t : Term} {ty : CedarType}
--   (hwf : Γ.WellFormed)
--   (hwf_ty : ty.WellFormed Γ)
--   (hwf_v : v.WellFormed entities)
--   (hwt : InstanceOfType Γ v ty)
--   (hok : v.symbolize? ty = .some t) :
--   t.value? = .some v
-- := by
--   cases hwt with
--   | instance_of_bool
--   | instance_of_string
--   | instance_of_entity
--   | instance_of_ext
--   | instance_of_int =>
--     simp only [Value.symbolize?, Prim.symbolize, Option.some.injEq] at hok
--     simp [←hok, Term.value?, TermPrim.value?, BitVec.int64?]
--   | instance_of_set s sty hwt =>
--     cases hwf_ty with | set_wf hwf_sty =>
--     cases hwf_v with | set_wf hwf_v hwf_s =>
--     simp only [
--       Value.symbolize?, Option.bind_eq_bind,
--       bind, Option.bind,
--     ] at hok
--     split at hok
--     contradiction
--     rename_i ts hts
--     simp only [List.mapM₁_eq_mapM (λ v => v.symbolize? sty) s.toList] at hts
--     simp only [Option.some.injEq] at hok
--     simp only [←hok]
--     -- `symbolize?` on elements should succeed
--     have ⟨vs, hvs⟩ :
--       ∃ vs,
--         (Set.make ts).1.mapM (λ t => t.value?) = .some vs
--     := by
--       apply List.all_some_implies_mapM_some
--       intros t hmem_t
--       have := (Set.make_mem _ _).mpr hmem_t
--       have hts := List.mapM_some_implies_all_from_some hts
--       have ⟨x, hmem_x, hsym_x⟩ := hts t this
--       have hwt_x := hwt x hmem_x
--       have hsame_y := value?_symbolize?_id hwf hwf_sty (hwf_v x hmem_x) hwt_x hsym_x
--       exists x
--     unfold Term.value?
--     simp only [
--       List.mapM₁_eq_mapM ?_ (Set.make ts).1,
--       hvs,
--       Option.bind_some_fun, Option.some.injEq,
--       Value.set.injEq,
--     ]
--     -- Prove that the sets of values before and after `value? ∘ symbolize?` are equal
--     apply (Set.subset_iff_eq (Set.make_wf _) hwf_s).mp
--     constructor
--     · apply Set.subset_def.mpr
--       intros new_v hmem_new_v
--       have hmem_new_v := (Set.make_mem _ _).mpr hmem_new_v
--       have ⟨x, hmem_x, hx_value?⟩ := List.mapM_some_implies_all_from_some hvs new_v hmem_new_v
--       have hmem_x := (Set.make_mem _ _).mpr hmem_x
--       have ⟨old_v, hmem_old_v, hold_v_symbolize?⟩ := List.mapM_some_implies_all_from_some hts x hmem_x
--       have := value?_symbolize?_id hwf hwf_sty (hwf_v old_v hmem_old_v) (hwt old_v hmem_old_v) hold_v_symbolize?
--       simp only [this, Option.some.injEq] at hx_value?
--       simp only [hx_value?] at hmem_old_v
--       exact hmem_old_v
--     · apply Set.subset_def.mpr
--       intros old_v hmem_old_v
--       have ⟨t, hmem_t, hv_symbolize?⟩ := List.mapM_some_implies_all_some hts old_v hmem_old_v
--       have ⟨new_v, hmem_new_v, hnew_v_symbolize?⟩ := List.mapM_some_implies_all_some hvs t ((Set.make_mem _ _).mp hmem_t)
--       have := value?_symbolize?_id hwf hwf_sty (hwf_v old_v hmem_old_v) (hwt old_v hmem_old_v) hv_symbolize?
--       simp only [this, Option.some.injEq] at hnew_v_symbolize?
--       simp only [←hnew_v_symbolize?] at hmem_new_v
--       exact (Set.make_mem _ _).mp hmem_new_v
--   | instance_of_record rec rty h₁ h₂ h₃ =>
--     cases hwf_ty with | record_wf hwf_rty_map hwf_rty =>
--     cases hwf_v with | record_wf hwf_v hwf_rec_map =>
--     simp only [
--       Value.symbolize?,
--       Option.bind_eq_bind,
--       bind, Option.bind,
--     ] at hok
--     -- have := List.mapM₂_eq_mapM (λ x =>
--     --     (Map.find? rty x.fst).bind fun __do_lift =>
--     --       match __do_lift with
--     --       | Qualified.optional ty => (x.snd.symbolize? ty).bind fun __do_lift => some (x.fst, __do_lift.some)
--     --       | Qualified.required ty => (x.snd.symbolize? ty).bind fun __do_lift => some (x.fst, __do_lift))
--     --     rec.toList
--     -- simp [Subtype.val] at this
--     -- -- have := Eq.trans (Eq.symm hok) this
--     -- have := List.mapM₂_eq_mapM (λ x => do
--     --       match ← Map.find? rty x.fst with
--     --       | .optional ty => .some (x.fst, Term.some (← x.snd.symbolize? ty))
--     --       | .required ty => .some (x.fst, ← x.snd.symbolize? ty))
--     --     rec.toList
--     -- simp [this] at hok
--     -- have [SizeOf Attr] [SizeOf Term] [i : SizeOf Value] :
--     --   (rec.toList.mapM₂ fun (x : {x : Attr × Value // i.sizeOf x.snd < 1 + sizeOf rec.toList}) =>
--     --     (Map.find? rty x.1.fst).bind fun __do_lift =>
--     --       match __do_lift with
--     --       | Qualified.optional ty => (x.1.snd.symbolize? ty).bind fun __do_lift => some (x.1.fst, __do_lift.some)
--     --       | Qualified.required ty => (x.1.snd.symbolize? ty).bind fun __do_lift => some (x.1.fst, __do_lift)) =
--     --   (rec.toList.mapM fun x =>
--     --     (Map.find? rty x.fst).bind fun __do_lift =>
--     --       match __do_lift with
--     --       | Qualified.optional ty => (x.snd.symbolize? ty).bind fun __do_lift => some (x.fst, __do_lift.some)
--     --       | Qualified.required ty => (x.snd.symbolize? ty).bind fun __do_lift => some (x.fst, __do_lift))
--     -- :=
--     --   List.mapM₂_eq_mapM
--     --     (fun x =>
--     --     (Map.find? rty x.fst).bind fun __do_lift =>
--     --       match __do_lift with
--     --       | Qualified.optional ty => (x.snd.symbolize? ty).bind fun __do_lift => some (x.fst, __do_lift.some)
--     --       | Qualified.required ty => (x.snd.symbolize? ty).bind fun __do_lift => some (x.fst, __do_lift))
--     --     rec.toList
--     -- simp only [this] at hok
--     split at hok
--     contradiction
--     simp only [Option.some.injEq] at hok
--     rename_i ts hts
--     simp only [←hok]
--     have ⟨vs, hvs⟩ :
--       ∃ vs,
--         (Map.mk ts).1.mapM (λ (a, t) => Term.value?.attrValue? a t)
--         = .some vs
--     := by
--       apply List.all_some_implies_mapM_some
--       intros p hmem_p
--       simp only
--       unfold Term.value?.attrValue?
--       have hts := List.mapM_some_implies_all_from_some hts
--       have ⟨x, hmem_x, hsym_x⟩ := hts p hmem_p
--       simp only [List.attach₂] at hmem_x
--       have ⟨x', hmem_x', hxx'⟩ := List.mem_pmap.mp hmem_x
--       split at hsym_x
--       contradiction
--       rename_i qty hfind_qty
--       simp only at hsym_x
--       -- Type of sym_x is well-formed
--       have hxx' : x.1 = x' := by simp [←hxx']
--       simp only [hxx'] at hfind_qty
--       have hwf_qty := hwf_rty x'.fst qty hfind_qty
--       have hrec_find := (Map.in_list_iff_find?_some hwf_rec_map).mp hmem_x'
--       have hwf_x' := hwf_v x'.fst x'.snd hrec_find
--       have hwt_x' := h₂ x'.fst x'.snd qty hrec_find hfind_qty
--       cases hqty : qty with
--       | optional ty =>
--         simp only [hqty] at hsym_x
--         split at hsym_x
--         contradiction
--         rename_i sym_x hsym_x_ok
--         simp only [Option.some.injEq] at hsym_x
--         simp [←hsym_x]
--         have ⟨v, hv⟩ : ∃ v, sym_x.value? = .some v := by
--           simp only [hqty] at hwf_qty
--           cases hwf_qty with | optional_wf hwf_ty =>
--           simp only [hxx'] at hsym_x_ok
--           simp only [hqty] at hwt_x'
--           have := value?_symbolize?_id hwf hwf_ty hwf_x' hwt_x' hsym_x_ok
--           simp [this]
--         simp [hv]
--       | required ty =>
--         simp only [hqty] at hsym_x
--         split at hsym_x
--         contradiction
--         rename_i sym_x hsym_x_ok
--         simp only [Option.some.injEq] at hsym_x
--         simp [←hsym_x]
--         have ⟨v, hv⟩ : ∃ v, sym_x.value? = .some v := by
--           simp only [hqty] at hwf_qty
--           cases hwf_qty with | required_wf hwf_ty =>
--           simp only [hxx'] at hsym_x_ok
--           simp only [hqty] at hwt_x'
--           have := value?_symbolize?_id hwf hwf_ty hwf_x' hwt_x' hsym_x_ok
--           simp [this]
--         split
--         · simp [Term.value?] at hv
--         · simp [Term.value?] at hv
--         simp [hv]
--     unfold Term.value?
--     simp only [
--       hvs,
--       List.mapM₂_eq_mapM
--         (fun x => Term.value?.attrValue? x.fst x.snd)
--         (Map.mk ts).1,
--       Option.bind_some_fun, Option.some.injEq,
--       Value.record.injEq,
--     ]
--     cases rec with | mk rec =>
--     simp only [Map.mk.injEq]

--     have hts :
--       List.mapM
--       (fun x =>
--         match Map.find? rty x.fst, fun __do_lift =>
--             match __do_lift with
--             | Qualified.optional ty =>
--               match x.snd.symbolize? ty, fun __do_lift => some (x.fst, __do_lift.some) with
--               | none, x => none
--               | some a, f => f a
--             | Qualified.required ty =>
--               match x.snd.symbolize? ty, fun __do_lift => some (x.fst, __do_lift) with
--               | none, x => none
--               | some a, f => f a with
--           | none, x => none
--           | some a, f => f a)
--         (Map.mk rec).toList =
--       some ts
--     := by
--       apply Eq.symm

--       -- have := (List.mapM₂_eq_mapM (fun x =>
--       --   match Map.find? rty x.fst, fun __do_lift =>
--       --       match __do_lift with
--       --       | Qualified.optional ty =>
--       --         match x.snd.symbolize? ty, fun __do_lift => some (x.fst, Term.some __do_lift) with
--       --         | none, x => none
--       --         | some a, f => f a
--       --       | Qualified.required ty =>
--       --         match x.snd.symbolize? ty, fun __do_lift => some (x.fst, __do_lift) with
--       --         | none, x => none
--       --         | some a, f => f a with
--       --     | none, x => none
--       --     | some a, f => f a) (Map.mk rec).toList)
--       -- have := List.mapM₂_eq_mapM (λ ⟨a, v⟩ => do
--       --   match ← rty.find? a with
--       --   | .optional ty => .some (a, Option.some (← v.symbolize? ty))
--       --   | .required ty => .some (a, ← v.symbolize? ty)) (Map.mk rec).toList

--       -- simp [this]

--       -- apply Eq.trans (Eq.symm hts) this

--       sorry

--     rw [filterMap_mapM_combine hvs]
--     rw [filterMap_mapM_combine hts]
--     simp only [Map.toList, Map.kvs]
--     apply filterMap_partial_inverse
--     intros p hmem_p

--     split
--     · simp only [Option.bind_none, reduceCtorEq]
--       rename_i hnot_find
--       have hmem_p := (Map.in_list_iff_find?_some hwf_rec_map).mp hmem_p
--       have := h₁ p.fst
--       unfold Map.contains at this
--       simp only [Option.isSome, hmem_p, forall_const] at this
--       split at this
--       · rename_i h
--         simp [h] at hnot_find
--       · contradiction
--     rename_i qty hfind_qty
--     simp only
--     cases qty with
--     | optional ty =>
--       simp only
--       split
--       · rename_i hsym_p_nok
--         have ⟨y, hmem_y, hyok⟩ := List.mapM_some_implies_all_some hts p hmem_p
--         split at hyok
--         contradiction
--         simp only at hyok
--         rename_i hrty_find
--         simp only [hfind_qty, Option.some.injEq] at hrty_find
--         simp only [←hrty_find] at hyok
--         simp only [hsym_p_nok] at hyok
--         contradiction
--       · rename_i hsym_p hsym_p_ok
--         simp only [Option.bind_some, Term.value?.attrValue?]

--         sorry
--     | required ty =>
--       sorry

--     -- have ⟨y, hmem_y, hyok⟩ := List.mapM_some_implies_all_some hts p hmem_p
--     -- simp only [hyok, Option.bind_some]
--     -- have ⟨z, hmem_z, hzok⟩ := List.mapM_some_implies_all_some hvs y hmem_y
--     -- simp only [hzok, Option.bind_some]

--     -- have : ∀ v ∈ vs, ∃ v', v.2 = .some v' := by
--     --   sorry

--     -- have ⟨z', hz'⟩ := this z hmem_z
--     -- simp [hz']
--     -- all_goals sorry

--     -- apply List.filterMap_unattach

--     -- apply filterMap_always_some_eq
--     -- apply List.forall₂_iff_map_eq

--     -- simp [
--     --   List.mapM₂_eq_mapM (fun x =>
--     --   match Map.find? rty x.fst, fun __do_lift =>
--     --     match __do_lift with
--     --     | Qualified.optional ty =>
--     --       match x.snd.symbolize? ty, fun __do_lift => some (x.fst, Option.some __do_lift) with
--     --       | none, x => none
--     --       | some a, f => f a
--     --     | Qualified.required ty =>
--     --       match x.snd.symbolize? ty, fun __do_lift => some (x.fst, __do_lift) with
--     --       | none, x => none
--     --       | some a, f => f a with
--     --   | none, x => none
--     --   | some a, f => f a) rec.toList
--     -- ] at hts

--     -- have := List.mapM₂_eq_mapM (fun x =>
--     --     (Map.find? rty x.fst).bind fun __do_lift =>
--     --       match __do_lift with
--     --       | Qualified.optional ty => (x.snd.symbolize? ty).bind fun __do_lift => some (x.fst, __do_lift.some)
--     --       | Qualified.required ty => (x.snd.symbolize? ty).bind fun __do_lift => some (x.fst, __do_lift)) rec.toList

--     -- simp [this] at hts
--     -- have ⟨ts, hts⟩ :
--     --   ∃ ts,
--     --   (rec.toList.mapM₂ fun x =>
--     --     (Map.find? rty x.1.fst).bind fun __do_lift =>
--     --       match __do_lift with
--     --       | Qualified.optional ty => (x.1.snd.symbolize? ty).bind fun __do_lift => some (x.1.fst, __do_lift.some)
--     --       | Qualified.required ty => (x.1.snd.symbolize? ty).bind fun __do_lift => some (x.1.fst, __do_lift)) = .some ts
--     -- := by
--     --   sorry
--     -- rw [hts] at hok

--     -- sorry

-- /--
-- `Value.symbolize?` is total on well-typed values,
-- and the resulting term is a well-formed literal

-- TODO: might need an additional assumption `v.WellStructured`?
-- -/
-- theorem value_symbolize?_ok_same
--   {Γ : TypeEnv} {entities : Entities} {v : Value} {ty : CedarType}
--   (hwf : Γ.WellFormed)
--   (hwf_ty : ty.WellFormed Γ)
--   (hwf_v : v.WellFormed entities)
--   (hwt : InstanceOfType Γ v ty) :
--   ∃ t,
--     v.symbolize? ty = .some t ∧
--     v ∼ t
-- := by
--   sorry
--   -- cases hwt with
--   -- | instance_of_bool
--   -- | instance_of_string
--   -- | instance_of_entity
--   -- | instance_of_ext
--   -- | instance_of_int =>
--   --   simp [
--   --     Value.symbolize?, Prim.symbolize,
--   --     Same.same, SameValues,
--   --     Term.value?, TermPrim.value?, BitVec.int64?,
--   --   ]
--   -- | instance_of_set s sty hwt =>
--   --   cases hwf_ty with | set_wf hwf_sty =>
--   --   cases hwf_v with | set_wf hwf_v hwf_s =>
--   --   -- `symbolize?` on elements should succeed
--   --   have ⟨ts, hts⟩ :
--   --     ∃ ts,
--   --       s.toList.mapM (fun v => v.symbolize? sty) = .some ts
--   --   := by
--   --     apply List.all_some_implies_mapM_some
--   --     intros x hmem_x
--   --     have := hwt x hmem_x
--   --     have ⟨t, ht, _⟩ := value_symbolize?_same hwf hwf_sty (hwf_v x hmem_x) this
--   --     exists t
--   --   -- `value? ∘ symbolize?` should succeed on elements
--   --   have ⟨vs, hvs⟩ :
--   --     ∃ vs,
--   --       (Set.make ts).1.mapM (λ t => t.value?) = .some vs
--   --   := by
--   --     apply List.all_some_implies_mapM_some
--   --     intros t hmem_t
--   --     have := (Set.make_mem _ _).mpr hmem_t
--   --     have hts := List.mapM_some_implies_all_from_some hts
--   --     have ⟨x, hmem_x, hsym_x⟩ := hts t this
--   --     have hwt_x := hwt x hmem_x
--   --     have ⟨y, hy, hsame_y⟩ := value_symbolize?_same hwf hwf_sty (hwf_v x hmem_x) hwt_x
--   --     simp only [hsym_x, Option.some.injEq] at hy
--   --     exists x
--   --     simp only [←hy] at hsame_y
--   --     exact hsame_y
--   --   simp only [
--   --     Value.symbolize?,
--   --     List.mapM₁_eq_mapM (λ v => v.symbolize? sty) s.toList,
--   --   ]
--   --   simp only [
--   --     hts, Option.bind_some_fun,
--   --     Option.some.injEq, exists_eq_left',
--   --     Same.same, SameValues,
--   --   ]
--   --   unfold Term.value?
--   --   simp only [
--   --     List.mapM₁_eq_mapM ?_ (Set.make ts).1,
--   --   ]
--   --   simp only [hvs, Option.bind_some_fun, Option.some.injEq, Value.set.injEq]
--   --   -- Prove that the sets of values before and after `value? ∘ symbolize?` are equal
--   --   apply (Set.subset_iff_eq (Set.make_wf _) hwf_s).mp
--   --   constructor
--   --   · apply Set.subset_def.mpr
--   --     intros new_v hmem_new_v
--   --     have hmem_new_v := (Set.make_mem _ _).mpr hmem_new_v
--   --     have ⟨x, hmem_x, hx_value?⟩ := List.mapM_some_implies_all_from_some hvs new_v hmem_new_v
--   --     have hmem_x := (Set.make_mem _ _).mpr hmem_x
--   --     have ⟨old_v, hmem_old_v, hold_v_symbolic?⟩ := List.mapM_some_implies_all_from_some hts x hmem_x

--   --     sorry
--   --   · sorry
--   -- | instance_of_record rec =>
--   --   sorry

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
