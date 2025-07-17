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

import Cedar.Thm.SymCC.Env.WF
import Cedar.SymCC.Decoder

/-! Some facts about `default*` -/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Spec
open Cedar.SymCC
open Cedar.Data

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
    apply List.map_id_eq
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

end Cedar.Thm
