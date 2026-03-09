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

import Cedar.Data.SizeOf
import Cedar.SymCC.Decoder
import Cedar.Thm.SymCC.Data
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Term.Lit
import Cedar.Thm.SymCC.Term.TypeOf

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
    cases hwf_ty ; assumption
  | set ty' =>
    simp only [Decoder.defaultLit]
    constructor
    · intros t ht
      exfalso
      exact Set.not_mem_empty _ ht
    · intros t ht
      exfalso
      exact Set.not_mem_empty _ ht
    · cases hwf_ty ; assumption
    · exact Set.empty_wf
  | record rty =>
    cases rty with | mk attrs =>
    cases hwf_ty with | record_wf hwf_rty hwf_rty_map =>
    simp only [Decoder.defaultLit]
    simp only [Map.mapOnValues₂_eq_mapOnValues]
    constructor
    · intros attr t hmem_attr_t
      replace hmem_attr_t := Map.mem_toList_find? (Map.mapOnValues_wf.mp hwf_rty_map) hmem_attr_t
      replace ⟨attr_ty, hmem_attr_t, _⟩ := Map.find?_mapOnValues_some' _ hmem_attr_t
      subst t
      have := Map.sizeOf_lt_of_find? hmem_attr_t
      apply default_lit_wf _ hwf_eidOf
      apply hwf_rty attr
      exact hmem_attr_t
    · exact Map.mapOnValues_wf.mp hwf_rty_map
termination_by sizeOf ty
decreasing_by
  subst_vars
  simp at *
  omega

theorem default_lit_is_lit
  {eidOf : EntityType → String} {ty : TermType} :
  (Decoder.defaultLit eidOf ty).isLiteral
:= by
  cases ty with
  | prim p =>
    cases p
    all_goals
      simp [Decoder.defaultLit, Decoder.defaultPrim, Term.isLiteral]
  | record rty =>
    simp only [Decoder.defaultLit]
    rw [Map.mapOnValues₂_eq_mapOnValues]
    rw [isLiteral_record_mapOnValues]
    intro tty htty
    exact default_lit_is_lit
  | _ => simp [Decoder.defaultLit, Term.isLiteral]
termination_by sizeOf ty
decreasing_by
  simp_wf
  have := Map.sizeOf_lt_of_values htty
  omega

public theorem default_lit_well_typed
  {eidOf : EntityType → String} {ty : TermType} :
  (Decoder.defaultLit eidOf ty).typeOf = ty
:= by
  cases ty with
  | prim p =>
    cases p with
    | ext x => cases x <;>
        simp [Decoder.defaultLit, Decoder.defaultPrim, Decoder.defaultExt, typeOf_term_prim_ext_datetime, typeOf_term_prim_ext_decimal, typeOf_term_prim_ext_duration, typeOf_term_prim_ext_ipaddr]
    | _ => simp [Decoder.defaultLit, Decoder.defaultPrim, typeOf_bool, typeOf_bv, typeOf_term_prim_string, typeOf_term_prim_entity]
  | option => simp only [Decoder.defaultLit, typeOf_term_none]
  | set => simp only [Decoder.defaultLit, typeOf_term_set]
  | record rty =>
    simp only [Decoder.defaultLit, typeOf_term_record_eq]
    congr
    rw [Map.mapOnValues₂_eq_mapOnValues, Map.mapOnValues_mapOnValues]
    unfold Function.comp
    apply Map.mapOnValues_restricted_id
    intro tty htty
    exact default_lit_well_typed
termination_by sizeOf ty
decreasing_by
  simp_wf
  have := Map.sizeOf_lt_of_values htty
  omega

end Cedar.Thm
