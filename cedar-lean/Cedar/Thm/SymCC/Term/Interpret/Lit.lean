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

import Cedar.Thm.SymCC.Data
import Cedar.Thm.SymCC.Term.Interpret.Basic
import Cedar.Thm.SymCC.Term.Interpret.WF
import Cedar.Thm.SymCC.Term.Lit
import Cedar.Thm.SymCC.Term.PE
import Cedar.Thm.SymCC.Term.WF
import Cedar.Thm.SymCC.Interpretation

/-!
# Interpretation preserves well-formedness of Terms

This file proves that interpretation produces literals that preserve
well-formedness: interpreting a well-formed term of a given type produces a
well-formed literal term of the same type. It also proves that interpreting
a well-formed literal produces that same literal.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

private theorem interpret_term_set_lit_id {εs : SymEntities} {I : Interpretation} {s : Set Term} {ty : TermType}
  (h₁ : (Term.set s ty).WellFormed εs)
  (ih : ∀ t, t ∈ s → t.interpret I = t):
  (Term.set s ty).interpret I = Term.set s ty
:= by
  simp only [interpret_term_set, Set.elts, Term.set.injEq, and_true]
  have h₄ : List.map (Term.interpret I) s.1 = List.map id s.1 := by
    apply List.map_congr ; simp only [id_eq] ; exact ih
  simp only [List.map_id] at h₄
  replace h₂ := wf_term_set_implies_wf_set h₁
  simp only [Set.WellFormed, Set.toList, Set.elts] at h₂
  rw [← h₄, eq_comm] at h₂
  exact h₂

private theorem interpret_term_record_lit_id {εs : SymEntities} {I : Interpretation} {r: Map Attr Term}
  (h₁ : Term.WellFormed εs (Term.record r))
  (ih : ∀ (a : Attr) (t : Term), (a, t) ∈ r.toList → Term.interpret I t = t) :
  Term.interpret I (Term.record r) = Term.record r
:= by
  simp [interpret_term_record, Map.toList]
  have h₄ : List.map (fun x => (x.fst, Term.interpret I x.snd)) r.toList = List.map id r.toList := by
    apply List.map_congr
    intro x h₂
    simp only [id_eq, ih x.fst x.snd h₂]
  simp only [List.map_id] at h₄
  replace h₂ := wf_term_record_implies_wf_map h₁
  simp only [Map.WellFormed] at h₂
  rw [← h₄, eq_comm] at h₂
  exact h₂

theorem interpret_term_lit_id {εs : SymEntities} (I : Interpretation) {t : Term}
  (h₁ : t.WellFormedLiteral εs) :
  t.interpret I = t
:= by
  have ⟨h₂, h₃⟩ := h₁
  match t with
  | .var _ | .app _ _ _ =>
    simp only [Term.isLiteral, Bool.false_eq_true] at h₃
  | .prim _ =>
    simp only [interpret_term_prim]
  | .none _ =>
    simp only [interpret_term_none]
  | .some _ =>
    simp only [Term.isLiteral] at h₃
    replace h₂ := wf_term_some_implies h₂
    simp only [interpret_term_some, Term.some.injEq]
    exact interpret_term_lit_id I (And.intro h₂ h₃)
  | .set s ty =>
    have ih : ∀ t', t' ∈ s → t'.interpret I = t' := by
      intro t' h₄
      have _ := Set.sizeOf_lt_of_mem h₄ -- termination
      exact interpret_term_lit_id I
        (And.intro
          (wf_term_set_implies_wf_elt h₂ h₄)
          (lit_term_set_implies_lit_elt h₃ h₄))
    exact interpret_term_set_lit_id h₁.left ih
  | .record r =>
    have ih : ∀ a' t', (a', t') ∈ r.1 → t'.interpret I = t' := by
      intro a' t' h₄
      have _ := Map.sizeOf_lt_of_value h₄ -- termination
      exact interpret_term_lit_id I
        (And.intro
          (wf_term_record_implies_wf_value h₂ h₄)
          (lit_term_record_implies_lit_value h₃ h₄))
    exact interpret_term_record_lit_id h₁.left ih
termination_by sizeOf t

private theorem interpret_term_set_lit {I : Interpretation} {s : Set Term} {ty: TermType}
  (ih : ∀ (t : Term), t ∈ s → Term.isLiteral (Term.interpret I t) = true) :
  Term.isLiteral (Term.interpret I (Term.set s ty)) = true
:= by
  simp only [interpret_term_set]
  unfold Term.isLiteral
  simp only [List.attach_def, List.all_pmap_subtype Term.isLiteral, List.all_eq_true]
  intro t h₁
  rw [Set.in_list_iff_in_set, ← Set.make_mem] at h₁
  simp only [List.mem_map] at h₁
  replace ⟨t', h₁, h₂⟩ := h₁
  subst h₂
  rw [Set.in_list_iff_in_set] at h₁
  exact ih t' h₁

private theorem interpret_term_record_lit {I : Interpretation} {r : Map Attr Term}
  (ih : ∀ (a : Attr) (t : Term), (a, t) ∈ Map.toList r → Term.isLiteral (Term.interpret I t) = true) :
  Term.isLiteral (Term.interpret I (Term.record r)) = true
:= by
  simp only [interpret_term_record]
  unfold Term.isLiteral
  simp only [
    List.attach₃,
    List.all_pmap_subtype λ (x : Attr × Term) => Term.isLiteral x.snd,
    List.all_eq_true]
  intro x h₁
  simp only [Map.make] at h₁
  have h₂ := List.canonicalize_subseteq Prod.fst (r.toList.map λ x => (x.fst, Term.interpret I x.snd))
  simp only [List.subset_def] at h₂
  specialize h₂ h₁
  simp only [List.mem_map] at h₂
  replace ⟨x', h₁, h₂⟩ := h₂
  subst h₂
  simp only
  apply ih x'.fst x'.snd
  simp [h₁]

private theorem interpret_wf_is_wfl {εs : SymEntities} {I : Interpretation} {t : Term} {ty : TermType} :
  Interpretation.WellFormed I εs →
  Term.WellFormed εs t →
  t.typeOf = ty →
  (t.interpret I).isLiteral →
  (t.interpret I).WellFormedLiteral εs ∧ (t.interpret I).typeOf = ty
:= by
  intro hI hwf ht ih
  replace hwf := interpret_term_wf hI hwf
  simp only [ht] at hwf
  simp only [Term.WellFormedLiteral, hwf, ih, and_self]

local macro "interpret_wf_to_wfl"
  t:ident hI:ident hwf:ident ht:ident ih:ident : term => do
  `(term| (
    let ih'  := $ih $t (by simp only [List.mem_cons, List.mem_singleton, or_true, true_or])
    let hwf' := $hwf $t (by simp only [List.mem_cons, List.mem_singleton, or_true, true_or])
    interpret_wf_is_wfl $hI hwf' $ht ih'
  ))

local macro "show_interpret_term_app_unary_lit"
  t:ident hI:ident hwf:ident ht:ident ih:ident
  interpret_thm:ident pe_thm:term : tactic => do
 `(tactic| (
    have ⟨hl, hr⟩ := interpret_wf_to_wfl $t $hI $hwf $ht $ih
    simp only [$interpret_thm:ident, $pe_thm:term hl hr]
  ))

local macro "show_interpret_term_app_binary_lit"
  t₁:ident t₂:ident hI:ident hwf:ident h₁:ident h₂:ident ih:ident interpret_thm:ident pe_thm:term : tactic => do
 `(tactic| (
    have ⟨hl₁, hr₁⟩ := interpret_wf_to_wfl $t₁ $hI $hwf $h₁ $ih
    have ⟨hl₂, hr₂⟩ := interpret_wf_to_wfl $t₂ $hI $hwf $h₂ $ih
    simp only [$interpret_thm:ident, $pe_thm:term hl₁ hr₁ hl₂ hr₂]
    ))

private theorem interpret_term_app_ext_lit {εs : SymEntities} {I : Interpretation} {xop : ExtOp} {ts : List Term} {ty : TermType}
  (hI  : Interpretation.WellFormed I εs)
  (hwf : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hwt : ExtOp.WellTyped xop ts ty)
  (ih  : ∀ (t : Term), t ∈ ts → Term.isLiteral (Term.interpret I t) = true) :
  Term.isLiteral (Term.interpret I (Term.app (.ext xop) ts ty)) = true
:= by
  cases hwt
  case decimal.val_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_ext_decimal_val pe_ext_decimal_val_wfl
  case ipaddr.isV4_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_ext_ipaddr_isV4 pe_ext_ipaddr_isV4_wfl
  case ipaddr.addrV4_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_ext_ipaddr_addrV4 (pe_ext_ipaddr_addrV4'_wfl hI)
  case ipaddr.prefixV4_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_ext_ipaddr_prefixV4 (pe_ext_ipaddr_prefixV4'_wfl hI)
  case ipaddr.addrV6_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_ext_ipaddr_addrV6 (pe_ext_ipaddr_addrV6'_wfl hI)
  case ipaddr.prefixV6_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_ext_ipaddr_prefixV6 (pe_ext_ipaddr_prefixV6'_wfl hI)
  case datetime.val_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_ext_datetime_val pe_ext_datetime_val_wfl
  case datetime.ofBitVec_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_ext_datetime_ofBitVec pe_ext_datetime_ofBitVec_wfl
  case duration.val_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_ext_duration_val pe_ext_duration_val_wfl
  case duration.ofBitVec_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_ext_duration_ofBitVec pe_ext_duration_ofBitVec_wfl

private theorem interpret_term_app_lit {εs : SymEntities} {I : Interpretation} {op : Op} {ts : List Term} {ty : TermType}
  (hI  : Interpretation.WellFormed I εs)
  (hwf : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hwt : Op.WellTyped εs op ts ty)
  (ih  : ∀ (t : Term), t ∈ ts → Term.isLiteral (Term.interpret I t) = true) :
  Term.isLiteral (Term.interpret I (Term.app op ts ty)) = true
:= by
  cases hwt
  case not_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_not pe_not_wfl
  case and_wt t₁ t₂ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_and pe_and_wfl
  case or_wt t₁ t₂ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_or pe_or_wfl
  case eq_wt t₁ t₂ h₁ =>
    have ⟨hl₁, _⟩ := interpret_wf_to_wfl t₁ hI hwf rfl ih
    have ⟨hl₂, _⟩ := interpret_wf_to_wfl t₂ hI hwf rfl ih
    simp only [interpret_term_app_eq, pe_eq_lit hl₁.right hl₂.right, Term.isLiteral]
  case ite_wt t₁ t₂ t₃ h₁ h₂ =>
    have ⟨hl₁, hr₁⟩ := interpret_wf_to_wfl t₁ hI hwf h₁ ih
    have ⟨hl₂, _⟩ := interpret_wf_to_wfl t₂ hI hwf rfl ih
    have ⟨hl₃, _⟩ := interpret_wf_to_wfl t₃ hI hwf rfl ih
    simp only [interpret_term_app_ite, pe_ite_wfl hl₁ hl₂ hl₃ hr₁]
  case uuf_wt f t h₁ h₂ =>
    have ht := interpret_wf_to_wfl t hI hwf h₁ ih
    have hf := wf_interpretation_implies_wf_udf hI h₂
    simp only [interpret_term_app_uuf, pe_app_wfl ht.left hf.left]
  case bvneg_wt t _ h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_bvneg pe_bvneg_wfl
  case bvnego_wt t _ h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_bvnego pe_bvnego_wfl
  case bvadd_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvadd pe_bvadd_wfl
  case bvsub_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvsub pe_bvsub_wfl
  case bvmul_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvmul pe_bvmul_wfl
  case bvsdiv_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvsdiv pe_bvsdiv_wfl
  case bvudiv_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvudiv pe_bvudiv_wfl
  case bvsrem_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvsrem pe_bvsrem_wfl
  case bvsmod_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvsmod pe_bvsmod_wfl
  case bvumod_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvumod pe_bvumod_wfl
  case bvshl_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvshl pe_bvshl_wfl
  case bvlshr_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvlshr pe_bvlshr_wfl
  case bvsaddo_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvsaddo pe_bvsaddo_wfl
  case bvssubo_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvssubo pe_bvssubo_wfl
  case bvsmulo_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvsmulo pe_bvsmulo_wfl
  case bvslt_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvslt pe_bvslt_wfl
  case bvsle_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvsle pe_bvsle_wfl
  case bvult_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvult pe_bvult_wfl
  case bvule_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_bvule pe_bvule_wfl
  case zero_extend_wt t _ _ h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_zero_extend pe_zero_extend_wfl
  case set.member_wt t₁ t₂ h₁ =>
    have ⟨hl₁, _⟩ := interpret_wf_to_wfl t₁ hI hwf rfl ih
    have ⟨hl₂, hr₂⟩ := interpret_wf_to_wfl t₂ hI hwf h₁ ih
    simp only [interpret_term_app_set_member, pe_set_member_wfl hl₁ hl₂ hr₂]
  case set.subset_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_set_subset pe_set_subset_wfl
  case set.inter_wt t₁ t₂ _ h₁ h₂ =>
    show_interpret_term_app_binary_lit t₁ t₂ hI hwf h₁ h₂ ih interpret_term_app_set_inter pe_set_inter_wfl
  case option.get_wt t h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_option_get (pe_option_get'_wfl hI)
  case record.get_wt t a rty h₁ h₂ =>
    have ht := interpret_wf_to_wfl t hI hwf h₁ ih
    simp only [interpret_term_app_record_get, pe_record_get_wfl ht.left ht.right h₂]
  case string.like_wt t _ h₁ =>
    show_interpret_term_app_unary_lit t hI hwf h₁ ih interpret_term_app_string_like pe_string_like_wfl
  case ext_wt h₁ =>
    exact interpret_term_app_ext_lit hI hwf h₁ ih

theorem interpret_term_lit {εs : SymEntities} {I : Interpretation} {t : Term}
  (h₀ : I.WellFormed εs)
  (h₁ : t.WellFormed εs) :
  (t.interpret I).isLiteral
:= by
  induction h₁
  case prim_wf =>
    simp only [interpret_term_prim, Term.isLiteral]
  case var_wf h₁ =>
    simp only [interpret_term_var, (wf_interpretation_implies_wfl_var h₀ h₁).right]
  case none_wf =>
    simp only [interpret_term_none, Term.isLiteral]
  case some_wf ih =>
    simp only [interpret_term_some, Term.isLiteral, ih]
  case app_wf h₁ h₂ ih =>
    exact interpret_term_app_lit h₀ h₁ h₂ ih
  case set_wf ih =>
    exact interpret_term_set_lit ih
  case record_wf ih =>
    exact interpret_term_record_lit ih

theorem interpret_term_wfl {εs : SymEntities} {I : Interpretation} {t : Term}
  (h₁ : I.WellFormed εs)
  (h₂ : t.WellFormed εs) :
  (t.interpret I).WellFormedLiteral εs ∧
  (t.interpret I).typeOf = t.typeOf
:= by
  simp only [Term.WellFormedLiteral, interpret_term_wf h₁ h₂, interpret_term_lit h₁ h₂, and_self]

end Cedar.Thm
