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
import Cedar.Thm.SymCC.Term.WF
import Cedar.Thm.SymCC.Interpretation

/-!
# Interpretation preserves well-formedness of Terms

This file proves that interpretation preserves well-formedness: interpreting a
well-formed term of a given type produces a well-formed term of the same type.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory



def InterpretTermWF (εs : SymEntities) (I : Interpretation) (t : Term) : Prop :=
  (t.interpret I).WellFormed εs ∧
  (t.interpret I).typeOf = t.typeOf

theorem interpret_term_prim_wf {εs : SymEntities} {I : Interpretation} {p : TermPrim}
  (h : Term.WellFormed εs (Term.prim p)) :
  InterpretTermWF εs I (Term.prim p)
:= by
  simp only [InterpretTermWF, interpret_term_prim, and_true, h]

theorem interpret_term_var_wf {εs : SymEntities} {I : Interpretation} {v : TermVar}
  (h₁ : I.WellFormed εs)
  (h₂ : Term.WellFormed εs (Term.var v)) :
  InterpretTermWF εs I (Term.var v)
:= by
  simp only [InterpretTermWF, interpret_term_var, Term.typeOf]
  replace h₂ := wf_term_var_implies h₂
  constructor
  exact wf_interpretation_implies_wf_var h₁ h₂
  exact wf_interpretation_implies_typeOf_var h₁ h₂

theorem interpret_term_none_wf {εs : SymEntities} {I : Interpretation} {ty : TermType}
  (h : Term.WellFormed εs (Term.none ty)) :
  InterpretTermWF εs I (Term.none ty)
:= by
  simp only [InterpretTermWF, interpret_term_none, and_true, h]

theorem interpret_term_some_wf {εs : SymEntities} {I : Interpretation} {t : Term}
  (ih : InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.some t)
:= by
  simp only [InterpretTermWF, interpret_term_some, Term.typeOf, ih.right, and_true]
  exact Term.WellFormed.some_wf ih.left

private theorem interpret_term_set_wf_aux {I : Interpretation} {s : Set Term} {t : Term} :
  t ∈ Set.make (List.map (Term.interpret I) (Set.elts s)) →
  ∃ t', t' ∈ s ∧ t = t'.interpret I
:= by
  intro h₁
  simp only [←Set.make_mem, List.mem_map] at h₁
  replace ⟨t', h₁, h₂⟩ := h₁
  exists t'
  simp only [h₂, and_true]
  simp only [Membership.mem] at *
  assumption

theorem interpret_term_set_wf {εs : SymEntities} {I : Interpretation} {s : Set Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.set s ty))
  (ih : ∀ (t : Term), t ∈ s → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.set s ty)
:= by
  simp only [InterpretTermWF, interpret_term_set, Term.typeOf, and_true]
  apply Term.WellFormed.set_wf
  case h₁ =>
    intro t h₂
    have ⟨t', h₃, h₄⟩ := interpret_term_set_wf_aux h₂
    subst h₄
    exact (ih t' h₃).left
  case h₂ =>
    intro t h₂
    have ⟨t', h₃, h₄⟩ := interpret_term_set_wf_aux h₂
    subst h₄
    have h₅ := wf_term_set_implies_typeOf_elt h₁ h₃
    subst h₅
    exact (ih t' h₃).right
  case h₃ => exact wf_term_set_implies_wf_type h₁
  case h₄ => exact Set.make_wf (List.map (Term.interpret I) (Set.elts s))

theorem interpret_term_record_wf {εs : SymEntities} {I : Interpretation} {r : Map Attr Term}
  (h₁ : Term.WellFormed εs (Term.record r))
  (ih :  ∀ (a : Attr) (t : Term), (a, t) ∈ r.1 → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.record r)
:= by
  simp [InterpretTermWF, interpret_term_record]
  constructor
  case left  =>
    apply Term.WellFormed.record_wf
    case h₁ =>
      intro a t h₄
      simp only [Map.toList] at *
      replace h₄ := Map.make_mem_list_mem h₄
      simp only [List.mem_map, Prod.mk.injEq] at h₄
      replace ⟨kv, h₄, h₅, h₆⟩ := h₄
      subst h₅ h₆
      exact (ih kv.fst kv.snd h₄).left
    case h₂ => exact Map.make_wf (List.map (fun x => (x.fst, Term.interpret I x.snd)) (Map.kvs r))
  case right =>
    replace h₁ := wf_term_record_implies_wf_map h₁
    rw [←Map.toList, ←Map.mapOnValues_eq_make_map (Term.interpret I) h₁]
    unfold Term.typeOf
    simp only [Map.mapOnValues, Map.kvs, List.attach₃, TermType.record.injEq, Map.mk.injEq]
    simp only [List.map_pmap_subtype (λ (x : Attr × Term) => (x.fst, Term.typeOf x.snd)), List.map_map]
    apply List.map_congr
    intros atᵢ h₂
    replace ih := (ih atᵢ.1 atᵢ.2 h₂).right
    simp only [ih, Function.comp_apply]

local macro "show_interpret_term_app_wf_unary" h1:ident ih:ident invert:ident wfdestruct:ident wfconstruct:term : tactic => do
 -- Using un-hygienic identifiers here because of a naming bug in the rename_i
 -- tactic that's making tactic-local names inaccessible.
 let h2 := Lean.mkIdent `__inv__h2
 let h3 := Lean.mkIdent `__inv__h3
 `(tactic| (
    simp only [InterpretTermWF];
    first
      | replace ⟨$h1:ident, _, $h2:ident, _, $h3:ident⟩ := $wfdestruct:ident $h1:ident;
        subst $h1:ident $h2:ident -- most ops
      | replace ⟨_, $h1:ident, _, $h2:ident, _, $h3:ident⟩ := $wfdestruct:ident $h1:ident;
        subst $h1:ident $h2:ident -- bvneg
      | replace ⟨$h1:ident, _, _, $h2:ident, _, $h3:ident⟩ := $wfdestruct:ident $h1:ident;
        subst $h1:ident $h2:ident -- bvnego
    simp only [$invert:ident, Term.typeOf];
    simp only [List.mem_singleton, InterpretTermWF, forall_eq, $h3:ident] at $ih:ident;
    exact $wfconstruct ($ih:ident).left ($ih:ident).right
  ))

private theorem interpret_term_app_wf_not {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .not ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .not ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_not wf_term_app_not wf_not

private theorem interpret_term_app_wf_uuf {εs : SymEntities} {I : Interpretation} {ts : List Term} {f : UUF} {ty : TermType}
  (h₀ : I.WellFormed εs)
  (h₁ : Term.WellFormed εs (Term.app (.uuf f) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.uuf f) ts ty)
:= by
  simp only [InterpretTermWF]
  replace ⟨h₁, ⟨_, h₂, h₃⟩, h₄⟩ := wf_term_app_uuf h₁
  subst h₁ h₂
  simp only [interpret_term_app_uuf, Term.typeOf]
  simp only [List.mem_cons, List.mem_singleton, InterpretTermWF, forall_eq_or_imp, forall_eq] at ih
  replace ⟨ih, ih'⟩ := ih.left
  have h₅ := wf_interpretation_implies_wf_udf h₀ h₄
  have h₆ : f.out = (UnaryFunction.udf (Interpretation.funs I f)).outType := by simp only [UnaryFunction.outType, h₅]
  rw [h₆]
  apply wf_app ih
  case h₂ => simp only [ih', h₃.right, UnaryFunction.argType, h₅]
  case h₃ => simp only [UnaryFunction.WellFormed, h₅]

private theorem interpret_term_app_wf_bvneg {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvneg ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvneg ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_bvneg wf_term_app_bvneg wf_bvneg

private theorem interpret_term_app_wf_bvnego {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvnego ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvnego ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_bvnego wf_term_app_bvnego wf_bvnego

private theorem interpret_term_app_wf_zero_extend {εs : SymEntities} {I : Interpretation} {ts : List Term} {n : Nat} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app (.zero_extend n) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.zero_extend n) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_zero_extend wf_term_app_zero_extend wf_zero_extend

private theorem interpret_term_app_wf_string_like {εs : SymEntities} {I : Interpretation} {ts : List Term} {p : Pattern} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app (.string.like p) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.string.like p) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_string_like wf_term_app_string_like wf_string_like

private theorem interpret_term_app_wf_option_get {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₀ : I.WellFormed εs)
  (h₁ : Term.WellFormed εs (Term.app .option.get ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .option.get ts ty)
:= by
  simp only [InterpretTermWF]
  replace ⟨_, h₁, _, h₃⟩ := wf_term_app_option_get h₁
  subst h₁
  simp only [interpret_term_app_option_get, Term.typeOf]
  simp only [List.mem_singleton, InterpretTermWF, forall_eq, h₃] at ih
  exact wf_option_get' h₀ ih.left ih.right

private theorem interpret_term_app_wf_ext_decimal_val {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app (.ext .decimal.val) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.ext .decimal.val) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_ext_decimal_val wf_term_app_ext_decimal_val wf_ext_decimal_val

private theorem interpret_term_app_wf_ext_ipaddr_isV4 {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app (.ext .ipaddr.isV4) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.ext .ipaddr.isV4) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_ext_ipaddr_isV4 wf_term_app_ext_ipaddr_isV4 wf_ext_ipaddr_isV4

private theorem interpret_term_app_wf_ext_ipaddr_addrV4 {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₀ : I.WellFormed εs)
  (h₁ : Term.WellFormed εs (Term.app (.ext .ipaddr.addrV4) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.ext .ipaddr.addrV4) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_ext_ipaddr_addrV4 wf_term_app_ext_ipaddr_addrV4 (wf_ext_ipaddr_addrV4' h₀)

private theorem interpret_term_app_wf_ext_ipaddr_prefixV4 {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₀ : I.WellFormed εs)
  (h₁ : Term.WellFormed εs (Term.app (.ext .ipaddr.prefixV4) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.ext .ipaddr.prefixV4) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_ext_ipaddr_prefixV4 wf_term_app_ext_ipaddr_prefixV4 (wf_ext_ipaddr_prefixV4' h₀)

private theorem interpret_term_app_wf_ext_ipaddr_addrV6 {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₀ : I.WellFormed εs)
  (h₁ : Term.WellFormed εs (Term.app (.ext .ipaddr.addrV6) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.ext .ipaddr.addrV6) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_ext_ipaddr_addrV6 wf_term_app_ext_ipaddr_addrV6 (wf_ext_ipaddr_addrV6' h₀)

private theorem interpret_term_app_wf_ext_ipaddr_prefixV6 {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₀ : I.WellFormed εs)
  (h₁ : Term.WellFormed εs (Term.app (.ext .ipaddr.prefixV6) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.ext .ipaddr.prefixV6) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_ext_ipaddr_prefixV6 wf_term_app_ext_ipaddr_prefixV6 (wf_ext_ipaddr_prefixV6' h₀)

private theorem interpret_term_app_wf_ext_datetime_val {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app (.ext .datetime.val) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.ext .datetime.val) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_ext_datetime_val wf_term_app_ext_datetime_val wf_ext_datetime_val

private theorem interpret_term_app_wf_ext_datetime_ofBitVec {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app (.ext .datetime.ofBitVec) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.ext .datetime.ofBitVec) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_ext_datetime_ofBitVec wf_term_app_ext_datetime_ofBitVec wf_ext_datetime_ofBitVec

private theorem interpret_term_app_wf_ext_duration_val {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app (.ext .duration.val) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.ext .duration.val) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_ext_duration_val wf_term_app_ext_duration_val wf_ext_duration_val

private theorem interpret_term_app_wf_ext_duration_ofBitVec {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app (.ext .duration.ofBitVec) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.ext .duration.ofBitVec) ts ty)
:= by show_interpret_term_app_wf_unary h₁ ih interpret_term_app_ext_duration_ofBitVec wf_term_app_ext_duration_ofBitVec wf_ext_duration_ofBitVec

local macro "show_interpret_term_app_wf_binary" h1:ident ih:ident invert:ident wfdestruct:ident wfconstruct:ident : tactic => do
 let h2 := Lean.mkIdent `__inv__h2
 let h3 := Lean.mkIdent `__inv__h3
 let h4 := Lean.mkIdent `__inv__h4
 `(tactic| (
    simp only [InterpretTermWF];
    first
      | replace ⟨_, $h1:ident, _, _, $h2:ident, $h3:ident, $h4:ident⟩ := $wfdestruct:ident $h1:ident;
        subst $h1:ident $h2:ident -- bvops
      | replace ⟨$h1:ident, _, _, $h2:ident, $h3:ident, _, $h4:ident⟩ := $wfdestruct:ident $h1:ident;
        subst $h1:ident $h2:ident -- and/or
      | replace ⟨$h1:ident, _, _, _, $h2:ident, $h3:ident, $h4:ident⟩ := $wfdestruct:ident $h1:ident;
        subst $h1:ident $h2:ident; -- eq
    simp only [$invert:ident, Term.typeOf];
    simp only [List.mem_cons, List.mem_singleton, InterpretTermWF, forall_eq_or_imp, forall_eq] at $ih:ident;
    simp only [WFArg] at $h3:ident $h4:ident;
    apply $wfconstruct:ident <;>
    simp only [$ih:ident, $h3:ident, $h4:ident]
  ))

private theorem interpret_term_app_wf_and {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .and ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .and ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_and wf_term_app_and wf_and

private theorem interpret_term_app_wf_or {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .or ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .or ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_or wf_term_app_or wf_or

private theorem interpret_term_app_wf_eq {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .eq ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .eq ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_eq wf_term_app_eq wf_eq

private theorem interpret_term_app_wf_ite {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .ite ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .ite ts ty)
:= by
  simp only [InterpretTermWF]
  replace ⟨t₁, t₂, t₃, h₁, h₂, h₃, h₄⟩ := wf_term_app_ite h₁
  subst h₁
  simp only [interpret_term_app_ite, Term.typeOf]
  simp only [List.mem_cons, List.mem_singleton, InterpretTermWF, forall_eq_or_imp, forall_eq] at ih
  have ⟨_, ih₂, _, _⟩ := ih
  simp only [WFArg] at h₂ h₃ h₄
  rw [←h₃.right, ←ih₂.right]
  apply wf_ite <;>
  simp only [ih, h₂, h₃, h₄]

private theorem interpret_term_app_wf_bvadd {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvadd ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvadd ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_bvadd wf_term_app_bvadd wf_bvadd

private theorem interpret_term_app_wf_bvsub {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvsub ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvsub ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_bvsub wf_term_app_bvsub wf_bvsub

private theorem interpret_term_app_wf_bvmul {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvmul ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvmul ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_bvmul wf_term_app_bvmul wf_bvmul

private theorem interpret_term_app_wf_bvsdiv {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvsdiv ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvsdiv ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_bvsdiv wf_term_app_bvsdiv wf_bvsdiv

private theorem interpret_term_app_wf_bvudiv {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvudiv ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvudiv ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_bvudiv wf_term_app_bvudiv wf_bvudiv

private theorem interpret_term_app_wf_bvsrem {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvsrem ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvsrem ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_bvsrem wf_term_app_bvsrem wf_bvsrem

private theorem interpret_term_app_wf_bvsmod {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvsmod ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvsmod ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_bvsmod wf_term_app_bvsmod wf_bvsmod

private theorem interpret_term_app_wf_bvumod {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvumod ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvumod ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_bvumod wf_term_app_bvumod wf_bvumod

private theorem interpret_term_app_wf_bvshl {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvshl ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvshl ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_bvshl wf_term_app_bvshl wf_bvshl

private theorem interpret_term_app_wf_bvlshr {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvlshr ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvlshr ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_bvlshr wf_term_app_bvlshr wf_bvlshr

local macro "show_interpret_term_app_wf_binary_pred" h1:ident ih:ident invert:ident wfdestruct:ident wfconstruct:ident : tactic => do
 let h2 := Lean.mkIdent `__inv__h2
 let h3 := Lean.mkIdent `__inv__h3
 let h4 := Lean.mkIdent `__inv__h4
 `(tactic| (
    simp only [InterpretTermWF];
    first
      | replace ⟨$h1:ident, _, _, _, $h2:ident, $h3:ident, $h4:ident⟩ := $wfdestruct:ident $h1:ident;
        subst $h1:ident $h2:ident -- bvops
    simp only [$invert:ident, Term.typeOf];
    simp only [WFArg] at $h3:ident $h4:ident;
    simp only [List.mem_cons, List.mem_singleton, InterpretTermWF, forall_eq_or_imp, forall_eq,
      $h3:ident, $h4:ident, List.not_mem_nil, false_implies, forall_const, and_true] at $ih:ident
    exact $wfconstruct:ident ($ih:ident).left.left ($ih:ident).right.left ($ih:ident).left.right ($ih:ident).right.right
  ))

private theorem interpret_term_app_wf_bvsaddo {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvsaddo ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvsaddo ts ty)
:= by show_interpret_term_app_wf_binary_pred h₁ ih interpret_term_app_bvsaddo wf_term_app_bvsaddo wf_bvsaddo

private theorem interpret_term_app_wf_bvssubo {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvssubo ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvssubo ts ty)
:= by show_interpret_term_app_wf_binary_pred h₁ ih interpret_term_app_bvssubo wf_term_app_bvssubo wf_bvssubo

private theorem interpret_term_app_wf_bvsmulo {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvsmulo ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvsmulo ts ty)
:= by show_interpret_term_app_wf_binary_pred h₁ ih interpret_term_app_bvsmulo wf_term_app_bvsmulo wf_bvsmulo

private theorem interpret_term_app_wf_bvslt {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvslt ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvslt ts ty)
:= by show_interpret_term_app_wf_binary_pred h₁ ih interpret_term_app_bvslt wf_term_app_bvslt wf_bvslt

private theorem interpret_term_app_wf_bvsle {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvsle ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvsle ts ty)
:= by show_interpret_term_app_wf_binary_pred h₁ ih interpret_term_app_bvsle wf_term_app_bvsle wf_bvsle

private theorem interpret_term_app_wf_bvult {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvult ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvult ts ty)
:= by show_interpret_term_app_wf_binary_pred h₁ ih interpret_term_app_bvult wf_term_app_bvult wf_bvult

private theorem interpret_term_app_wf_bvule {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .bvule ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .bvule ts ty)
:= by show_interpret_term_app_wf_binary_pred h₁ ih interpret_term_app_bvule wf_term_app_bvule wf_bvule

private theorem interpret_term_app_wf_set_subset {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .set.subset ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .set.subset ts ty)
:= by show_interpret_term_app_wf_binary_pred h₁ ih interpret_term_app_set_subset wf_term_app_set_subset wf_set_subset

private theorem interpret_term_app_wf_set_inter {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .set.inter ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .set.inter ts ty)
:= by show_interpret_term_app_wf_binary h₁ ih interpret_term_app_set_inter wf_term_app_set_inter wf_set_inter

private theorem interpret_term_app_wf_set_member {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app .set.member ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app .set.member ts ty)
:= by
  simp only [InterpretTermWF]
  replace ⟨h₁, t₁, t₂, h₂, h₃, h₄, h₅⟩ := wf_term_app_set_member h₁
  subst h₁ h₂
  simp only [interpret_term_app_set_member, Term.typeOf]
  simp [List.mem_cons, List.mem_singleton, InterpretTermWF, forall_eq_or_imp, forall_eq, h₃, h₄, h₅, List.not_mem_nil, false_implies, forall_const, and_true] at ih
  replace ⟨ih, ih'⟩ := ih
  apply wf_set_member ih.left ih'.left
  rw [ih'.right, ←h₅, ih.right, h₅]

private theorem interpret_term_app_wf_record_get {εs : SymEntities} {I : Interpretation} {ts : List Term} {a : Attr} {ty : TermType}
  (h₁ : Term.WellFormed εs (Term.app (.record.get a) ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app (.record.get a) ts ty)
:= by
  simp only [InterpretTermWF]
  replace ⟨r, h₁, t₁, h₂, _, h₃⟩ := wf_term_app_record_get h₁
  subst h₂
  simp only [interpret_term_app_record_get, Term.typeOf]
  simp only [List.mem_singleton, InterpretTermWF, forall_eq, h₃] at ih
  exact wf_record_get ih.left ih.right h₁

theorem interpret_term_app_wf {εs : SymEntities} {I : Interpretation} {op : Op} {ts : List Term} {ty : TermType}
  (h₀ : I.WellFormed εs)
  (h₁ : Term.WellFormed εs (Term.app op ts ty))
  (ih : ∀ (t : Term), t ∈ ts → InterpretTermWF εs I t) :
  InterpretTermWF εs I (Term.app op ts ty)
:= by
  match op with
  | .not               => exact interpret_term_app_wf_not h₁ ih
  | .and               => exact interpret_term_app_wf_and h₁ ih
  | .or                => exact interpret_term_app_wf_or h₁ ih
  | .eq                => exact interpret_term_app_wf_eq h₁ ih
  | .ite               => exact interpret_term_app_wf_ite h₁ ih
  | .uuf _             => exact interpret_term_app_wf_uuf h₀ h₁ ih
  | .bvneg             => exact interpret_term_app_wf_bvneg h₁ ih
  | .bvnego            => exact interpret_term_app_wf_bvnego h₁ ih
  | .bvadd             => exact interpret_term_app_wf_bvadd h₁ ih
  | .bvsub             => exact interpret_term_app_wf_bvsub h₁ ih
  | .bvmul             => exact interpret_term_app_wf_bvmul h₁ ih
  | .bvsdiv            => exact interpret_term_app_wf_bvsdiv h₁ ih
  | .bvudiv            => exact interpret_term_app_wf_bvudiv h₁ ih
  | .bvsrem            => exact interpret_term_app_wf_bvsrem h₁ ih
  | .bvsmod            => exact interpret_term_app_wf_bvsmod h₁ ih
  | .bvumod            => exact interpret_term_app_wf_bvumod h₁ ih
  | .bvshl             => exact interpret_term_app_wf_bvshl h₁ ih
  | .bvlshr            => exact interpret_term_app_wf_bvlshr h₁ ih
  | .bvsaddo           => exact interpret_term_app_wf_bvsaddo h₁ ih
  | .bvssubo           => exact interpret_term_app_wf_bvssubo h₁ ih
  | .bvsmulo           => exact interpret_term_app_wf_bvsmulo h₁ ih
  | .bvslt             => exact interpret_term_app_wf_bvslt h₁ ih
  | .bvsle             => exact interpret_term_app_wf_bvsle h₁ ih
  | .bvult             => exact interpret_term_app_wf_bvult h₁ ih
  | .bvule             => exact interpret_term_app_wf_bvule h₁ ih
  | .set.member        => exact interpret_term_app_wf_set_member h₁ ih
  | .set.subset        => exact interpret_term_app_wf_set_subset h₁ ih
  | .set.inter         => exact interpret_term_app_wf_set_inter h₁ ih
  | .zero_extend _     => exact interpret_term_app_wf_zero_extend h₁ ih
  | .option.get        => exact interpret_term_app_wf_option_get h₀ h₁ ih
  | .record.get _      => exact interpret_term_app_wf_record_get h₁ ih
  | .string.like _     => exact interpret_term_app_wf_string_like h₁ ih
  | .ext xop           =>
    match xop with
    | .decimal.val       => exact interpret_term_app_wf_ext_decimal_val h₁ ih
    | .ipaddr.isV4       => exact interpret_term_app_wf_ext_ipaddr_isV4 h₁ ih
    | .ipaddr.addrV4     => exact interpret_term_app_wf_ext_ipaddr_addrV4 h₀ h₁ ih
    | .ipaddr.prefixV4   => exact interpret_term_app_wf_ext_ipaddr_prefixV4 h₀ h₁ ih
    | .ipaddr.addrV6     => exact interpret_term_app_wf_ext_ipaddr_addrV6 h₀ h₁ ih
    | .ipaddr.prefixV6   => exact interpret_term_app_wf_ext_ipaddr_prefixV6 h₀ h₁ ih
    | .datetime.val      => exact interpret_term_app_wf_ext_datetime_val h₁ ih
    | .datetime.ofBitVec => exact interpret_term_app_wf_ext_datetime_ofBitVec h₁ ih
    | .duration.val      => exact interpret_term_app_wf_ext_duration_val h₁ ih
    | .duration.ofBitVec => exact interpret_term_app_wf_ext_duration_ofBitVec h₁ ih

theorem interpret_term_wf {εs : SymEntities} {I : Interpretation} {t : Term}
  (h₁ : I.WellFormed εs)
  (h₂ : t.WellFormed εs) :
  (t.interpret I).WellFormed εs ∧
  (t.interpret I).typeOf = t.typeOf
:= by
  match t with
  | .prim _   => exact interpret_term_prim_wf h₂
  | .var _    => exact interpret_term_var_wf h₁ h₂
  | .none _   => exact interpret_term_none_wf h₂
  | .some _   =>
    have ih := interpret_term_wf h₁ (wf_term_some_implies h₂)
    exact interpret_term_some_wf ih
  | .set s _  =>
    have ih : ∀ tᵢ, tᵢ ∈ s → InterpretTermWF εs I tᵢ := by
      intro _ h₃
      exact interpret_term_wf h₁ (wf_term_set_implies_wf_elt h₂ h₃)
    exact interpret_term_set_wf h₂ ih
  | .record r =>
    have ih : ∀ aᵢ tᵢ, (aᵢ, tᵢ) ∈ r.1 → InterpretTermWF εs I tᵢ := by
      intro _ _ h₃
      exact interpret_term_wf h₁ (wf_term_record_implies_wf_value h₂ h₃)
    exact interpret_term_record_wf h₂ ih
  | .app op ts ty =>
    have ih : ∀ tᵢ, tᵢ ∈ ts → InterpretTermWF εs I tᵢ := by
      intro _ h₃
      exact interpret_term_wf h₁ (wf_term_app_implies_wf_arg h₂ h₃)
    exact interpret_term_app_wf h₁ h₂ ih
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  · replace h₃ := Set.sizeOf_lt_of_mem h₃ ; omega
  · replace h₃ := Map.sizeOf_lt_of_value h₃ ; omega
  · replace h₃ := List.sizeOf_lt_of_mem h₃ ; omega

theorem interpret_term_isEntityType {εs : SymEntities} {I : Interpretation} {t : Term}
  (h₁ : I.WellFormed εs)
  (h₂ : t.WellFormed εs) :
  t.typeOf.isEntityType = (t.interpret I).typeOf.isEntityType
:= by simp only [interpret_term_wf h₁ h₂]

theorem interpret_term_isRecordType {εs : SymEntities} {I : Interpretation} {t : Term}
  (h₁ : I.WellFormed εs)
  (h₂ : t.WellFormed εs) :
  t.typeOf.isRecordType = (t.interpret I).typeOf.isRecordType
:= by simp only [interpret_term_wf h₁ h₂]

end Cedar.Thm
