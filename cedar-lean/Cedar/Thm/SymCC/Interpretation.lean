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

import Cedar.Thm.SymCC.Data.Basic

/-!
# Basic properties of well-formed interpretations

This file proves basic lemmas about well-formedness predicate on
interpretations.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem wf_interpretation_implies_wfl_var {εs : SymEntities} {I : Interpretation} {v : TermVar} :
  I.WellFormed εs → v.WellFormed εs → (I.vars v).WellFormedLiteral εs
:= by
  intro h₁ h₂
  exact (h₁.left v h₂).left

theorem wf_interpretation_implies_wf_var {εs : SymEntities} {I : Interpretation} {v : TermVar} :
  I.WellFormed εs → v.WellFormed εs → (I.vars v).WellFormed εs
:= by
  intro h₁ h₂
  exact (wf_interpretation_implies_wfl_var h₁ h₂).left

theorem wf_interpretation_implies_typeOf_var {εs : SymEntities} {I : Interpretation} {v : TermVar} :
  I.WellFormed εs → v.WellFormed εs → (I.vars v).typeOf = v.ty
:= by
  intro h₁ h₂
  exact (h₁.left v h₂).right

theorem wf_interpretation_implies_wf_udf {εs : SymEntities} {I : Interpretation} {f : UUF} :
  I.WellFormed εs → f.WellFormed εs →
  ((I.funs f).WellFormed εs ∧ (I.funs f).arg = f.arg ∧ (I.funs f).out = f.out)
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃, h₄⟩ := h₁.right.left f h₂
  simp only [h₁, h₃, h₄, and_self]

theorem wf_interpretation_implies_wfp_option_get {εs : SymEntities} {I : Interpretation} {t : Term} {ty : TermType} :
  I.WellFormed εs → ty.WellFormed εs → t = .app Op.option.get [.none ty] ty →
  (I.partials t).WellFormedLiteral εs ∧ (I.partials t).typeOf = ty
:= by
  intro h₁ h₂ h₃
  subst h₃
  replace h₁ := h₁.right.right (Term.app Op.option.get [Term.none ty] ty)
    (Term.WellFormedPartialApp.none_wfp h₂)
  simp only [Interpretation.WellFormed.WellFormedPartialAppInterpretation,
    Term.typeOf] at h₁
  exact h₁

theorem wf_interpretation_implies_wfp_ext_ipaddr_addrV4 {εs : SymEntities} {I : Interpretation} {t : Term}
  (v6 : Ext.IPAddr.IPv6Addr) (p6 : Ext.IPAddr.IPv6Prefix) :
  I.WellFormed εs →
  t = .app (.ext ExtOp.ipaddr.addrV4) [.prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩)))] (.bitvec 32) →
  (I.partials t).WellFormedLiteral εs ∧ (I.partials t).typeOf = (.bitvec 32)
:= by
  intro h₁ h₂
  subst h₂
  have h₂ : ¬ (Ext.IPAddr.IPNet.V6 ⟨v6, p6⟩).isV4 :=
    by simp only [Ext.IPAddr.IPNet.isV4, Bool.false_eq_true, not_false_eq_true]
  replace h₁ := h₁.right.right
    (.app (.ext ExtOp.ipaddr.addrV4) [.prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩)))] (.bitvec 32))
    (Term.WellFormedPartialApp.ext_ipddr_addr4_wfp h₂)
  simp only [Interpretation.WellFormed.WellFormedPartialAppInterpretation,
    Term.typeOf] at h₁
  exact h₁

theorem wf_interpretation_implies_wfp_ext_ipaddr_prefixV4 {εs : SymEntities} {I : Interpretation} {t : Term}
  (v6 : Ext.IPAddr.IPv6Addr) (p6 : Ext.IPAddr.IPv6Prefix) :
  I.WellFormed εs →
  t = .app (.ext ExtOp.ipaddr.prefixV4) [.prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩)))] (.option (.bitvec 5)) →
  (I.partials t).WellFormedLiteral εs ∧ (I.partials t).typeOf = (.option (.bitvec 5))
:= by
  intro h₁ h₂
  subst h₂
  have h₂ : ¬ (Ext.IPAddr.IPNet.V6 ⟨v6, p6⟩).isV4 := by
    simp only [Ext.IPAddr.IPNet.isV4, Bool.false_eq_true, not_false_eq_true]
  replace h₁ := h₁.right.right
    (.app (.ext ExtOp.ipaddr.prefixV4) [.prim (.ext (.ipaddr (.V6 ⟨v6, p6⟩)))] (.option (.bitvec 5)))
    (Term.WellFormedPartialApp.ext_ipddr_prefix4_wfp h₂)
  simp only [Interpretation.WellFormed.WellFormedPartialAppInterpretation,
    Term.typeOf] at h₁
  exact h₁

theorem wf_interpretation_implies_wfp_ext_ipaddr_addrV6 {εs : SymEntities} {I : Interpretation} {t : Term}
  (v4 : Ext.IPAddr.IPv4Addr) (p4 : Ext.IPAddr.IPv4Prefix) :
  I.WellFormed εs →
  t = .app (.ext ExtOp.ipaddr.addrV6) [.prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩)))] (.bitvec 128) →
  (I.partials t).WellFormedLiteral εs ∧ (I.partials t).typeOf = (.bitvec 128)
:= by
  intro h₁ h₂
  subst h₂
  have h₂ : ¬ (Ext.IPAddr.IPNet.V4 ⟨v4, p4⟩).isV6 := by
    simp only [Ext.IPAddr.IPNet.isV6, Bool.false_eq_true, not_false_eq_true]
  replace h₁ := h₁.right.right
    (.app (.ext ExtOp.ipaddr.addrV6) [.prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩)))] (.bitvec 128))
    (Term.WellFormedPartialApp.ext_ipddr_addr6_wfp h₂)
  simp only [Interpretation.WellFormed.WellFormedPartialAppInterpretation,
    Term.typeOf] at h₁
  exact h₁

theorem wf_interpretation_implies_wfp_ext_ipaddr_prefixV6 {εs : SymEntities} {I : Interpretation} {t : Term}
  (v4 : Ext.IPAddr.IPv4Addr) (p4 : Ext.IPAddr.IPv4Prefix) :
  I.WellFormed εs →
  t = .app (.ext ExtOp.ipaddr.prefixV6) [.prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩)))] (.option (.bitvec 7)) →
  (I.partials t).WellFormedLiteral εs ∧ (I.partials t).typeOf = (.option (.bitvec 7))
:= by
  intro h₁ h₂
  subst h₂
  have h₂ : ¬ (Ext.IPAddr.IPNet.V4 ⟨v4, p4⟩).isV6 := by
    simp only [Ext.IPAddr.IPNet.isV6, Bool.false_eq_true, not_false_eq_true]
  replace h₁ := h₁.right.right
    (.app (.ext ExtOp.ipaddr.prefixV6) [.prim (.ext (.ipaddr (.V4 ⟨v4, p4⟩)))] (.option (.bitvec 7)))
    (Term.WellFormedPartialApp.ext_ipddr_prefix6_wfp h₂)
  simp only [Interpretation.WellFormed.WellFormedPartialAppInterpretation,
    Term.typeOf] at h₁
  exact h₁

end Cedar.Thm
