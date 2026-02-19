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
import Cedar.Thm.SymCC.Interpretation
import Cedar.Thm.SymCC.Term.TypeOf

/-!
# Well-formed terms and factory functions

This file proves basic lemmas about well-formedness of terms and
Factory functions.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory BitVec

theorem wf_term_var_implies {εs : SymEntities} {v : TermVar} :
   (Term.var v).WellFormed εs → v.WellFormed εs
:= by intro h ; cases h ; assumption

theorem wf_term_some_implies {εs : SymEntities} {t : Term} :
   (Term.some t).WellFormed εs → t.WellFormed εs
:= by intro h ; cases h ; assumption

theorem wf_term_none_implies {εs : SymEntities} {ty : TermType} :
   (Term.none ty).WellFormed εs → ty.WellFormed εs
:= by intro h; cases h; assumption

theorem wf_term_set_implies_wf_elt {εs : SymEntities} {s : Set Term} {ty : TermType} {t : Term} :
  (Term.set s ty).WellFormed εs →
  t ∈ s →
  t.WellFormed εs
:= by
  intro h₁ h₂
  cases h₁ ; rename_i h₃ _ _ _
  exact h₃ t h₂

theorem wf_term_set_implies_typeOf_elt {εs : SymEntities} {s : Set Term} {ty : TermType} {t : Term} :
  (Term.set s ty).WellFormed εs →
  t ∈ s →
  t.typeOf = ty
:= by
  intro h₁ h₂
  cases h₁ ; rename_i h₃
  exact h₃ t h₂

theorem wf_term_set_implies_wf_type {εs : SymEntities} {s : Set Term} {ty : TermType} :
  (Term.set s ty).WellFormed εs →
  ty.WellFormed εs
:= by intro h₁ ; cases h₁ ; assumption

theorem wf_term_set_implies_wf_set {εs : SymEntities} {s : Set Term} {ty : TermType} :
  (Term.set s ty).WellFormed εs →
  s.WellFormed
:= by intro h₁ ; cases h₁ ; assumption

theorem wf_term_set_cons {εs : SymEntities} {hd : Term} {tl : List Term} {ty : TermType} :
  (Term.set (Set.mk (hd :: tl)) ty).WellFormed εs →
  (hd.WellFormed εs ∧ hd.typeOf = ty ∧ (Term.set (Set.mk tl) ty).WellFormed εs)
:= by
  intro h₁
  have h₂ := Set.mem_cons_self hd tl
  simp only [wf_term_set_implies_wf_elt h₁ h₂, wf_term_set_implies_typeOf_elt h₁ h₂, true_and]
  apply Term.WellFormed.set_wf
  · intro t h₃ ; exact wf_term_set_implies_wf_elt h₁ (Set.mem_cons_of_mem t hd tl h₃)
  · intro t h₃ ; exact wf_term_set_implies_typeOf_elt h₁ (Set.mem_cons_of_mem t hd tl h₃)
  · exact wf_term_set_implies_wf_type h₁
  · replace h₁ := wf_term_set_implies_wf_set h₁
    rw [Set.wf_iff_sorted, List.Sorted] at *
    exact List.tail_sortedBy h₁

theorem wf_term_record_implies {εs : SymEntities} {r : Map Attr Term} {a : Attr}
  (h₁ : Term.WellFormed εs (Term.record r))
  (h₂ : Map.find? r a = .some t) :
  Term.WellFormed εs t
:= by
  cases h₁ ; rename_i h₃ _
  exact h₃ a t (Map.find?_mem_toList h₂)

theorem wf_term_record_implies_wf_value {εs : SymEntities} {r : Map Attr Term} {a : Attr}
  (h₁ : Term.WellFormed εs (Term.record r))
  (h₂ : (a, t) ∈ r.1) :
  Term.WellFormed εs t
:= by
  cases h₁ ; rename_i h₃ _
  exact h₃ a t h₂

theorem wf_term_record_implies_wf_map {εs : SymEntities} {r : Map Attr Term}
  (h₁ : Term.WellFormed εs (Term.record r)) :
  r.WellFormed
:= by cases h₁ ; assumption

theorem wf_prods_implies_wf_map_snd {εs : SymEntities} {ats : List (Attr × Term)}
  (h₁ : ∀ (a : Attr) (t : Term), (a, t) ∈ ats → Term.WellFormed εs t) :
  ∀ t ∈ ats.map Prod.snd, t.WellFormed εs
:= by
  intro t h₂
  simp only [List.mem_map] at h₂
  replace ⟨(a, t'), h₂, h₃⟩ := h₂
  simp only at h₂ h₃
  subst h₃
  exact h₁ a t' h₂

theorem wf_prods_option_implies_wf_prods {εs : SymEntities} {ats : List (Attr × Term)} :
  (∀ a t, (a, t) ∈ ats → t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty) →
  (∀ a t, (a, t) ∈ ats → t.WellFormed εs)
:= by intro h₁ a t h₂ ; exact (h₁ a t h₂).left

theorem wf_bool {b : Bool} :
  Term.WellFormed εs (Term.prim (TermPrim.bool b))
:= by
  apply Term.WellFormed.prim_wf
  apply TermPrim.WellFormed.bool_wf

theorem wf_bv {n : Nat} {bv : BitVec n} :
  Term.WellFormed εs (Term.prim (TermPrim.bitvec bv))
:= by
  apply Term.WellFormed.prim_wf
  apply TermPrim.WellFormed.bitvec_wf

theorem wf_string {s : String} {εs : SymEntities} :
  Term.WellFormed εs (Term.prim (TermPrim.string s))
:= by
  apply Term.WellFormed.prim_wf
  apply TermPrim.WellFormed.string_wf

theorem wf_datetime {dt : Ext.Datetime} :
  Term.WellFormed ε (Term.ext (.datetime dt))
:= by
  apply Term.WellFormed.prim_wf
  apply TermPrim.WellFormed.ext_wf

theorem wf_duration {dt : Ext.Datetime.Duration} :
  Term.WellFormed ε (Term.ext (.duration dt))
:= by
  apply Term.WellFormed.prim_wf
  apply TermPrim.WellFormed.ext_wf

theorem wf_term_some {t : Term} {ty : TermType} {εs : SymEntities} :
  t.WellFormed εs → t.typeOf = ty →
  t.some.WellFormed εs ∧ t.some.typeOf = .option ty
:= by
  intro hwt hty
  simp only [Term.WellFormed.some_wf hwt, typeOf_term_some, hty, _root_.and_self]

----- Term.app wf -----

theorem wf_term_app_implies_wf_arg {εs : SymEntities} {op : Op} {ts : List Term} {ty : TermType} {t : Term} :
  (Term.app op ts ty).WellFormed εs →
  t ∈ ts →
  t.WellFormed εs
:= by
  intros h₁ h₂
  cases h₁
  rename_i h₂ _
  apply h₂ ; assumption

def WFArg (εs : SymEntities) (t : Term) (ty : TermType) : Prop :=
  t.WellFormed εs ∧ t.typeOf = ty

def WFUnary (εs : SymEntities) (ts : List Term) (ty : TermType) : Prop :=
  ∃ t, ts = [t] ∧ WFArg εs t ty

def WFBinary (εs : SymEntities) (ts : List Term) (ty : TermType) : Prop :=
  ∃ t₁ t₂, ts = [t₁, t₂] ∧ WFArg εs t₁ ty ∧ WFArg εs t₂ ty

----- Unary operators -----
/--
This tactic discharges proofs for `wf_term_app_*` lemmas that invert the
well-formedness predicate on `app` terms for unary operators.
-/
local macro "invert_wf_term_app_unary" h1:ident : tactic => do
 -- Using un-hygienic identifiers here because of a naming bug in the rename_i
 -- tactic that's making tactic-local names inaccessible. Or, rather, relying on
 -- pseudo-hygiene from the 60's by using unlikely names for local ids :))
 let h2 := Lean.mkIdent `__inv__h2
 let t  := Lean.mkIdent `__inv__t
 `(tactic| (
    cases $h1:ident;
    rename_i $h1:ident $h2:ident;
    repeat (cases $h2:ident ; rename_i $h2:ident);
    rename_i $t:ident;
    replace $h1:ident := $h1:ident $t:ident;
    simp only [List.mem_singleton, forall_const] at $h1:ident;
    simp only [true_and, WFUnary, List.cons.injEq, and_true, WFArg, exists_eq_left', $h1:ident, $h2:ident, _root_.and_self]
   ))

theorem wf_term_app_not {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .not ts ty).WellFormed εs) :
  ty = .bool ∧ WFUnary εs ts .bool
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_not_exact {εs : SymEntities} {t : Term} {ty : TermType}
  (h₁ : (Term.app .not [t] ty).WellFormed εs) :
  ty = .bool ∧ WFArg εs t .bool
:= by
  have h₂ := wf_term_app_not h₁
  simp only [WFUnary, List.cons.injEq, and_true, exists_eq_left'] at h₂
  exact h₂

theorem wf_term_app_string_like {εs : SymEntities} {ts : List Term} {ty : TermType} {p : Pattern}
  (h₁ : (Term.app (Op.string.like p) ts ty).WellFormed εs) :
  ty = .bool ∧ WFUnary εs ts .string
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_option_get {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app Op.option.get ts ty).WellFormed εs) :
  WFUnary εs ts (.option ty)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_ext_decimal_val {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app (.ext ExtOp.decimal.val) ts ty).WellFormed εs) :
  ty = (.bitvec 64) ∧ WFUnary εs ts (.ext .decimal)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_ext_ipaddr_isV4 {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app (.ext ExtOp.ipaddr.isV4) ts ty).WellFormed εs) :
  ty = .bool ∧ WFUnary εs ts (.ext .ipAddr)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_ext_ipaddr_addrV4 {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app (.ext ExtOp.ipaddr.addrV4) ts ty).WellFormed εs) :
  ty = (.bitvec 32) ∧ WFUnary εs ts (.ext .ipAddr)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_ext_ipaddr_prefixV4 {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app (.ext ExtOp.ipaddr.prefixV4) ts ty).WellFormed εs) :
  ty = (.option (.bitvec 5)) ∧ WFUnary εs ts (.ext .ipAddr)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_ext_ipaddr_addrV6 {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app (.ext ExtOp.ipaddr.addrV6) ts ty).WellFormed εs) :
  ty = (.bitvec 128) ∧ WFUnary εs ts (.ext .ipAddr)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_ext_ipaddr_prefixV6 {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app (.ext ExtOp.ipaddr.prefixV6) ts ty).WellFormed εs) :
  ty = (.option (.bitvec 7)) ∧ WFUnary εs ts (.ext .ipAddr)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_ext_datetime_val {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app (.ext ExtOp.datetime.val) ts ty).WellFormed εs) :
  ty = (.bitvec 64) ∧ WFUnary εs ts (.ext .datetime)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_ext_datetime_ofBitVec {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app (.ext ExtOp.datetime.ofBitVec) ts ty).WellFormed εs) :
  ty = (.ext .datetime) ∧ WFUnary εs ts (.bitvec 64)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_ext_duration_val {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app (.ext ExtOp.duration.val) ts ty).WellFormed εs) :
  ty = (.bitvec 64) ∧ WFUnary εs ts (.ext .duration)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_ext_duration_ofBitVec {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app (.ext ExtOp.duration.ofBitVec) ts ty).WellFormed εs) :
  ty = (.ext .duration) ∧ WFUnary εs ts (.bitvec 64)
:= by invert_wf_term_app_unary h₁

theorem wf_term_app_uuf {εs : SymEntities} {ts : List Term} {f : UUF} {ty : TermType}
  (h₁ : (Term.app (.uuf f) ts ty).WellFormed εs) :
  ty = f.out ∧ WFUnary εs ts f.arg ∧ f.WellFormed εs
:= by
  cases h₁
  rename_i h₁ h₂
  cases h₂
  rename_i t h₂ h₃
  simp only [WFUnary, List.cons.injEq, and_true, WFArg, exists_eq_left', List.mem_singleton, h₁ t,
    h₂, _root_.and_self, h₃]

theorem wf_term_app_record_get {εs : SymEntities} {ts : List Term} {a : Attr} {ty : TermType}
  (h₁ : (Term.app (Op.record.get a) ts ty).WellFormed εs) :
  ∃ rty, rty.find? a = .some ty ∧ WFUnary εs ts (.record rty)
:= by
  cases h₁
  rename_i h₁ h₂
  cases h₂
  rename_i t rty h₂ h₃
  exists rty
  simp only [h₃, WFUnary, List.cons.injEq, and_true, WFArg, exists_eq_left',
    List.mem_singleton, h₁ t, h₂, _root_.and_self]

----- Binary and ternary operators -----
/--
This tactic discharges proofs for `wf_term_app_*` lemmas that invert the
well-formedness predicate on `app` terms for binary operators.
-/
local macro "invert_wf_term_app_binary" h1:ident : tactic => do
 let h2 := Lean.mkIdent `__inv__h2
 let h3 := Lean.mkIdent `__inv__h3
 let t1 := Lean.mkIdent `__inv__t1
 let t2 := Lean.mkIdent `__inv__t2
 `(tactic| (
    cases $h1:ident
    rename_i $h1:ident $h2:ident
    cases $h2:ident
    rename_i $t1:ident $t2:ident $h2:ident $h3:ident
    simp only [true_and]
    exists $t1:ident, $t2:ident
    simp only [WFArg, List.mem_cons, List.mem_singleton,
      true_or, $h1:ident $t1:ident, $h2:ident, _root_.and_self, or_true,
      $h1:ident $t2:ident, $h3:ident]
   ))

theorem wf_term_app_and {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .and ts ty).WellFormed εs) :
  ty = .bool ∧ WFBinary εs ts .bool
:= by invert_wf_term_app_binary h₁

theorem wf_term_app_or {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .or ts ty).WellFormed εs) :
  ty = .bool ∧ WFBinary εs ts .bool
:= by invert_wf_term_app_binary h₁

theorem wf_term_app_eq {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .eq ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ ty', WFBinary εs ts ty'
:= by
  cases h₁
  rename_i h₁ h₂
  cases h₂
  rename_i t₁ t₂ h₂
  simp only [true_and]
  exists t₁.typeOf
  simp only [WFBinary, List.cons.injEq, and_true, WFArg]
  exists t₁, t₂
  simp only [_root_.and_self, List.mem_cons, true_or, h₁ t₁, h₂, or_true, h₁ t₂]

theorem wf_term_app_ite {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .ite ts ty).WellFormed εs) :
  ∃ t₁ t₂ t₃, ts = [t₁, t₂, t₃] ∧ WFArg εs t₁ .bool ∧ WFArg εs t₂ ty ∧ WFArg εs t₃ ty
:= by
  cases h₁
  rename_i h₁ h₂
  cases h₂
  rename_i t₁ t₂ t₃ h₂ h₃
  exists t₁, t₂, t₃
  simp only [WFArg, List.mem_cons, true_or,
    h₁ t₁, h₂, _root_.and_self, or_true, h₁ t₂, h₃, h₁ t₃]

theorem wf_term_app_ite_exact {εs : SymEntities} {t₁ t₂ t₃ : Term} {ty : TermType}
  (h₁ : (Term.app .ite [t₁, t₂, t₃] ty).WellFormed εs) :
  WFArg εs t₁ .bool ∧ WFArg εs t₂ ty ∧ WFArg εs t₃ ty
:= by
  have ⟨t₁', t₂', t₃', h₂⟩  := wf_term_app_ite h₁
  simp only [List.cons.injEq, and_true] at h₂
  simp only [h₂, _root_.and_self]

----- Unary operators on parametric types -----
/--
This tactic discharges proofs for `wf_term_app_*` lemmas that invert the
well-formedness predicate on `app` terms for unary operators on parametric
types.
-/
local macro "invert_wf_term_app_param_unary" h1:ident : tactic => do
 let h2 := Lean.mkIdent `__inv__h2
 let t := Lean.mkIdent `__inv__t
 let n := Lean.mkIdent `__inv__n
 `(tactic| (
    cases $h1:ident;
    rename_i $h1:ident $h2:ident;
    cases $h2:ident;
    rename_i $t:ident $n:ident $h2:ident;
    try (simp only [true_and]);
    exists $n:ident;
    simp only [WFUnary, List.cons.injEq, and_true, WFArg, exists_eq_left',
      List.mem_singleton, $h1:ident $t:ident, $h2:ident, _root_.and_self]
  ))

theorem wf_term_app_bvneg {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvneg ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFUnary εs ts ty
:= by invert_wf_term_app_param_unary h₁

theorem wf_term_app_bvnego {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvnego ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ n, WFUnary εs ts (.bitvec n)
:= by invert_wf_term_app_param_unary h₁

theorem wf_term_app_zero_extend {εs : SymEntities} {ts : List Term} {n : Nat} {ty : TermType}
  (h₁ : (Term.app (.zero_extend n) ts ty).WellFormed εs) :
  ∃ m, ty = .bitvec (n + m) ∧ WFUnary εs ts (.bitvec m)
:= by invert_wf_term_app_param_unary h₁

----- Binary operators on parametric types -----
/--
This tactic discharges proofs for `wf_term_app_*` lemmas that invert the
well-formedness predicate on `app` terms for binary operators on parametric
types.
-/
local macro "invert_wf_term_app_param_binary" h1:ident : tactic => do
 let h2 := Lean.mkIdent `__inv__h2
 let h3 := Lean.mkIdent `__inv__h3
 let t1 := Lean.mkIdent `__inv__t1
 let t2 := Lean.mkIdent `__inv__t2
 let n := Lean.mkIdent `__inv__n
 `(tactic| (
    cases $h1:ident
    rename_i $h1:ident $h2:ident
    cases $h2:ident
    rename_i $t1:ident $t2:ident $n:ident $h2:ident $h3:ident
    try (simp only [true_and])
    exists $n:ident
    simp only [WFBinary, List.cons.injEq, and_true, WFArg, true_and]
    exists $t1:ident, $t2:ident
    simp only [_root_.and_self, List.mem_cons, List.mem_singleton, true_or,
      $h1:ident $t1:ident, $h2:ident, or_true,
      $h1:ident $t2:ident, $h3:ident]
   ))

theorem wf_term_app_bvadd {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvadd ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFBinary εs ts ty
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvsub {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvsub ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFBinary εs ts ty
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvmul {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvmul ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFBinary εs ts ty
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvsdiv {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvsdiv ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFBinary εs ts ty
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvudiv {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvudiv ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFBinary εs ts ty
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvsrem {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvsrem ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFBinary εs ts ty
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvsmod {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvsmod ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFBinary εs ts ty
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvumod {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvumod ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFBinary εs ts ty
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvshl {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvshl ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFBinary εs ts ty
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvlshr {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvlshr ts ty).WellFormed εs) :
  ∃ n, ty = .bitvec n ∧ WFBinary εs ts ty
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvsaddo {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvsaddo ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ n, WFBinary εs ts (.bitvec n)
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvssubo {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvssubo ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ n, WFBinary εs ts (.bitvec n)
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvsmulo {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvsmulo ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ n, WFBinary εs ts (.bitvec n)
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvslt {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvslt ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ n, WFBinary εs ts (.bitvec n)
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvsle {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvsle ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ n, WFBinary εs ts (.bitvec n)
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvult {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvult ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ n, WFBinary εs ts (.bitvec n)
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_bvule {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app .bvule ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ n, WFBinary εs ts (.bitvec n)
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_set_subset {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app Op.set.subset ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ ty, WFBinary εs ts (.set ty)
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_set_inter {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app Op.set.inter ts ty).WellFormed εs) :
  ∃ ty', ty = (.set ty') ∧ WFBinary εs ts (.set ty')
:= by invert_wf_term_app_param_binary h₁

theorem wf_term_app_set_member {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : (Term.app Op.set.member ts ty).WellFormed εs) :
  ty = .bool ∧ ∃ t₁ t₂, ts = [t₁, t₂] ∧ t₁.WellFormed εs ∧ WFArg εs t₂ (.set t₁.typeOf)
:= by
  cases h₁
  rename_i h₁ h₂
  cases h₂
  rename_i t₁ t₂ h₂
  simp only [List.cons.injEq, and_true, true_and]
  exists t₁, t₂
  simp only [_root_.and_self, List.mem_cons, true_or,
    h₁ t₁, WFArg, or_true, h₁ t₂, h₂]

----- Factory functions preserve well-formedness -----

theorem wf_arg {εs : SymEntities} {t₁ : Term}
  (h₁ : Term.WellFormed εs t₁) :
  ∀ (t : Term), t ∈ [t₁] → Term.WellFormed εs t
:= by intros t₁ h₃; simp at h₃; subst h₃; exact h₁

theorem wf_args {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : Term.WellFormed εs t₁)
  (h₂ : Term.WellFormed εs t₂) :
  ∀ (t : Term), t ∈ [t₁, t₂] → Term.WellFormed εs t
:= by
  intros t h₃ ; simp at h₃
  cases h₃ <;> rename_i h₃ <;> subst h₃ <;> assumption

theorem wf_args_ternary {εs : SymEntities} {t₁ t₂ t₃ : Term}
  (h₁ : Term.WellFormed εs t₁)
  (h₂ : Term.WellFormed εs t₂)
  (h₃ : Term.WellFormed εs t₃) :
  ∀ (t : Term), t ∈ [t₁, t₂, t₃] → Term.WellFormed εs t
:= by
  intros t h₃ ; simp at h₃
  rcases h₃ with h₃ | h₃ | h₃ <;> subst h₃ <;> assumption

theorem wf_arg' {εs : SymEntities} {t₁ : Term}
  (h₁ : ∀ (t : Term), t ∈ [t₁] → Term.WellFormed εs t) :
  Term.WellFormed εs t₁
:= by
  simp only [List.mem_singleton, forall_eq] at h₁
  exact h₁

theorem wf_args' {εs : SymEntities} {t₁ t₂ : Term}
  (h : ∀ (t : Term), t ∈ [t₁, t₂] → Term.WellFormed εs t) :
  Term.WellFormed εs t₁ ∧ Term.WellFormed εs t₂
:= by
  simp only [List.mem_cons, forall_eq_or_imp] at h
  simp only [List.not_mem_nil, false_implies, forall_const, and_true] at h
  exact h

theorem wf_setOf {εs : SymEntities} {ts : List Term} {ty : TermType}
  (h₁ : ∀ t ∈ ts, t.WellFormed εs)
  (h₂ : ∀ t ∈ ts, t.typeOf = ty)
  (h₃ : ty.WellFormed εs) :
  (setOf ts ty).WellFormed εs ∧ (setOf ts ty).typeOf = .set ty
:= by
  simp only [setOf, Term.typeOf, and_true]
  apply Term.WellFormed.set_wf _ _ h₃ (Set.make_wf ts)
  all_goals {
    intro t hmem
    rw [← Set.make_mem] at hmem
    simp only [h₁ t hmem, h₂ t hmem]
  }

theorem wf_setOf_map {εs : SymEntities} {f : Term → Term} {ts : List Term} {ty : TermType}
  (hwf : ∀ t ∈ ts, (f t).WellFormed εs ∧ (f t).typeOf = ty)
  (hwty : ty.WellFormed εs) :
  (setOf (ts.map f) ty).WellFormed εs ∧
  (setOf (ts.map f) ty).typeOf = .set ty
:= by
  apply wf_setOf _ _ hwty
  all_goals {
    intro tₒ ht
    simp only [List.mem_map] at ht
    replace ⟨t, ht, ho⟩ := ht
    subst ho
    simp only [hwf t ht]
  }

theorem wf_some_setOf_map {εs : SymEntities} {f : Term → Term} {ts : List Term} {ty : TermType}
  (hwf : ∀ t ∈ ts, (f t).WellFormed εs ∧ (f t).typeOf = ty)
  (hwty : ty.WellFormed εs) :
  (Term.some (setOf (ts.map f) ty)).WellFormed εs ∧
  (Term.some (setOf (ts.map f) ty)).typeOf = .option (.set ty)
:= by
  have hws := wf_setOf_map hwf hwty
  simp only [typeOf_term_some, hws.right, Term.WellFormed.some_wf hws.left, _root_.and_self]

theorem wf_recordOf {εs : SymEntities} {ats : List (Attr × Term)}
  (h₁ : ∀ a t, (a, t) ∈ ats → t.WellFormed εs) :
  (recordOf ats).WellFormed εs
:= by
  simp only [recordOf]
  apply Term.WellFormed.record_wf _ (Map.make_wf ats)
  intro a t ht
  simp only [Map.toList] at ht
  replace ht := Map.make_mem_list_mem ht
  exact h₁ a t ht

theorem wf_recordOf_map {εs : SymEntities} {f : Term → Term} {ats : List (Attr × Term)}
  (hwf : ∀ a t, (a, t) ∈ ats → (f t).WellFormed εs) :
  (recordOf (ats.map (Prod.map id f))).WellFormed εs
:= by
  apply wf_recordOf
  intro a t h
  simp only [List.mem_map] at h
  replace ⟨(a', t'), hmem, h⟩ := h
  simp only [Prod.map, id_eq, Prod.mk.injEq] at h
  replace ⟨h, h'⟩ := h
  subst h h'
  exact hwf a' t' hmem

theorem wf_some_recordOf_map {εs : SymEntities} {f : Term → Term} {ats : List (Attr × Term)}
  (hwf : ∀ a t, (a, t) ∈ ats → (f t).WellFormed εs) :
  (Term.some (recordOf (ats.map (Prod.map id f)))).WellFormed εs ∧
  ∃ ty, (Term.some (recordOf (ats.map (Prod.map id f)))).typeOf = .option ty
:= by
  simp only [typeOf_term_some, TermType.option.injEq, exists_eq', and_true]
  exact Term.WellFormed.some_wf (wf_recordOf_map hwf)

theorem wf_not {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .bool) :
  (not t).WellFormed εs ∧ (not t).typeOf = .bool
:= by
  simp [Factory.not]
  split
  case h_1 =>
    simp [Term.typeOf, TermPrim.typeOf, wf_bool]
  case h_2 t' ty =>
    simp [Term.typeOf] at h₂ ; subst h₂
    cases h₁
    case app_wf h₃ h₄ =>
      constructor
      case left  => apply h₃ ; simp only [List.mem_singleton]
      case right => cases h₄ ; assumption
  case h_3 =>
    constructor
    case left  => exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.not_wt h₂)
    case right => simp [Term.typeOf]

theorem wf_eq_simplify {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = t₂.typeOf) :
  (eq.simplify t₁ t₂).WellFormed εs ∧ (eq.simplify t₁ t₂).typeOf = .bool
:= by
  fun_cases Factory.eq.simplify t₁ t₂
  <;> simp_all only [Term.prim.injEq, TermPrim.bool.injEq,
    Bool.and_eq_true, Bool.false_eq_true,
    not_false_eq_true, decide_eq_true_eq, _root_.and_self, and_true,
    typeOf_bool, wf_bool]
  · rename_i h₃ ; exact wf_not h₂ h₃.right
  · exact wf_not h₁ h₃
  · simp only [Term.typeOf, and_true]
    exact Term.WellFormed.app_wf (wf_args h₁ h₂) (Op.WellTyped.eq_wt h₃)

theorem wf_eq {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = t₂.typeOf) :
  (eq t₁ t₂).WellFormed εs ∧ (eq t₁ t₂).typeOf = .bool
:= by
  fun_cases Factory.eq t₁ t₂
  · replace h₁ := wf_term_some_implies h₁
    replace h₂ := wf_term_some_implies h₂
    simp only [Term.typeOf, TermType.option.injEq] at h₃
    exact wf_eq_simplify h₁ h₂ h₃
  · simp [wf_bool, typeOf_bool]
  · simp [wf_bool, typeOf_bool]
  · exact wf_eq_simplify h₁ h₂ h₃

theorem wf_and {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bool)
  (h₄ : t₂.typeOf = .bool) :
  (and t₁ t₂).WellFormed εs ∧ (and t₁ t₂).typeOf = .bool
:= by
  simp [Factory.and]
  split
  case isTrue => simp [h₁, h₃]
  case isFalse =>
    split
    case isTrue => simp [h₂, h₄]
    case isFalse =>
      split
      case isTrue => simp [wf_bool, typeOf_bool]
      case isFalse =>
        simp [Term.typeOf]
        exact Term.WellFormed.app_wf (wf_args h₁ h₂) (Op.WellTyped.and_wt h₃ h₄)

theorem wf_or {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bool)
  (h₄ : t₂.typeOf = .bool) :
  (or t₁ t₂).WellFormed εs ∧ (or t₁ t₂).typeOf = .bool
:= by
  simp [Factory.or]
  split
  case isTrue => simp [h₁, h₃]
  case isFalse =>
    split
    case isTrue => simp [h₂, h₄]
    case isFalse =>
      split
      case isTrue => simp [wf_bool, typeOf_bool]
      case isFalse =>
        simp [Term.typeOf]
        exact Term.WellFormed.app_wf (wf_args h₁ h₂) (Op.WellTyped.or_wt h₃ h₄)

theorem wf_ite_simplify {εs : SymEntities} {t₁ t₂ t₃ : Term}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₃.WellFormed εs)
  (h₄ : t₁.typeOf = .bool)
  (h₅ : t₂.typeOf = t₃.typeOf) :
  (ite.simplify t₁ t₂ t₃).WellFormed εs ∧ (ite.simplify t₁ t₂ t₃).typeOf = t₂.typeOf
:= by
  simp only [ite.simplify, Bool.or_eq_true, decide_eq_true_eq]
  split <;> try simp [h₂]
  split <;> try simp [h₃, h₅]
  split <;> try simp [typeOf_bool] at *
  · simp [h₁, h₄]
  · exact wf_not h₁ h₄
  · exact wf_and h₁ h₂ h₄ h₅
  · rw [eq_comm] at h₅
    rw [h₅]
    exact wf_or h₁ h₃ h₄ h₅
  · rw [← h₅]
    simp only [Term.typeOf, and_true]
    exact Term.WellFormed.app_wf (wf_args_ternary h₁ h₂ h₃) (Op.WellTyped.ite_wt h₄ h₅)

theorem wf_ite {εs : SymEntities} {t₁ t₂ t₃ : Term}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₃.WellFormed εs)
  (h₄ : t₁.typeOf = .bool)
  (h₅ : t₂.typeOf = t₃.typeOf) :
  (ite t₁ t₂ t₃).WellFormed εs ∧ (ite t₁ t₂ t₃).typeOf = t₂.typeOf
:= by
  simp only [Factory.ite]
  split
  · simp only [typeOf_term_some, TermType.option.injEq] at *
    replace h₂ := wf_term_some_implies h₂
    replace h₃ := wf_term_some_implies h₃
    have h₆ := wf_ite_simplify h₁ h₂ h₃ h₄ h₅
    exact And.intro (Term.WellFormed.some_wf h₆.left) h₆.right
  · exact wf_ite_simplify h₁ h₂ h₃ h₄ h₅

theorem wf_foldr {α} {εs : SymEntities}
  {xs : List α} {t : Term} {f : α → Term → Term}
  (h₁ : Term.WellFormed εs t)
  (h₂ : ∀ x t', x ∈ xs → t'.WellFormed εs → t'.typeOf = t.typeOf →
        ((f x t').WellFormed εs ∧ (f x t').typeOf = t.typeOf)) :
  Term.WellFormed εs (List.foldr f t xs) ∧
  Term.typeOf (List.foldr f t xs) = t.typeOf
:= by
  induction xs
  case nil => simp [h₁]
  case cons hd tl ih =>
    simp only [List.foldr_cons]
    have h₃ : Term.WellFormed εs (List.foldr f t tl) ∧ Term.typeOf (List.foldr f t tl) = Term.typeOf t := by
      apply ih
      intro x t' ha hb hc
      exact h₂ x t' (by simp [ha]) hb hc
    specialize h₂ hd (List.foldr f t tl)
    simp [h₃] at h₂
    exact h₂

theorem wf_app {εs : SymEntities} {t : Term} {f : UnaryFunction}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = f.argType)
  (h₃ : f.WellFormed εs):
  (app f t).WellFormed εs ∧ (app f t).typeOf = f.outType
:= by
  simp [Factory.app]
  split
  case h_1 =>
    simp [UnaryFunction.argType] at h₂
    simp [UnaryFunction.WellFormed] at h₃
    simp [Term.typeOf, UnaryFunction.outType]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.uuf_wt h₂ h₃)
  case h_2 =>
    simp [UnaryFunction.argType] at h₂
    simp [UnaryFunction.WellFormed] at h₃
    split
    case isTrue =>
      have ⟨h₃, h₄, _, h₆⟩ := h₃
      split <;> simp [UnaryFunction.outType]
      case h_1 t' h₇ =>
        specialize h₆ t t' (Map.find?_mem_toList h₇)
        simp [Term.WellFormedLiteral] at h₆
        simp [h₆]
      case h_2 => simp [h₃.left, h₄]
    case isFalse f _ =>
      simp [UnaryFunction.outType]
      have ⟨h₃, h₄, _, h₆⟩ := h₃
      rw [←h₄]
      apply wf_foldr h₃.left
      intro x t' h₇ h₈ h₉
      specialize h₆ x.fst x.snd h₇
      have ⟨ha, hb, hc, hd⟩ := h₆
      rw [h₄, ←hd]
      have h₁₀ := wf_eq h₁ ha.left (by simp [h₂, hb])
      apply wf_ite h₁₀.left hc.left h₈ h₁₀.right
      simp [h₉, ←hd, h₄]

theorem wf_bvneg {εs : SymEntities} {t : Term} {n : Nat}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .bitvec n) :
  (bvneg t).WellFormed εs ∧ (bvneg t).typeOf = (.bitvec n)
:= by
  simp [Factory.bvneg]
  split
  case h_1 => simp [wf_bv, typeOf_bv, typeOf_bv_width h₂]
  case h_2 =>
    simp only [Term.typeOf] at h₂
    cases h₁; rename_i h₁ h₃
    cases h₃; rename_i h₃
    simp [h₁, h₂, h₃]
  case h_3 =>
    simp [Term.typeOf, h₂]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.bvneg_wt h₂)

theorem wf_bvnego {εs : SymEntities} {t : Term} {n : Nat}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .bitvec n) :
  (bvnego t).WellFormed εs ∧ (bvnego t).typeOf = .bool
:= by
  simp [Factory.bvnego]
  split
  case h_1 => simp [wf_bool, typeOf_bool]
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.bvnego_wt h₂)

local macro "simp_wf_bv_arith" h₁:ident h₂:ident h₃:ident h₄:ident arith_fun:ident wf_thm:ident : tactic => do
 `(tactic| (
    simp only [$arith_fun:ident, Factory.bvapp]
    split
    case h_1 => simp only [ofNat_toNat, add_eq, wf_bv, typeOf_bv, typeOf_bv_width $h₃:ident, _root_.and_self]
    case h_2 =>
      simp only [$h₃:ident, Term.typeOf, and_true]
      exact Term.WellFormed.app_wf (wf_args $h₁:ident $h₂:ident) ($wf_thm:ident $h₃:ident $h₄:ident)
  ))

local macro "simp_wf_bv_arith_overflow" h₁:ident h₂:ident h₃:ident h₄:ident arith_overflow_fun:ident wf_thm:ident : tactic => do
 `(tactic| (
    simp only [$arith_overflow_fun:ident, Factory.bvso]
    split
    case h_1 => simp only [wf_bool, typeOf_bool, _root_.and_self]
    case h_2 =>
      simp only [Term.typeOf, and_true]
      exact Term.WellFormed.app_wf (wf_args $h₁:ident $h₂:ident) ($wf_thm:ident $h₃:ident $h₄:ident)
  ))

local macro "simp_wf_bv_cmp" h₁:ident h₂:ident h₃:ident h₄:ident cmp_fun:ident wf_thm:ident : tactic => do
 `(tactic| (
    simp [$cmp_fun:ident, Factory.bvcmp]
    split
    case h_1 => simp only [wf_bool, typeOf_bool, _root_.and_self]
    case h_2 =>
      simp only [Term.typeOf, and_true]
      exact Term.WellFormed.app_wf (wf_args $h₁:ident $h₂:ident) ($wf_thm:ident $h₃:ident $h₄:ident)
  ))

theorem wf_bvadd {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvadd t₁ t₂).WellFormed εs ∧ (bvadd t₁ t₂).typeOf = .bitvec n
:= by simp_wf_bv_arith h₁ h₂ h₃ h₄ Factory.bvadd Op.WellTyped.bvadd_wt

theorem wf_bvsub {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvsub t₁ t₂).WellFormed εs ∧ (bvsub t₁ t₂).typeOf = .bitvec n
:= by simp_wf_bv_arith h₁ h₂ h₃ h₄ Factory.bvsub Op.WellTyped.bvsub_wt

theorem wf_bvmul {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvmul t₁ t₂).WellFormed εs ∧ (bvmul t₁ t₂).typeOf = .bitvec n
:= by simp_wf_bv_arith h₁ h₂ h₃ h₄ Factory.bvmul Op.WellTyped.bvmul_wt

theorem wf_bvsdiv {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvsdiv t₁ t₂).WellFormed εs ∧ (bvsdiv t₁ t₂).typeOf = .bitvec n
:= by simp_wf_bv_arith h₁ h₂ h₃ h₄ Factory.bvsdiv Op.WellTyped.bvsdiv_wt

theorem wf_bvudiv {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvudiv t₁ t₂).WellFormed εs ∧ (bvudiv t₁ t₂).typeOf = .bitvec n
:= by simp_wf_bv_arith h₁ h₂ h₃ h₄ Factory.bvudiv Op.WellTyped.bvudiv_wt

theorem wf_bvsrem {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvsrem t₁ t₂).WellFormed εs ∧ (bvsrem t₁ t₂).typeOf = .bitvec n
:= by simp_wf_bv_arith h₁ h₂ h₃ h₄ Factory.bvsrem Op.WellTyped.bvsrem_wt

theorem wf_bvsmod {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvsmod t₁ t₂).WellFormed εs ∧ (bvsmod t₁ t₂).typeOf = .bitvec n
:= by simp_wf_bv_arith h₁ h₂ h₃ h₄ Factory.bvsmod Op.WellTyped.bvsmod_wt

theorem wf_bvumod {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvumod t₁ t₂).WellFormed εs ∧ (bvumod t₁ t₂).typeOf = .bitvec n
:= by simp_wf_bv_arith h₁ h₂ h₃ h₄ Factory.bvumod Op.WellTyped.bvumod_wt

theorem wf_bvshl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvshl t₁ t₂).WellFormed εs ∧ (bvshl t₁ t₂).typeOf = .bitvec n
:= by simp_wf_bv_arith h₁ h₂ h₃ h₄ Factory.bvshl Op.WellTyped.bvshl_wt

theorem wf_bvlshr {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvlshr t₁ t₂).WellFormed εs ∧ (bvlshr t₁ t₂).typeOf = .bitvec n
:= by simp_wf_bv_arith h₁ h₂ h₃ h₄ Factory.bvlshr Op.WellTyped.bvlshr_wt

theorem wf_bvsaddo {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvsaddo t₁ t₂).WellFormed εs ∧ (bvsaddo t₁ t₂).typeOf = .bool
:= by simp_wf_bv_arith_overflow h₁ h₂ h₃ h₄ Factory.bvsaddo Op.WellTyped.bvsaddo_wt

theorem wf_bvssubo {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvssubo t₁ t₂).WellFormed εs ∧ (bvssubo t₁ t₂).typeOf = .bool
:= by simp_wf_bv_arith_overflow h₁ h₂ h₃ h₄ Factory.bvssubo Op.WellTyped.bvssubo_wt

theorem wf_bvsmulo {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvsmulo t₁ t₂).WellFormed εs ∧ (bvsmulo t₁ t₂).typeOf = .bool
:= by simp_wf_bv_arith_overflow h₁ h₂ h₃ h₄ Factory.bvsmulo Op.WellTyped.bvsmulo_wt

theorem wf_bvslt {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvslt t₁ t₂).WellFormed εs ∧ (bvslt t₁ t₂).typeOf = .bool
:= by simp_wf_bv_cmp h₁ h₂ h₃ h₄ Factory.bvslt Op.WellTyped.bvslt_wt

theorem wf_bvsle {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvsle t₁ t₂).WellFormed εs ∧ (bvsle t₁ t₂).typeOf = .bool
:= by simp_wf_bv_cmp h₁ h₂ h₃ h₄ Factory.bvsle Op.WellTyped.bvsle_wt

theorem wf_bvult {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvult t₁ t₂).WellFormed εs ∧ (bvult t₁ t₂).typeOf = .bool
:= by simp_wf_bv_cmp h₁ h₂ h₃ h₄ Factory.bvult Op.WellTyped.bvult_wt

theorem wf_bvule {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvule t₁ t₂).WellFormed εs ∧ (bvule t₁ t₂).typeOf = .bool
:= by simp_wf_bv_cmp h₁ h₂ h₃ h₄ Factory.bvule Op.WellTyped.bvule_wt

theorem wf_zero_extend {εs : SymEntities} {t : Term} {n m : Nat}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .bitvec m) :
  (zero_extend n t).WellFormed εs ∧ (zero_extend n t).typeOf = (.bitvec (n + m))
:= by
  simp [Factory.zero_extend]
  split
  case h_1 => simp [wf_bv, typeOf_bv, typeOf_bv_width h₂]
  case h_2 =>
    split
    case h_1 h₃ =>
      simp [h₂] at h₃ ; subst h₃
      simp [Term.typeOf]
      exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.zero_extend_wt h₂)
    case h_2 h₃ => simp [h₂] at h₃

theorem wf_set_member {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₂.typeOf = .set t₁.typeOf) :
  (set.member t₁ t₂).WellFormed εs ∧ (set.member t₁ t₂).typeOf = .bool
:= by
  simp [Factory.set.member]
  split
  case h_1 => simp [wf_bool, typeOf_bool]
  case h_2 =>
    split
    case isTrue => simp [wf_bool, typeOf_bool]
    case isFalse =>
      simp [Term.typeOf] at * ; subst h₃
      apply Term.WellFormed.app_wf (wf_args h₁ h₂)
      apply Op.WellTyped.set.member_wt
      simp [Term.typeOf]
  case h_3 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_args h₁ h₂) (Op.WellTyped.set.member_wt h₃)

theorem wf_set_subset {εs : SymEntities} {t₁ t₂ : Term} {ty : TermType}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .set ty)
  (h₄ : t₂.typeOf = .set ty) :
  (set.subset t₁ t₂).WellFormed εs ∧ (set.subset t₁ t₂).typeOf = .bool
:= by
  simp [Factory.set.subset]
  split
  case isTrue => simp [wf_bool, typeOf_bool]
  case isFalse =>
    split
    case h_1 => simp [wf_bool, typeOf_bool]
    case h_2 =>
      split
      case isTrue => simp [wf_bool, typeOf_bool]
      case isFalse ty _ _ _ =>
        simp [Term.typeOf] at * ; subst h₃ h₄
        apply Term.WellFormed.app_wf (wf_args h₁ h₂)
        apply @Op.WellTyped.set.subset_wt _ _ _ ty <;>
        simp only [Term.typeOf]
    case h_3 =>
      simp [Term.typeOf]
      exact Term.WellFormed.app_wf (wf_args h₁ h₂) (Op.WellTyped.set.subset_wt h₃ h₄)

theorem wf_set_inter {εs : SymEntities} {t₁ t₂ : Term} {ty : TermType}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .set ty)
  (h₄ : t₂.typeOf = .set ty) :
  (set.inter t₁ t₂).WellFormed εs ∧ (set.inter t₁ t₂).typeOf = .set ty
:= by
  simp only [Factory.set.inter]
  split
  case isTrue h₅ => subst h₅; simp [h₁, h₄]
  case isFalse =>
    split
    case h_1 | h_2 =>
      simp [Term.typeOf] at *
      simp [h₁, h₂]
      assumption
    case h_3 s₁ _ s₂ _ _ _ _ =>
      split <;> simp [Term.typeOf] at *
      case isTrue =>
        subst h₃ h₄
        simp only [and_true]
        apply Term.WellFormed.set_wf
        case h₁ | h₂ =>
          intros t h₄
          have h₅ := @Set.mem_inter_iff Term _ t s₁ s₂
          simp [Inter.inter] at h₅
          rw [h₅] at h₄
          cases h₁
          first
            | { rename_i h₆ _ _ _ ; apply h₆ ; simp [h₄] }
            | { rename_i h₆ ; apply h₆ ; simp [h₄] }
        case h₃ => cases h₁ ; assumption
        case h₄ =>
          cases h₁ ; rename_i h₆ _ _ _
          cases h₂ ; rename_i h₇ _ _ _
          apply Set.inter_wf ; assumption
      case isFalse =>
        subst h₃ h₄
        simp only [and_true]
        apply Term.WellFormed.app_wf (wf_args h₁ h₂)
        apply Op.WellTyped.set.inter_wt <;>
        simp [Term.typeOf]
    case h_4 =>
      simp [Term.typeOf, h₃]
      exact Term.WellFormed.app_wf (wf_args h₁ h₂) (Op.WellTyped.set.inter_wt h₃ h₄)

theorem wf_term_set_empty {εs : SymEntities} {ty : TermType}
  (h₁ : ty.WellFormed εs) :
  Term.WellFormed εs (Term.set (Set.mk []) ty) ∧
  (Term.set (Set.mk []) ty).typeOf = .set ty
:= by
  simp only [Term.typeOf, and_true]
  have h₂ := @Set.empty_wf Term _ _
  unfold Set.empty at h₂
  apply Term.WellFormed.set_wf _ _ h₁ h₂
  all_goals {
    intro t h
    have h' := Set.empty_no_elts t
    unfold Set.empty at h'
    contradiction
  }

theorem wf_set_isEmpty {εs : SymEntities} {t₁ : Term} {ty : TermType}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₁.typeOf = .set ty):
  (set.isEmpty t₁).WellFormed εs ∧ (set.isEmpty t₁).typeOf = .bool
:= by
  simp only [set.isEmpty]
  split
  case h_1 | h_2 => exact And.intro wf_bool typeOf_bool
  case h_3 =>
    split
    case h_1 h =>
      simp [h₂] at h ; subst h
      apply wf_eq h₁
      · replace h₁ := typeOf_wf_term_is_wf h₁
        rw [h₂] at h₁
        cases h₁ ; rename_i h₁
        exact (wf_term_set_empty h₁).left
      · simp only [h₂, Term.typeOf]
    case h_2   => exact And.intro wf_bool typeOf_bool

theorem wf_set_intersects {εs : SymEntities} {t₁ t₂ : Term} {ty : TermType}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .set ty)
  (h₄ : t₂.typeOf = .set ty) :
  (set.intersects t₁ t₂).WellFormed εs ∧ (set.intersects t₁ t₂).typeOf = .bool
:= by
  simp only [set.intersects]
  have hwf := wf_set_inter h₁ h₂ h₃ h₄
  replace hwf := wf_set_isEmpty hwf.left hwf.right
  exact wf_not hwf.left hwf.right

theorem wf_record_get {εs : SymEntities} {t : Term} {rty : Map Attr TermType} {ty : TermType}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .record rty)
  (h₃ : rty.find? a = .some ty) :
  (record.get t a).WellFormed εs ∧ (record.get t a).typeOf = ty
:= by
  simp [Factory.record.get]
  split
  case h_1 r =>
    split
    case h_1 t h₄ =>
      have ⟨_, h₅, h₆⟩  := typeOf_term_record_attr_value h₂ h₃
      simp [h₄] at h₅ ; subst h₅
      simp [h₆]
      exact wf_term_record_implies h₁ h₄
    case h_2 h₄ =>
      have ⟨_, h⟩ := typeOf_term_record_attr_value h₂ h₃
      simp [h] at h₄
  case h_2 =>
    split
    case h_1 =>
      split
      case h_1 h₅ _ _ h₆ =>
        simp [h₂] at h₅ ; subst h₅
        simp [h₃] at h₆ ; subst h₆
        simp [Term.typeOf]
        apply Term.WellFormed.app_wf (wf_arg h₁)
        exact Op.WellTyped.record.get_wt h₂ h₃
      case h_2 h₄ _  h₅ =>
        simp [h₂] at h₄ ; subst h₄
        simp [h₃] at h₅
    case h_2 h₄ => simp [h₂] at h₄

theorem wf_option_get {εs : SymEntities} {t : Term} {ty : TermType}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .option ty) :
  (option.get t).WellFormed εs ∧ (option.get t).typeOf = ty
:= by
  simp [Factory.option.get]
  split
  case h_1 =>
    simp [Term.typeOf] at h₂
    simp [wf_term_some_implies h₁, h₂]
  case h_2 =>
    split
    case h_1 h₃ =>
      simp [h₂] at h₃ ; subst h₃
      simp [Term.typeOf]
      exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.option.get_wt h₂)
    case h_2 h₃ => simp [h₂] at h₃

theorem wf_option_get_mem_of_type {εs : SymEntities} {ts : List Term} {ty : TermType}
  (hwf : ∀ t ∈ ts, t.WellFormed εs)
  (hty : ∀ t ∈ ts, t.typeOf = .option ty) :
  ∀ t ∈ ts, (option.get t).WellFormed εs ∧ (option.get t).typeOf = ty
:= by
  intro t ht
  exact wf_option_get (hwf t ht) (hty t ht)

theorem wf_option_get_mem_of_type_snd {εs : SymEntities} {ats : List (Attr × Term)}
  (hwf : ∀ (a : Attr) (t : Term), (a, t) ∈ ats → Term.WellFormed εs t ∧ ∃ ty, t.typeOf = .option ty) :
  ∀ a t, (a, t) ∈ ats → (option.get t).WellFormed εs
:= by
  intro a t ht
  replace ⟨hwf, ty, hty⟩ := hwf a t ht
  simp only [wf_option_get hwf hty]

theorem wf_option_get' {εs : SymEntities} {I : Interpretation} {t : Term} {ty : TermType}
  (h₀ : I.WellFormed εs)
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .option ty) :
  (option.get' I t).WellFormed εs ∧ (option.get' I t).typeOf = ty
:= by
  simp only [option.get']
  split
  case h_1 ty' =>
    simp only [Term.typeOf, TermType.option.injEq] at h₂
    subst h₂
    have h₃ := wf_interpretation_implies_wfp_option_get h₀ (wf_term_none_implies h₁) rfl
    exact (And.intro h₃.left.left h₃.right)
  case h_2 =>
    exact wf_option_get h₁ h₂

theorem wf_string_like {εs : SymEntities} {t : Term} {p : Pattern}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .string) :
  (string.like t p).WellFormed εs ∧ (string.like t p).typeOf = .bool
:= by
  simp [Factory.string.like]
  split
  case h_1 => simp [wf_bool, typeOf_bool]
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.string.like_wt h₂)

-- TODO: Turn this proof into a tactic.
-- Currently, it's just copy / paste / replace for these lemmas.
-- The proofs differ only in the Factory op name and the ExtOp.WellTyped
-- constructor.
theorem wf_ext_decimal_val {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .decimal) :
  (ext.decimal.val t).WellFormed εs ∧ (ext.decimal.val t).typeOf = (.bitvec 64)
:= by
  simp [Factory.ext.decimal.val]
  split
  case h_1 => simp [wf_bv, typeOf_bv]
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.ext_wt (ExtOp.WellTyped.decimal.val_wt h₂))

theorem wf_ext_ipaddr_isV4 {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .ipAddr) :
  (ext.ipaddr.isV4 t).WellFormed εs ∧ (ext.ipaddr.isV4 t).typeOf = .bool
:= by
  simp [Factory.ext.ipaddr.isV4]
  split
  case h_1 => simp [wf_bool, typeOf_bool]
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.ext_wt (ExtOp.WellTyped.ipaddr.isV4_wt h₂))

theorem wf_ext_ipaddr_addrV4 {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .ipAddr) :
  (ext.ipaddr.addrV4 t).WellFormed εs ∧ (ext.ipaddr.addrV4 t).typeOf = (.bitvec 32)
:= by
  simp only [Factory.ext.ipaddr.addrV4]
  split
  case h_1 =>
    simp only [Ext.IPAddr.V4_WIDTH, Ext.IPAddr.ADDR_SIZE, wf_bv, typeOf_bv, Nat.reducePow, _root_.and_self]
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.ext_wt (ExtOp.WellTyped.ipaddr.addrV4_wt h₂))

theorem wf_ext_ipaddr_addrV4' {εs : SymEntities} {I : Interpretation} {t : Term}
  (h₀ : I.WellFormed εs)
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .ipAddr) :
  (ext.ipaddr.addrV4' I t).WellFormed εs ∧ (ext.ipaddr.addrV4' I t).typeOf = (.bitvec 32)
:= by
  simp only [ext.ipaddr.addrV4']
  split
  case h_1 t v6 p6 =>
    have h₃ := wf_interpretation_implies_wfp_ext_ipaddr_addrV4 v6 p6 h₀ rfl
    exact (And.intro h₃.left.left h₃.right)
  case h_2 =>
    exact wf_ext_ipaddr_addrV4 h₁ h₂

theorem wf_ext_ipaddr_prefixV4 {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .ipAddr) :
  (ext.ipaddr.prefixV4 t).WellFormed εs ∧ (ext.ipaddr.prefixV4 t).typeOf = (.option (.bitvec 5))
:= by
  simp only [ext.ipaddr.prefixV4]
  split
  case h_1 =>
    split <;> simp only [noneOf, someOf, Term.typeOf, TermPrim.typeOf, BitVec.width, and_true]
    · exact Term.WellFormed.none_wf TermType.WellFormed.bitvec_wf
    · exact Term.WellFormed.some_wf wf_bv
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.ext_wt (ExtOp.WellTyped.ipaddr.prefixV4_wt h₂))

theorem wf_ext_ipaddr_prefixV4' {εs : SymEntities} {I : Interpretation} {t : Term}
  (h₀ : I.WellFormed εs)
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .ipAddr) :
  (ext.ipaddr.prefixV4' I t).WellFormed εs ∧ (ext.ipaddr.prefixV4' I t).typeOf = (.option (.bitvec 5))
:= by
  simp [Factory.ext.ipaddr.prefixV4']
  split
  case h_1 t v6 p6 =>
    have h₃ := wf_interpretation_implies_wfp_ext_ipaddr_prefixV4 v6 p6 h₀ rfl
    exact (And.intro h₃.left.left h₃.right)
  case h_2 =>
    exact wf_ext_ipaddr_prefixV4 h₁ h₂

theorem wf_ext_ipaddr_addrV6 {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .ipAddr) :
  (ext.ipaddr.addrV6 t).WellFormed εs ∧ (ext.ipaddr.addrV6 t).typeOf = (.bitvec 128)
:= by
  simp [Factory.ext.ipaddr.addrV6]
  split
  case h_1 =>
    simp only [Ext.IPAddr.V6_WIDTH, Ext.IPAddr.ADDR_SIZE, wf_bv, typeOf_bv, Nat.reducePow, _root_.and_self]
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.ext_wt (ExtOp.WellTyped.ipaddr.addrV6_wt h₂))

theorem wf_ext_ipaddr_addrV6' {εs : SymEntities} {I : Interpretation} {t : Term}
  (h₀ : I.WellFormed εs)
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .ipAddr) :
  (ext.ipaddr.addrV6' I t).WellFormed εs ∧ (ext.ipaddr.addrV6' I t).typeOf = (.bitvec 128)
:= by
  simp [Factory.ext.ipaddr.addrV6']
  split
  case h_1 t v4 p4 =>
    have h₃ := wf_interpretation_implies_wfp_ext_ipaddr_addrV6 v4 p4 h₀ rfl
    exact (And.intro h₃.left.left h₃.right)
  case h_2 =>
    exact wf_ext_ipaddr_addrV6 h₁ h₂

theorem wf_ext_ipaddr_prefixV6 {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .ipAddr) :
  (ext.ipaddr.prefixV6 t).WellFormed εs ∧ (ext.ipaddr.prefixV6 t).typeOf = (.option (.bitvec 7))
:= by
  simp [Factory.ext.ipaddr.prefixV6]
  split
  case h_1 =>
    split <;> simp only [noneOf, someOf, Term.typeOf, TermPrim.typeOf, BitVec.width, and_true]
    · exact Term.WellFormed.none_wf TermType.WellFormed.bitvec_wf
    · exact Term.WellFormed.some_wf wf_bv
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.ext_wt (ExtOp.WellTyped.ipaddr.prefixV6_wt h₂))

theorem wf_ext_ipaddr_prefixV6' {εs : SymEntities} {I : Interpretation} {t : Term}
  (h₀ : I.WellFormed εs)
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .ipAddr) :
  (ext.ipaddr.prefixV6' I t).WellFormed εs ∧ (ext.ipaddr.prefixV6' I t).typeOf = (.option (.bitvec 7))
:= by
  simp [Factory.ext.ipaddr.prefixV6']
  split
  case h_1 t v4 p4 =>
    have h₃ := wf_interpretation_implies_wfp_ext_ipaddr_prefixV6 v4 p4 h₀ rfl
    exact (And.intro h₃.left.left h₃.right)
  case h_2 =>
    exact wf_ext_ipaddr_prefixV6 h₁ h₂

theorem wf_ext_datetime_val {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .datetime) :
  (ext.datetime.val t).WellFormed εs ∧ (ext.datetime.val t).typeOf = (.bitvec 64)
:= by
  simp [Factory.ext.datetime.val]
  split
  case h_1 => simp [wf_bv, typeOf_bv]
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.ext_wt (ExtOp.WellTyped.datetime.val_wt h₂))

theorem wf_ext_datetime_ofBitVec {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .prim (.bitvec 64)) :
  (ext.datetime.ofBitVec t).WellFormed εs ∧ (ext.datetime.ofBitVec t).typeOf = .ext .datetime
:= by
  simp [Factory.ext.datetime.ofBitVec]
  split
  case h_1 =>
    simp [wf_datetime, Term.typeOf, TermPrim.typeOf]
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.ext_wt (ExtOp.WellTyped.datetime.ofBitVec_wt h₂))

theorem wf_ext_duration_val {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .ext .duration) :
  (ext.duration.val t).WellFormed εs ∧ (ext.duration.val t).typeOf = (.bitvec 64)
:= by
  simp [Factory.ext.duration.val]
  split
  case h_1 => simp [wf_bv, typeOf_bv]
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.ext_wt (ExtOp.WellTyped.duration.val_wt h₂))

theorem wf_ext_duration_ofBitVec {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs)
  (h₂ : t.typeOf = .prim (.bitvec 64)) :
  (ext.duration.ofBitVec t).WellFormed εs ∧ (ext.duration.ofBitVec t).typeOf = .ext .duration
:= by
  simp [Factory.ext.duration.ofBitVec]
  split
  case h_1 =>
    simp [wf_duration, Term.typeOf, TermPrim.typeOf]
  case h_2 =>
    simp [Term.typeOf]
    exact Term.WellFormed.app_wf (wf_arg h₁) (Op.WellTyped.ext_wt (ExtOp.WellTyped.duration.ofBitVec_wt h₂))

theorem wf_isNone {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs) :
  (isNone t).WellFormed εs ∧ (isNone t).typeOf = .bool
:= by
  simp only [isNone]
  split
  case h_1 | h_2 | h_3 =>
    simp [wf_bool, typeOf_bool]
  case h_4 =>
    replace ⟨h₁, h₂⟩ := (wf_term_app_ite_exact h₁).left
    exact wf_not h₁ h₂
  case h_5 =>
    exact (wf_term_app_ite_exact h₁).left
  case h_6 =>
    split
    case h_1 ty heq =>
      have hty := typeOf_wf_term_is_wf h₁
      simp only [heq] at hty
      cases hty ; rename_i hty
      exact wf_eq h₁ (Term.WellFormed.none_wf hty) (by simp only [Term.typeOf, heq])
    case h_2 =>
      simp [wf_bool, typeOf_bool]

theorem wf_isSome {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs) :
  (isSome t).WellFormed εs ∧ (isSome t).typeOf = .bool
:= by
  simp only [isSome]
  have h₂ := wf_isNone h₁
  exact wf_not h₂.left h₂.right

theorem wf_ifSome_option {εs : SymEntities} {g t : Term} {ty : TermType} :
  g.WellFormed εs →
  t.WellFormed εs →
  t.typeOf = .option ty →
  (ifSome g t).WellFormed εs ∧ (ifSome g t).typeOf = .option ty
:= by
  intro h₁ h₂ h₃
  have h₄ := wf_isNone h₁
  have h₅ := typeOf_wf_term_is_wf h₂
  simp only [ifSome, h₃, noneOf]
  have ht : TermType.option ty = (Term.none ty).typeOf := by simp only [Term.typeOf]
  rw [ht]
  rw [h₃, ht] at h₅
  simp only [Term.typeOf] at h₅
  cases h₅ ; rename_i h₅
  apply wf_ite h₄.left (Term.WellFormed.none_wf h₅) h₂ h₄.right
  simp only [← ht, h₃]

theorem wf_ifFalse {εs : SymEntities} {g t : Term} :
  g.WellFormed εs →
  t.WellFormed εs →
  g.typeOf = .bool →
  (ifFalse g t).WellFormed εs ∧ (ifFalse g t).typeOf = .option t.typeOf
:= by
  intro h₁ h₂ h₃
  simp only [ifFalse, noneOf, someOf]
  have h₄ := wf_ite h₁
    (Term.WellFormed.none_wf (typeOf_wf_term_is_wf h₂))
    (Term.WellFormed.some_wf h₂) h₃ (by simp only [Term.typeOf])
  simp only [h₄, Term.typeOf, _root_.and_self]

theorem wf_ifTrue {εs : SymEntities} {g t : Term} :
  g.WellFormed εs →
  t.WellFormed εs →
  g.typeOf = .bool →
  (ifTrue g t).WellFormed εs ∧ (ifTrue g t).typeOf = .option t.typeOf
:= by
  intro h₁ h₂ h₃
  simp only [ifTrue, noneOf, someOf]
  have h₄ := wf_ite h₁
    (Term.WellFormed.some_wf h₂)
    (Term.WellFormed.none_wf (typeOf_wf_term_is_wf h₂))
    h₃ (by simp only [Term.typeOf])
  simp only [h₄, Term.typeOf, _root_.and_self]

theorem wf_foldl {α} {εs : SymEntities}
  {xs : List α} {t : Term} {f : Term → α → Term}
  (h₁ : Term.WellFormed εs t)
  (h₂ : ∀ x t', x ∈ xs → t'.WellFormed εs → t'.typeOf = t.typeOf →
        ((f t' x).WellFormed εs ∧ (f t' x).typeOf = t.typeOf)) :
  Term.WellFormed εs (List.foldl f t xs) ∧
  Term.typeOf (List.foldl f t xs) = t.typeOf
:= by
  induction xs generalizing t
  case nil => simp only [List.foldl_nil, h₁, _root_.and_self]
  case cons hd tl ih =>
    simp only [List.foldl_cons]
    have h₃ := h₂ hd t List.mem_cons_self h₁ rfl
    specialize @ih (f t hd) h₃.left
    rw [h₃.right] at ih
    apply ih
    intro t' t'' h₄ h₅ h₆
    exact h₂ _ _ (by simp only [List.mem_cons, h₄, or_true]) h₅ h₆


theorem wf_anyTrue {εs : SymEntities} {f : Term → Term} {ts : List Term} :
  (∀ t ∈ ts, (f t).WellFormed εs ∧ (f t).typeOf = .bool) →
  (anyTrue f ts).WellFormed εs ∧ (anyTrue f ts).typeOf = .bool
:= by
  intro hwf
  simp only [anyTrue]
  rw [← @typeOf_bool false]
  apply wf_foldl wf_bool
  intro t t' hin hw' hty'
  simp only [typeOf_bool] at *
  specialize hwf t hin
  exact wf_or hwf.left hw' hwf.right hty'

theorem wf_anyNone {εs : SymEntities} {gs : List Term} :
  (∀ g ∈ gs, g.WellFormed εs) →
  (anyNone gs).WellFormed εs ∧ (anyNone gs).typeOf = .bool
:= by
  intro hwf
  apply wf_anyTrue
  intro t hin
  specialize hwf t hin
  exact wf_isNone hwf

theorem wf_ifAllSome {εs : SymEntities} {gs : List Term} {t : Term} {ty : TermType} :
  (∀ g ∈ gs, g.WellFormed εs) →
  t.WellFormed εs →
  t.typeOf = .option ty →
  (ifAllSome gs t).WellFormed εs ∧ (ifAllSome gs t).typeOf = .option ty
:= by
  intro h₁ h₂ h₃
  simp only [ifAllSome, h₃, noneOf]
  have h₄ := @typeOf_term_none ty
  simp only [← h₄]
  have h₅ := wf_anyNone h₁
  have h₆ := typeOf_wf_term_is_wf h₂
  rw [h₃] at h₆ ; cases h₆ ; rename_i h₆
  exact wf_ite h₅.left (Term.WellFormed.none_wf h₆) h₂ h₅.right (by simp only [h₄, h₃])

theorem wf_bvaddChecked {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvaddChecked t₁ t₂).WellFormed εs ∧ (bvaddChecked t₁ t₂).typeOf = .option (.bitvec n)
:= by
  have ⟨h₅, h₆⟩ := wf_bvsaddo h₁ h₂ h₃ h₄
  have ⟨h₇, h₈⟩ := wf_bvadd h₁ h₂ h₃ h₄
  simp only [bvaddChecked, wf_ifFalse h₅ h₇ h₆, h₈, and_true]

theorem wf_bvsubChecked {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvsubChecked t₁ t₂).WellFormed εs ∧ (bvsubChecked t₁ t₂).typeOf = .option (.bitvec n)
:= by
  have ⟨h₅, h₆⟩ := wf_bvssubo h₁ h₂ h₃ h₄
  have ⟨h₇, h₈⟩ := wf_bvsub h₁ h₂ h₃ h₄
  simp only [bvsubChecked, wf_ifFalse h₅ h₇ h₆, h₈, and_true]

theorem wf_bvmulChecked {εs : SymEntities} {t₁ t₂ : Term} {n : Nat}
  (h₁ : t₁.WellFormed εs)
  (h₂ : t₂.WellFormed εs)
  (h₃ : t₁.typeOf = .bitvec n)
  (h₄ : t₂.typeOf = .bitvec n) :
  (bvmulChecked t₁ t₂).WellFormed εs ∧ (bvmulChecked t₁ t₂).typeOf = .option (.bitvec n)
:= by
  have ⟨h₅, h₆⟩ := wf_bvsmulo h₁ h₂ h₃ h₄
  have ⟨h₇, h₈⟩ := wf_bvmul h₁ h₂ h₃ h₄
  simp only [bvmulChecked, wf_ifFalse h₅ h₇ h₆, h₈, and_true]

local macro "simp_wf_decimal_cmp" h₁:ident h₂:ident cmp_fun:ident wf_thm:ident : tactic => do
 `(tactic| (
    simp only [$cmp_fun:ident]
    have h₁ := wf_ext_decimal_val ($h₁:ident).left ($h₁:ident).right
    have h₂ := wf_ext_decimal_val ($h₂:ident).left ($h₂:ident).right
    exact $wf_thm h₁.left h₂.left h₁.right h₂.right
  ))

theorem wf_decimal_lessThan {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs ∧ t₁.typeOf = .ext .decimal)
  (h₂ : t₂.WellFormed εs ∧ t₂.typeOf = .ext .decimal) :
  (Decimal.lessThan t₁ t₂).WellFormed εs ∧ (Decimal.lessThan t₁ t₂).typeOf = .bool
:= by simp_wf_decimal_cmp h₁ h₂ Decimal.lessThan wf_bvslt

theorem wf_decimal_lessThanOrEqual {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs ∧ t₁.typeOf = .ext .decimal)
  (h₂ : t₂.WellFormed εs ∧ t₂.typeOf = .ext .decimal) :
  (Decimal.lessThanOrEqual t₁ t₂).WellFormed εs ∧ (Decimal.lessThanOrEqual t₁ t₂).typeOf = .bool
:= by simp_wf_decimal_cmp h₁ h₂ Decimal.lessThanOrEqual wf_bvsle

theorem wf_decimal_greaterThan {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs ∧ t₁.typeOf = .ext .decimal)
  (h₂ : t₂.WellFormed εs ∧ t₂.typeOf = .ext .decimal) :
  (Decimal.greaterThan t₁ t₂).WellFormed εs ∧ (Decimal.greaterThan t₁ t₂).typeOf = .bool
:= by
  unfold Decimal.greaterThan
  exact wf_decimal_lessThan h₂ h₁

theorem wf_decimal_greaterThanOrEqual {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs ∧ t₁.typeOf = .ext .decimal)
  (h₂ : t₂.WellFormed εs ∧ t₂.typeOf = .ext .decimal) :
  (Decimal.greaterThanOrEqual t₁ t₂).WellFormed εs ∧ (Decimal.greaterThanOrEqual t₁ t₂).typeOf = .bool
:= by
  unfold Decimal.greaterThanOrEqual
  exact wf_decimal_lessThanOrEqual h₂ h₁

theorem wf_ipaddr_isIpv4 {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  (IPAddr.isIpv4 t).WellFormed εs ∧ (IPAddr.isIpv4 t).typeOf = .bool
:= by
  unfold IPAddr.isIpv4
  exact wf_ext_ipaddr_isV4 h₁.left h₁.right

theorem wf_ipaddr_isIpv6 {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  (IPAddr.isIpv6 t).WellFormed εs ∧ (IPAddr.isIpv6 t).typeOf = .bool
:= by
  unfold IPAddr.isIpv6
  have h₂ := wf_ipaddr_isIpv4 h₁
  exact wf_not h₂.left h₂.right

theorem wf_ipaddr_subnetWidth {εs : SymEntities} {w : Nat} {ipPre : Term}
  (h₁ : ipPre.WellFormed εs ∧ ipPre.typeOf = .option (.bitvec w)) :
  (IPAddr.subnetWidth w ipPre).WellFormed εs ∧
  (IPAddr.subnetWidth w ipPre).typeOf = .bitvec (Ext.IPAddr.ADDR_SIZE w)
:= by
  simp only [IPAddr.subnetWidth]
  generalize hw : (Ext.IPAddr.ADDR_SIZE w) = n
  simp only [Ext.IPAddr.ADDR_SIZE] at hw
  have h₂ := wf_isNone h₁.left
  have h₃ := wf_option_get h₁.left h₁.right
  have h₄ := @wf_zero_extend _ _ (n - w) _ h₃.left h₃.right
  have _ : w < n := by
    rw [← hw]
    exact Nat.lt_two_pow_self
  have hn : n - w + w = n := by omega
  rw [hn] at h₄
  have h₅ := @wf_bv εs n (BitVec.ofNat n 0)
  have h₆ := @typeOf_bv _ (BitVec.ofNat n 0)
  rw [← h₆]
  have h₇ := wf_bvsub (@wf_bv εs _ (BitVec.ofNat n n)) h₄.left typeOf_bv h₄.right
  apply wf_ite h₂.left h₅ h₇.left h₂.right
  simp only [h₆, h₇.right]

def WFIPRange (εs : SymEntities) (p : Term × Term) (w : Nat) : Prop :=
  WFArg εs p.1 (.bitvec w) ∧ WFArg εs p.2 (.bitvec w)

theorem wf_ipaddr_range {εs : SymEntities} {w : Nat} {ipAddr ipPre : Term}
  (h₁ : ipAddr.WellFormed εs ∧ ipAddr.typeOf = .bitvec (Ext.IPAddr.ADDR_SIZE w))
  (h₂ : ipPre.WellFormed εs ∧ ipPre.typeOf = .option (.bitvec w)) :
  WFIPRange εs (IPAddr.range w ipAddr ipPre) (Ext.IPAddr.ADDR_SIZE w)
:= by
  simp only [IPAddr.range]
  generalize hsw : IPAddr.subnetWidth w ipPre = sw
  generalize hlo : bvshl (bvlshr ipAddr sw) sw = lo
  generalize htw : Term.prim (TermPrim.bitvec 1#(Ext.IPAddr.ADDR_SIZE w)) = tw
  generalize hhi : bvsub (bvadd lo (bvshl tw sw)) tw = hi
  have hwf_sw := wf_ipaddr_subnetWidth h₂
  rw [hsw] at hwf_sw
  have hwf_lo := wf_bvlshr h₁.left hwf_sw.left h₁.right hwf_sw.right
  replace hwf_lo := wf_bvshl hwf_lo.left hwf_sw.left hwf_lo.right hwf_sw.right
  rw [hlo] at hwf_lo
  have hwf_tw := @wf_bv εs _ 1#(Ext.IPAddr.ADDR_SIZE w)
  have hty_tw := @typeOf_bv _ 1#(Ext.IPAddr.ADDR_SIZE w)
  have hwf_hi := wf_bvshl hwf_tw hwf_sw.left hty_tw hwf_sw.right
  replace hwf_hi := wf_bvadd hwf_lo.left hwf_hi.left hwf_lo.right hwf_hi.right
  replace hwf_hi := wf_bvsub hwf_hi.left hwf_tw hwf_hi.right hty_tw
  rw [htw, hhi] at hwf_hi
  simp only [WFIPRange, WFArg, hwf_lo, hwf_hi, _root_.and_self]

theorem ipaddr_addr_size_v4_eq : Ext.IPAddr.ADDR_SIZE Ext.IPAddr.V4_WIDTH = 32 := by decide
theorem ipaddr_addr_size_v6_eq : Ext.IPAddr.ADDR_SIZE Ext.IPAddr.V6_WIDTH = 128 := by decide

theorem wf_ipaddr_rangeV4 {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  WFIPRange εs (IPAddr.rangeV4 t) (Ext.IPAddr.ADDR_SIZE Ext.IPAddr.V4_WIDTH)
:= by
  unfold IPAddr.rangeV4
  have h₂ := wf_ext_ipaddr_addrV4 h₁.left h₁.right
  have h₃ := wf_ext_ipaddr_prefixV4 h₁.left h₁.right
  rw [← ipaddr_addr_size_v4_eq] at h₂
  exact wf_ipaddr_range h₂ h₃

theorem wf_ipaddr_rangeV6 {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  WFIPRange εs (IPAddr.rangeV6 t) (Ext.IPAddr.ADDR_SIZE Ext.IPAddr.V6_WIDTH)
:= by
  unfold IPAddr.rangeV6
  have h₂ := wf_ext_ipaddr_addrV6 h₁.left h₁.right
  have h₃ := wf_ext_ipaddr_prefixV6 h₁.left h₁.right
  rw [← ipaddr_addr_size_v6_eq] at h₂
  exact wf_ipaddr_range h₂ h₃

theorem wf_ipaddr_inRange {εs : SymEntities} {w : Nat} {range : Term → Term × Term} {t₁ t₂ : Term}
  (h₁ : WFIPRange εs (range t₁) w)
  (h₂ : WFIPRange εs (range t₂) w) :
  (IPAddr.inRange range t₁ t₂).WellFormed εs ∧ (IPAddr.inRange range t₁ t₂).typeOf = .bool
:= by
  simp only [IPAddr.inRange]
  simp only [WFIPRange, WFArg] at h₁ h₂
  have h₃ := wf_bvule h₁.right.left h₂.right.left h₁.right.right h₂.right.right
  have h₄ := wf_bvule h₂.left.left h₁.left.left h₂.left.right h₁.left.right
  exact wf_and h₃.left h₄.left h₃.right h₄.right

theorem wf_ipaddr_inRangeV {εs : SymEntities} {w : Nat} {isIp : Term → Term} {rangeV : Term → Term × Term} {t₁ t₂ : Term}
  (h₁ : WFIPRange εs (rangeV t₁) w)
  (h₂ : WFIPRange εs (rangeV t₂) w)
  (h₃ : (isIp t₁).WellFormed εs ∧ (isIp t₁).typeOf = .bool)
  (h₄ : (isIp t₂).WellFormed εs ∧ (isIp t₂).typeOf = .bool) :
  (IPAddr.inRangeV isIp rangeV t₁ t₂).WellFormed εs ∧
  (IPAddr.inRangeV isIp rangeV t₁ t₂).typeOf = .bool
:= by
  simp only [IPAddr.inRangeV]
  have h₅ := wf_and h₃.left h₄.left h₃.right h₄.right
  have h₆ := wf_ipaddr_inRange h₁ h₂
  exact wf_and h₅.left h₆.left h₅.right h₆.right

theorem wf_ipaddr_isInRange {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs ∧ t₁.typeOf = .ext .ipAddr)
  (h₂ : t₂.WellFormed εs ∧ t₂.typeOf = .ext .ipAddr) :
  (IPAddr.isInRange t₁ t₂).WellFormed εs ∧ (IPAddr.isInRange t₁ t₂).typeOf = .bool
:= by
  simp only [IPAddr.isInRange]
  have h₃ := wf_ipaddr_inRangeV (wf_ipaddr_rangeV4 h₁) (wf_ipaddr_rangeV4 h₂) (wf_ipaddr_isIpv4 h₁) (wf_ipaddr_isIpv4 h₂)
  have h₄ := wf_ipaddr_inRangeV (wf_ipaddr_rangeV6 h₁) (wf_ipaddr_rangeV6 h₂) (wf_ipaddr_isIpv6 h₁) (wf_ipaddr_isIpv6 h₂)
  exact wf_or h₃.left h₄.left h₃.right h₄.right

theorem wf_ipaddr_ipTerm (εs : SymEntities) (ip : IPAddr) :
  (IPAddr.ipTerm ip).WellFormed εs ∧ (IPAddr.ipTerm ip).typeOf = .ext .ipAddr
:= by
  simp only [IPAddr.ipTerm, Term.WellFormed.prim_wf TermPrim.WellFormed.ext_wf,
    typeOf_term_prim_ext_ipaddr, _root_.and_self]

theorem wf_ipaddr_inRangeLit {εs : SymEntities} {t : Term} {cidr₄ : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} {cidr₆ : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  (IPAddr.inRangeLit t cidr₄ cidr₆).WellFormed εs ∧ (IPAddr.inRangeLit t cidr₄ cidr₆).typeOf = .bool
:= by
  have h₂ := wf_ipaddr_isIpv4 h₁
  have h₃ := wf_ipaddr_inRange (wf_ipaddr_rangeV4 h₁)
    (wf_ipaddr_rangeV4 (wf_ipaddr_ipTerm εs (Ext.IPAddr.IPNet.V4 cidr₄)))
  have h₄ := wf_ipaddr_inRange (wf_ipaddr_rangeV6 h₁)
    (wf_ipaddr_rangeV6 (wf_ipaddr_ipTerm εs (Ext.IPAddr.IPNet.V6 cidr₆)))
  rw [← h₃.right]
  exact wf_ite h₂.left h₃.left h₄.left h₂.right (by simp only [h₃.right, h₄.right])

theorem wf_ipaddr_isLoopback {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  (IPAddr.isLoopback t).WellFormed εs ∧ (IPAddr.isLoopback t).typeOf = .bool
:= by
  simp only [IPAddr.isLoopback, wf_ipaddr_inRangeLit h₁, _root_.and_self]

theorem wf_ipaddr_isMulticast {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  (IPAddr.isMulticast t).WellFormed εs ∧ (IPAddr.isMulticast t).typeOf = .bool
:= by
  simp only [IPAddr.isMulticast, wf_ipaddr_inRangeLit h₁, _root_.and_self]

theorem wf_datetime_offset {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs ∧ t₁.typeOf = .ext .datetime)
  (h₂ : t₂.WellFormed εs ∧ t₂.typeOf = .ext .duration) :
  (Datetime.offset t₁ t₂).WellFormed εs ∧ (Datetime.offset t₁ t₂).typeOf = .option (.ext .datetime)
:= by
  have ⟨hwf₁, hty₁⟩ := wf_ext_datetime_val h₁.left h₁.right
  have ⟨hwf₂, hty₂⟩ := wf_ext_duration_val h₂.left h₂.right
  have ⟨hwf₃, hty₃⟩ := wf_bvadd hwf₁ hwf₂ hty₁ hty₂
  have ⟨hwf₄, hty₄⟩ := wf_ext_datetime_ofBitVec hwf₃ hty₃
  have ⟨hwf₅, hty₅⟩ := wf_bvsaddo hwf₁ hwf₂ hty₁ hty₂
  simp only [Datetime.offset, wf_ifFalse hwf₅ hwf₄ hty₅, hty₄, _root_.and_self]

theorem wf_datetime_durationSince {εs : SymEntities} {t₁ t₂ : Term}
  (h₁ : t₁.WellFormed εs ∧ t₁.typeOf = .ext .datetime)
  (h₂ : t₂.WellFormed εs ∧ t₂.typeOf = .ext .datetime) :
  (Datetime.durationSince t₁ t₂).WellFormed εs ∧ (Datetime.durationSince t₁ t₂).typeOf = .option (.ext .duration)
:= by
  have ⟨hwf₁, hty₁⟩ := wf_ext_datetime_val h₁.left h₁.right
  have ⟨hwf₂, hty₂⟩ := wf_ext_datetime_val h₂.left h₂.right
  have ⟨hwf₃, hty₃⟩ := wf_bvsub hwf₁ hwf₂ hty₁ hty₂
  have ⟨hwf₄, hty₄⟩ := wf_ext_duration_ofBitVec hwf₃ hty₃
  have ⟨hwf₅, hty₅⟩ := wf_bvssubo hwf₁ hwf₂ hty₁ hty₂
  simp only [Datetime.durationSince, wf_ifFalse hwf₅ hwf₄ hty₅, hty₄, _root_.and_self]

theorem wf_datetime_toDate {εs : SymEntities} {t : Term}
  (h : t.WellFormed εs ∧ t.typeOf = .ext .datetime) :
  (Datetime.toDate t).WellFormed εs ∧ (Datetime.toDate t).typeOf = .option (.ext .datetime)
:= by
  have ⟨hwf₀, hty₀⟩ := wf_ext_datetime_val h.left h.right
  have hwf_bv_zero := @wf_bv εs _ (Int64.toBitVec 0)
  have hwf_bv_ms_per_day := @wf_bv εs _ (Int64.toBitVec 86400000)
  have ⟨hwf₁, hty₁⟩   := wf_bvsle hwf_bv_zero hwf₀ typeOf_bv hty₀
  have ⟨hwf₂, hty₂⟩   := wf_bvsdiv hwf₀ hwf_bv_ms_per_day hty₀ typeOf_bv
  have ⟨hwf₃, hty₃⟩   := wf_bvmul hwf_bv_ms_per_day hwf₂ typeOf_bv hty₂
  have ⟨hwf₄, hty₄⟩   := wf_ext_datetime_ofBitVec hwf₃ hty₃
  have ⟨hwf₅, hty₅⟩   := wf_term_some hwf₄ hty₄
  have ⟨hwf₆, hty₆⟩   := wf_bvsrem hwf₀ hwf_bv_ms_per_day hty₀ typeOf_bv
  have ⟨hwf₇, hty₇⟩   := wf_eq hwf₆ hwf_bv_zero (by simp only [hty₆, typeOf_bv])
  have ⟨hwf₈, hty₈⟩   := wf_term_some h.left h.right
  have ⟨hwf₉, hty₉⟩   := wf_bvsub hwf₂ (@wf_bv εs _ (Int64.toBitVec 1)) hty₂ typeOf_bv
  have ⟨hwf₁₀, hty₁₀⟩ := wf_bvsmulo hwf₉ hwf_bv_ms_per_day hty₉ typeOf_bv
  have ⟨hwf₁₁, hty₁₁⟩ := wf_bvmul hwf₉ hwf_bv_ms_per_day hty₉ typeOf_bv
  have ⟨hwf₁₂, hty₁₂⟩ := wf_ext_datetime_ofBitVec hwf₁₁ hty₁₁
  have ⟨hwf₁₃, hty₁₃⟩ := wf_ifFalse hwf₁₀ hwf₁₂ hty₁₀
  have ⟨hwf₁₄, hty₁₄⟩ := wf_ite hwf₇ hwf₈ hwf₁₃ hty₇ (by simp only [hty₈, hty₁₃, hty₁₂])
  have ⟨hwf₁₅, hty₁₅⟩ := wf_ite hwf₁ hwf₅ hwf₁₄ hty₁ (by simp only [hty₅, hty₁₄, hty₈])
  simp only [Datetime.toDate, someOf, hwf₁₅, hty₁₅, hty₅, _root_.and_self]

theorem wf_datetime_toTime {εs : SymEntities} {t : Term}
  (h : t.WellFormed εs ∧ t.typeOf = .ext .datetime) :
  (Datetime.toTime t).WellFormed εs ∧ (Datetime.toTime t).typeOf = .ext .duration
:= by
  have ⟨hwf₀, hty₀⟩ := wf_ext_datetime_val h.left h.right
  have hwf_bv_zero := @wf_bv εs _ (Int64.toBitVec 0)
  have hwf_bv_ms_per_day := @wf_bv εs _ (Int64.toBitVec 86400000)
  have ⟨hwf₁, hty₁⟩ := wf_bvsle hwf_bv_zero hwf₀ typeOf_bv hty₀
  have ⟨hwf₂, hty₂⟩ := wf_bvsrem hwf₀ hwf_bv_ms_per_day hty₀ typeOf_bv
  have ⟨hwf₃, hty₃⟩ := wf_eq hwf₂ hwf_bv_zero (by simp only [hty₂, typeOf_bv])
  have ⟨hwf₄, hty₄⟩ := wf_bvadd hwf₂ hwf_bv_ms_per_day hty₂ typeOf_bv
  have ⟨hwf₅, hty₅⟩ := wf_ite hwf₃ hwf_bv_zero hwf₄ hty₃ (by simp only [typeOf_bv, hty₄])
  have ⟨hwf₆, hty₆⟩ := wf_ite hwf₁ hwf₂ hwf₅ hty₁ (by simp only [hty₂, hty₅, typeOf_bv])
  simp only [Datetime.toTime, wf_ext_duration_ofBitVec hwf₆ (by simp only [hty₆, hty₂]), _root_.and_self]

local macro "show_wf_duration_conversion" cfun:ident wf_thm:ident hwf:ident : tactic => do
 `(tactic| (
    unfold $cfun
    replace $hwf := $wf_thm $hwf
    exact wf_bvsdiv ($hwf).left wf_bv ($hwf).right typeOf_bv
   ))

theorem wf_duration_toMilliseconds {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .duration) :
  (Duration.toMilliseconds t).WellFormed εs ∧ (Duration.toMilliseconds t).typeOf = .bitvec 64
:= by
  unfold Duration.toMilliseconds
  exact wf_ext_duration_val h₁.left h₁.right

theorem wf_duration_toSeconds {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .duration) :
  (Duration.toSeconds t).WellFormed εs ∧ (Duration.toSeconds t).typeOf = .bitvec 64
:= by show_wf_duration_conversion Duration.toSeconds wf_duration_toMilliseconds h₁

theorem wf_duration_toMinutes {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .duration) :
  (Duration.toMinutes t).WellFormed εs ∧ (Duration.toMinutes t).typeOf = .bitvec 64
:= by show_wf_duration_conversion Duration.toMinutes wf_duration_toSeconds h₁

theorem wf_duration_toHours {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .duration) :
  (Duration.toHours t).WellFormed εs ∧ (Duration.toHours t).typeOf = .bitvec 64
:= by show_wf_duration_conversion Duration.toHours wf_duration_toMinutes h₁

theorem wf_duration_toDays {εs : SymEntities} {t : Term}
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .duration) :
  (Duration.toDays t).WellFormed εs ∧ (Duration.toDays t).typeOf = .bitvec 64
:= by show_wf_duration_conversion Duration.toDays wf_duration_toHours h₁

theorem wf_tags_hasTag {εs : SymEntities} {τs : SymTags} {t₁ t₂ : Term} {ety : EntityType}
  (hwτ : τs.WellFormed εs ety)
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty₁ : t₁.typeOf = TermType.entity ety)
  (hty₂ : t₂.typeOf = TermType.string) :
  (τs.hasTag t₁ t₂).WellFormed εs ∧ (τs.hasTag t₁ t₂).typeOf = .bool
:= by
  simp only [SymTags.hasTag]
  replace ⟨hwf, harg, hout, hwτ⟩ := hwτ
  rw [← harg] at hty₁
  have happ := wf_app hw₁ hty₁ hwf
  rw [hout, ← hty₂] at happ
  exact wf_set_member hw₂ happ.left happ.right

theorem wf_tagOf {εs : SymEntities} {t₁ t₂ : Term} {ety : EntityType}
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty₁ : t₁.typeOf = TermType.entity ety)
  (hty₂ : t₂.typeOf = TermType.string) :
  (tagOf t₁ t₂).WellFormed εs ∧ (tagOf t₁ t₂).typeOf = TermType.tagFor ety
:= by
  simp only [tagOf, EntityTag.mk, TermType.tagFor]
  constructor
  · apply Term.WellFormed.record_wf
    · intro a t hin
      simp only [Map.toList_mk_id, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hin
      rcases hin with ⟨_, hin⟩ | ⟨_, hin⟩ <;>
      subst hin <;>
      assumption
    · simp [Map.WellFormed, Map.make, List.canonicalize, List.insertCanonical, String.reduceLT]
  · simp only [typeOf_term_record_eq, List.map_cons, hty₁, hty₂, List.map_nil]

theorem wf_tags_getTag! {εs : SymEntities} {τs : SymTags} {t₁ t₂ : Term} {ety : EntityType}
  (hwτ : τs.WellFormed εs ety)
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty₁ : t₁.typeOf = TermType.entity ety)
  (hty₂ : t₂.typeOf = TermType.string) :
  (τs.getTag! t₁ t₂).WellFormed εs ∧ (τs.getTag! t₁ t₂).typeOf = τs.vals.outType
:= by
  simp only [SymTags.getTag!]
  have ⟨hwf, harg, _⟩ := hwτ.right.right.right
  have hwt := wf_tagOf hw₁ hw₂ hty₁ hty₂
  rw [← harg] at hwt
  exact wf_app hwt.left hwt.right hwf

theorem wf_tags_getTag {εs : SymEntities} {τs : SymTags} {t₁ t₂ : Term} {ety : EntityType}
  (hwτ : τs.WellFormed εs ety)
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hty₁ : t₁.typeOf = TermType.entity ety)
  (hty₂ : t₂.typeOf = TermType.string) :
  (τs.getTag t₁ t₂).WellFormed εs ∧ (τs.getTag t₁ t₂).typeOf = τs.vals.outType.option
:= by
  simp only [SymTags.getTag]
  have happ := wf_tags_getTag! hwτ hw₁ hw₂ hty₁ hty₂
  replace hwτ := wf_tags_hasTag hwτ hw₁ hw₂ hty₁ hty₂
  rw [← happ.right]
  exact wf_ifTrue hwτ.left happ.left hwτ.right

end Cedar.Thm
