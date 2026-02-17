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
import Cedar.Thm.SymCC.Term.WF
import Cedar.Thm.SymCC.Interpretation

/-!
# Interpretation of Terms and Factory functions

This file basic lemmas about the interpretation of terms and
the Factory functions for creating terms.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem interpret_term_prim {I : Interpretation} {p : TermPrim} :
  (Term.prim p).interpret I = Term.prim p
:= by simp only [Term.interpret]

theorem interpret_term_var {I : Interpretation} {v : TermVar} :
  (Term.var v).interpret I = I.vars v
:= by simp only [Term.interpret]

theorem interpret_term_none {I : Interpretation} {ty : TermType} :
  (Term.none ty).interpret I = Term.none ty
:= by simp only [Term.interpret, noneOf]

theorem interpret_term_some {I : Interpretation} {t : Term} :
  (Term.some t).interpret I = Term.some (t.interpret I)
:= by simp only [Term.interpret, someOf]

theorem interpret_term_set {I : Interpretation} {s : Set Term} {ty : TermType} :
  (Term.set s ty).interpret I =
  Term.set (Set.make (s.elts.map (Term.interpret I))) ty
:= by
  cases s
  simp only [Term.interpret, setOf, List.map₁_eq_map (Term.interpret I ·)]

theorem interpret_term_set_empty {ty : TermType} :
  Term.interpret I (Term.set (Set.mk []) ty) = Term.set (Set.mk []) ty
:= by
  simp only [interpret_term_set, Set.make, Set.elts, List.map_nil, List.canonicalize_nil]

theorem interpret_term_record {I : Interpretation} {r : Map Attr Term} :
  (Term.record r).interpret I =
  Term.record (Map.make (r.kvs.map λ (a, t) => (a, t.interpret I)))
:= by
  cases r
  simp only [Term.interpret, recordOf, List.map₃_eq_map λ (x : (Attr × Term)) => (x.fst, x.snd.interpret I)]

/--
This tactic discharges proofs in lemmas of the form `interpret_term_app_*`,
which unroll the interpretation of `app` terms.
-/
local syntax "simp_interpret_term_app" : tactic

local macro_rules
| `(tactic| simp_interpret_term_app) =>
  `(tactic|
    simp only [Term.interpret, List.map₁_eq_map, List.map_cons, List.map_nil] ;
    simp only [Op.interpret] -- Faster proof when this is a separate simp
    )

theorem interpret_term_app_not {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app .not [t₁] ty).interpret I =
  Factory.not (t₁.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_and {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .and [t₁, t₂] ty).interpret I =
  Factory.and (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_or {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .or [t₁, t₂] ty).interpret I =
  Factory.or (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_eq {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .eq [t₁, t₂] ty).interpret I =
  Factory.eq (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_ite {I : Interpretation} {t₁ t₂ t₃ : Term} {ty : TermType} :
  (Term.app .ite [t₁, t₂, t₃] ty).interpret I =
  Factory.ite (t₁.interpret I) (t₂.interpret I) (t₃.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_uuf {I : Interpretation} {f : UUF} {t₁ : Term} {ty : TermType} :
  (Term.app (.uuf f) [t₁] ty).interpret I =
  Factory.app (.udf (I.funs f)) (t₁.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvneg {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app .bvneg [t₁] ty).interpret I =
  Factory.bvneg (t₁.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvadd {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvadd [t₁, t₂] ty).interpret I =
  Factory.bvadd (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvsub {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvsub [t₁, t₂] ty).interpret I =
  Factory.bvsub (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvmul {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvmul [t₁, t₂] ty).interpret I =
  Factory.bvmul (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvsdiv {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvsdiv [t₁, t₂] ty).interpret I =
  Factory.bvsdiv (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvudiv {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvudiv [t₁, t₂] ty).interpret I =
  Factory.bvudiv (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvsrem {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvsrem [t₁, t₂] ty).interpret I =
  Factory.bvsrem (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvsmod {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvsmod [t₁, t₂] ty).interpret I =
  Factory.bvsmod (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvumod {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvumod [t₁, t₂] ty).interpret I =
  Factory.bvumod (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvshl {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvshl [t₁, t₂] ty).interpret I =
  Factory.bvshl (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvlshr {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvlshr [t₁, t₂] ty).interpret I =
  Factory.bvlshr (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvnego {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app .bvnego [t₁] ty).interpret I =
  Factory.bvnego (t₁.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvsaddo {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvsaddo [t₁, t₂] ty).interpret I =
  Factory.bvsaddo (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvssubo {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvssubo [t₁, t₂] ty).interpret I =
  Factory.bvssubo (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvsmulo {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvsmulo [t₁, t₂] ty).interpret I =
  Factory.bvsmulo (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvslt {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvslt [t₁, t₂] ty).interpret I =
  Factory.bvslt (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvsle {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvsle [t₁, t₂] ty).interpret I =
  Factory.bvsle (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvult {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvult [t₁, t₂] ty).interpret I =
  Factory.bvult (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_bvule {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app .bvule [t₁, t₂] ty).interpret I =
  Factory.bvule (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_zero_extend {I : Interpretation} {n : Nat} {t₁ : Term} {ty : TermType} :
  (Term.app (.zero_extend n) [t₁] ty).interpret I =
  Factory.zero_extend n (t₁.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_set_member {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app Op.set.member [t₁, t₂] ty).interpret I =
  Factory.set.member (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_set_subset {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app Op.set.subset [t₁, t₂] ty).interpret I =
  Factory.set.subset (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_set_inter {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  (Term.app Op.set.inter [t₁, t₂] ty).interpret I =
  Factory.set.inter (t₁.interpret I) (t₂.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_option_get {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app Op.option.get [t₁] ty).interpret I =
  Factory.option.get' I (t₁.interpret I)
:= by simp_interpret_term_app

theorem interpret_term_app_record_get {I : Interpretation} {a : Attr} {t₁ : Term} {ty : TermType} :
  (Term.app (Op.record.get a) [t₁] ty).interpret I =
  Factory.record.get (t₁.interpret I) a
:= by simp_interpret_term_app

theorem interpret_term_app_string_like {I : Interpretation} {p : Pattern} {t₁ : Term} {ty : TermType} :
  (Term.app (Op.string.like p) [t₁] ty).interpret I =
  Factory.string.like (t₁.interpret I) p
:= by simp_interpret_term_app

theorem interpret_term_app_ext_decimal_val {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app (.ext ExtOp.decimal.val) [t₁] ty).interpret I =
  Factory.ext.decimal.val (t₁.interpret I)
:= by simp_interpret_term_app; simp only [ExtOp.interpret]

theorem interpret_term_app_ext_ipaddr_isV4 {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app (.ext ExtOp.ipaddr.isV4) [t₁] ty).interpret I =
  Factory.ext.ipaddr.isV4 (t₁.interpret I)
:= by simp_interpret_term_app; simp only [ExtOp.interpret]

theorem interpret_term_app_ext_ipaddr_addrV4 {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app (.ext ExtOp.ipaddr.addrV4) [t₁] ty).interpret I =
  Factory.ext.ipaddr.addrV4' I (t₁.interpret I)
:= by simp_interpret_term_app; simp only [ExtOp.interpret]

theorem interpret_term_app_ext_ipaddr_prefixV4 {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app (.ext ExtOp.ipaddr.prefixV4) [t₁] ty).interpret I =
  Factory.ext.ipaddr.prefixV4' I (t₁.interpret I)
:= by simp_interpret_term_app; simp only [ExtOp.interpret]

theorem interpret_term_app_ext_ipaddr_addrV6 {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app (.ext ExtOp.ipaddr.addrV6) [t₁] ty).interpret I =
  Factory.ext.ipaddr.addrV6' I (t₁.interpret I)
:= by simp_interpret_term_app; simp only [ExtOp.interpret]

theorem interpret_term_app_ext_ipaddr_prefixV6 {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app (.ext ExtOp.ipaddr.prefixV6) [t₁] ty).interpret I =
  Factory.ext.ipaddr.prefixV6' I (t₁.interpret I)
:= by simp_interpret_term_app; simp only [ExtOp.interpret]

theorem interpret_term_app_ext_datetime_val {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app (.ext ExtOp.datetime.val) [t₁] ty).interpret I =
  Factory.ext.datetime.val (t₁.interpret I)
:= by simp_interpret_term_app; simp only [ExtOp.interpret]

theorem interpret_term_app_ext_datetime_ofBitVec {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app (.ext ExtOp.datetime.ofBitVec) [t₁] ty).interpret I =
  Factory.ext.datetime.ofBitVec (t₁.interpret I)
:= by simp_interpret_term_app; simp only [ExtOp.interpret]

theorem interpret_term_app_ext_duration_val {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app (.ext ExtOp.duration.val) [t₁] ty).interpret I =
  Factory.ext.duration.val (t₁.interpret I)
:= by simp_interpret_term_app; simp only [ExtOp.interpret]

theorem interpret_term_app_ext_duration_ofBitVec {I : Interpretation} {t₁ : Term} {ty : TermType} :
  (Term.app (.ext ExtOp.duration.ofBitVec) [t₁] ty).interpret I =
  Factory.ext.duration.ofBitVec (t₁.interpret I)
:= by simp_interpret_term_app; simp only [ExtOp.interpret]

end Cedar.Thm
