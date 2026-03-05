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

module

import Cedar.Spec
public import Cedar.SymCC.Env
public import Cedar.SymCC.Factory
import all Cedar.SymCC.Factory -- proving things about Factory functions, so we need access to internals that aren't normally exposed
public import Cedar.SymCC.Term
import all Cedar.SymCC.Term -- proving things about Term, so we need access to internals that aren't normally exposed
import all Cedar.SymCC.TermType -- proving things about TermType, so we need access to internals that aren't normally exposed
import Cedar.Thm.Data
import Cedar.Thm.SymCC.Data
import Cedar.Thm.SymCC.Env.WF
public import Cedar.Thm.SymCC.Data.Basic

/-!
# Properties of Terms

This file contains lemmas about the `typeOf` function on Terms.
-/

namespace Cedar.Thm

open Data Spec SymCC

public theorem typeOf_bool {b : Bool} :
  Term.typeOf (Term.prim (TermPrim.bool b)) = TermType.bool
:= by simp [Term.typeOf, TermPrim.typeOf]

public theorem typeOf_bv {n : Nat} {bv : BitVec n} :
  Term.typeOf (Term.prim (TermPrim.bitvec bv)) = .bitvec n
:= by simp [Term.typeOf, TermPrim.typeOf, BitVec.width]

public theorem typeOf_bv_width {n m : Nat} {bv : BitVec m} :
  Term.typeOf (Term.prim (TermPrim.bitvec bv)) = TermType.bitvec n →
  m = n
:= by simp [Term.typeOf, TermPrim.typeOf, BitVec.width]

public theorem typeOf_term_none (ty : TermType) :
  Term.typeOf (Term.none ty) = TermType.option ty
:= by simp [Term.typeOf]

public theorem typeOf_term_some {t : Term} :
  Term.typeOf (Term.some t) = TermType.option t.typeOf
:= by simp only [Term.typeOf]

public theorem typeOf_term_some_iff {t : Term} {ty : TermType} :
  t.typeOf = ty ↔
  Term.typeOf (Term.some t) = TermType.option ty
:= by simp only [Term.typeOf, TermType.option.injEq]

public theorem typeOf_term_prim_isPrimType (p : TermPrim) :
  (Term.prim p).typeOf.isPrimType
:= by
  simp only [Term.typeOf, TermPrim.typeOf]
  split <;>
  simp only [TermType.isPrimType]

public theorem typeOf_term_prim_entity {uid : EntityUID} :
  (Term.entity uid).typeOf = TermType.entity uid.ty
:= by
  simp only [Term.typeOf, TermPrim.typeOf]

public theorem typeOf_term_prim_string {s : String} :
  (Term.string s).typeOf = TermType.string
:= by
  simp only [Term.typeOf, TermPrim.typeOf]

public theorem typeOf_term_prim_ext_decimal {d : Ext.Decimal} :
  (Term.prim (.ext (.decimal d))).typeOf = TermType.ext Validation.ExtType.decimal
:= by simp only [Term.typeOf, TermPrim.typeOf]

public theorem typeOf_term_prim_ext_ipaddr {ip : Ext.IPAddr.IPNet} :
  (Term.prim (.ext (.ipaddr ip))).typeOf = TermType.ext Validation.ExtType.ipAddr
:= by simp only [Term.typeOf, TermPrim.typeOf]

public theorem typeOf_term_prim_ext_datetime {d : Ext.Datetime} :
  (Term.prim (.ext (.datetime d))).typeOf = TermType.ext Validation.ExtType.datetime
:= by simp only [Term.typeOf, TermPrim.typeOf]

public theorem typeOf_term_prim_ext_duration {d : Ext.Datetime.Duration} :
  (Term.prim (.ext (.duration d))).typeOf = TermType.ext Validation.ExtType.duration
:= by simp only [Term.typeOf, TermPrim.typeOf]

public theorem typeOf_term_record_eq  {r : Map Attr Term} :
  Term.typeOf (Term.record r) =
  TermType.record (r.mapOnValues Term.typeOf)
:= by simp only [Term.typeOf, Map.mapOnValues₂_eq_mapOnValues]

public theorem typeOf_term_record_is_record_type {r : Map Attr Term} :
  ∃ rty, (Term.record r).typeOf = TermType.record rty
:= by
  unfold Term.typeOf
  simp only [TermType.record.injEq, exists_eq']

public theorem typeOf_term_record_attr_value {r : Map Attr Term} {rty : Map Attr TermType} {a : Attr} {ty : TermType}
  (h₁ : (Term.record r).typeOf = TermType.record rty)
  (h₂ : rty.find? a = .some ty) :
  ∃ t, r.find? a = .some t ∧ t.typeOf = ty
:= by
  rw [typeOf_term_record_eq] at h₁
  simp only [TermType.record.injEq] at *
  subst h₁
  replace ⟨t, h₂, _⟩ := Map.find?_mapOnValues_some' _ h₂
  subst ty
  exists t

public theorem typeOf_term_record_attr_value_none {r : Map Attr Term} {rty : Map Attr TermType} {a : Attr}
  (h₁ : (Term.record r).typeOf = TermType.record rty)
  (h₂ : rty.find? a = none) :
  r.find? a = none
:= by
  rw [typeOf_term_record_eq] at h₁
  simp only [TermType.record.injEq] at *
  subst h₁
  rw [Map.find?_mapOnValues_none Term.typeOf] at h₂
  exact h₂

public theorem typeOf_term_record_attr_value_typeOf {r : Map Attr Term} {a : Attr} {t : Term}
  (h₁ : (Term.record r).typeOf = TermType.record rty)
  (h₂ : r.find? a = .some t) :
  rty.find? a = .some t.typeOf
:= by
  rw [typeOf_term_record_eq] at h₁
  simp only [TermType.record.injEq] at *
  subst h₁
  exact Map.find?_mapOnValues_some _ h₂

public theorem typeOf_term_record_attr_value_eq {r₁ r₂ : Map Attr Term} {rty : Map Attr TermType} {a : Attr} {t₁ t₂ : Term}
  (hty₁ : (Term.record r₁).typeOf = .record rty)
  (hty₂ : (Term.record r₂).typeOf = .record rty)
  (ht₁ : r₁.find? a = .some t₁)
  (ht₂ : r₂.find? a = .some t₂) :
  t₁.typeOf = t₂.typeOf
:= by
  replace ht₁ := typeOf_term_record_attr_value_typeOf hty₁ ht₁
  replace ht₂ := typeOf_term_record_attr_value_typeOf hty₂ ht₂
  simp only [ht₁, Option.some.injEq] at ht₂
  exact ht₂

public theorem typeOf_term_record_tail {a : Attr} {t₁ t₂ : Term} {tl₁ tl₂ : List (Attr × Term)} :
  Term.typeOf (Term.record (Map.mk ((a, t₁) :: tl₁))) = Term.typeOf (Term.record (Map.mk ((a, t₂) :: tl₂))) →
  Term.typeOf (Term.record (Map.mk tl₁)) = Term.typeOf (Term.record (Map.mk tl₂))
:= by
  simp only [typeOf_term_record_eq, TermType.record.injEq]
  exact Map.mapOnValues_tail (f := Term.typeOf)

private theorem typeOf_wf_term_prim_is_wf {εs : SymEntities} {p : TermPrim} :
  TermPrim.WellFormed εs p →
  TermType.WellFormed εs (TermPrim.typeOf p)
:= by
  intro h₁
  cases p <;>
  simp only [TermPrim.typeOf]
  case bool   => exact TermType.WellFormed.bool_wf
  case bitvec => exact TermType.WellFormed.bitvec_wf
  case string => exact TermType.WellFormed.string_wf
  case entity uid =>
    cases h₁ ; rename_i h₁
    exact TermType.WellFormed.entity_wf (validEntityUID_implies_validEntityType h₁)
  case ext v =>
    cases v <;>
    simp only <;>
    exact TermType.WellFormed.ext_wf

private theorem type_of_wt_op_is_wf {εs : SymEntities} {op : Op} {ts : List Term} {ty : TermType}
  (ht: Op.WellTyped εs op ts ty)
  (ih: ∀ (t : Term), t ∈ ts → TermType.WellFormed εs (Term.typeOf t)) :
  TermType.WellFormed εs ty
:= by
  cases ht
  case ite_wt =>
    apply ih
    simp only [List.mem_cons, true_or, or_true]
  case uuf_wt h₂ =>
    exact h₂.right
  case set.inter_wt t₁ _ ty h₁ _ =>
    specialize ih t₁
    simp [List.mem_cons, true_or, forall_const, h₁] at ih
    exact ih
  case option.get_wt t h₁ =>
    specialize ih t
    simp only [List.mem_singleton, h₁, forall_const] at ih
    cases ih
    assumption
  case record.get_wt t a rty h₁ h₂ =>
    specialize ih t
    simp only [List.mem_singleton, forall_const, h₁] at ih
    cases ih
    rename_i ih _
    exact ih a ty h₂
  case' ext_wt h₂ => cases h₂
  all_goals {
    first
    | exact TermType.WellFormed.bool_wf
    | exact TermType.WellFormed.bitvec_wf
    | exact TermType.WellFormed.option_wf TermType.WellFormed.bitvec_wf
    | exact TermType.WellFormed.ext_wf
  }

private theorem type_of_wf_term_record_is_wf {εs : SymEntities} {r : Map Attr Term}
  (hwf : Map.WellFormed r)
  (ih : ∀ (a : Attr) (t : Term), (a, t) ∈ Map.toList r → TermType.WellFormed εs (Term.typeOf t)) :
  TermType.WellFormed εs (Term.typeOf (Term.record r))
:= by
  unfold Term.typeOf
  rw [Map.mapOnValues₂_eq_mapOnValues]
  apply TermType.WellFormed.record_wf
  case h₁ =>
    intro a ty h
    replace ⟨t, h, _⟩ := Map.find?_mapOnValues_some' _ h
    subst ty
    apply ih a
    exact Map.find?_mem_toList h
  case h₂ =>
    exact Map.mapOnValues_wf.mp hwf

public theorem typeOf_wf_term_is_wf {εs : SymEntities} {t : Term} :
  t.WellFormed εs →
  t.typeOf.WellFormed εs
:= by
  intro h₁
  induction h₁
  case prim_wf p h₁ =>
    simp only [Term.typeOf]
    exact typeOf_wf_term_prim_is_wf h₁
  case var_wf h₁ =>
    simp only [TermVar.WellFormed] at h₁
    simp only [Term.typeOf, h₁]
  case none_wf h | some_wf h =>
    simp only [Term.typeOf]
    exact TermType.WellFormed.option_wf h
  case app_wf h₂ ih =>
    simp only [Term.typeOf]
    exact type_of_wt_op_is_wf h₂ ih
  case set_wf _ _ h₃ _ _ =>
    simp only [Term.typeOf]
    exact TermType.WellFormed.set_wf h₃
  case record_wf h₂ ih =>
    exact type_of_wf_term_record_is_wf h₂ ih

public theorem wfp_term_implies_wf_ty {εs : SymEntities} {t : Term}
  (h : Term.WellFormedPartialApp εs t) :
  t.typeOf.WellFormed εs
:= by
  cases h with
  | none_wfp h =>
    simp only [Term.typeOf]
    exact h
  | _ =>
    simp only [Term.typeOf]
    repeat constructor

public theorem typeOf_option_wf_terms_is_wf {εs : SymEntities} {hd : Term} {tl : List Term} {ts : List Term} {ty : TermType}:
  ts = hd :: tl →
  (∀ t ∈ ts, t.WellFormed εs) →
  (∀ t ∈ ts, Term.typeOf t = TermType.option ty) →
  ty.WellFormed εs
:= by
  intro hcons hwf hty
  subst hcons
  replace hwf := typeOf_wf_term_is_wf (hwf hd List.mem_cons_self)
  rw [hty hd List.mem_cons_self] at hwf
  cases hwf
  assumption

public theorem typeOf_term_record_cedarType?_some_implies_attr_cedarType?_some {a : Attr} {t : Term} {r : Map Attr Term} {ty : Validation.CedarType} :
  r.WellFormed →
  (Term.record r).typeOf.cedarType? = some ty →
  (a, t) ∈ r.toList →
  ∃ (tty : TermType) (cty : Validation.CedarType),
    tty.cedarType? = some cty ∧
    (t.typeOf = tty ∨ t.typeOf = .option tty)
:= by
  intro hwf hty hin
  simp only [typeOf_term_record_eq] at hty
  unfold TermType.cedarType? at hty
  rw [do_some] at hty
  replace ⟨atys, hty, _⟩ := hty
  subst ty
  rw [Map.mapMOnValues₂_eq_mapMOnValues] at hty
  simp only [Map.mapMOnValues_mapOnValues] at hty
  replace hty := Map.mapMOnValues_some_implies_all_some hty (a, t)
  replace ⟨qty, haty, hty⟩ := hty hin
  simp only [Function.comp_apply] at hty
  unfold TermType.cedarType?.qualifiedType? at hty
  split at hty <;>
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hty <;>
  replace ⟨cty, hty, _⟩ := hty <;> subst qty
  · rename_i tty heq
    exists tty, cty
    simp only [hty, heq, or_true, and_self]
  · exists t.typeOf, cty
    simp only [hty, true_or, and_self]

public theorem isPrimType_implies_prim_type {ty : TermType} :
  ty.isPrimType → ∃ pty, ty = .prim pty
:= by
  simp only [TermType.isPrimType]
  split <;>
  simp only [TermType.prim.injEq, exists_eq', imp_self, false_implies, Bool.false_eq_true]

public theorem isEntityType_implies_entity_type {ty : TermType} :
  ty.isEntityType → ∃ ety, ty = .entity ety
:= by
  simp only [TermType.isEntityType]
  split
  · simp only [TermType.prim.injEq, TermPrimType.entity.injEq, exists_eq', imp_self]
  · simp only [Bool.false_eq_true, false_implies]

public theorem isOptionEntityType_implies_option_entity_type {ty : TermType} :
  ty.isOptionEntityType → ∃ ety, ty = .option (.entity ety)
:= by
  simp only [TermType.isOptionEntityType]
  split
  · simp only [TermType.option.injEq, TermType.prim.injEq, TermPrimType.entity.injEq, exists_eq', imp_self]
  · simp only [Bool.false_eq_true, false_implies]

private theorem typeOf_ite_simplify_option {g t : Term} {ty : TermType} :
  t.typeOf = .option ty →
  (Factory.ite.simplify g (Term.none ty) t).typeOf = ty.option
:= by
  intro hty
  simp only [Factory.ite.simplify, Bool.or_eq_true, decide_eq_true_eq]
  split
  · simp only [Term.typeOf]
  · split
    · exact hty
    · split <;> simp [typeOf_bool, Term.typeOf] at *

public theorem typeOf_ifSome_option {g t : Term} {ty : TermType} :
  t.typeOf = .option ty →
  (Factory.ifSome g t).typeOf = .option ty
:= by
  intro hty
  simp only [Factory.ifSome, hty, Factory.ite, Factory.noneOf]
  exact typeOf_ite_simplify_option hty

public theorem typeOf_ifAllSome_option_type {gs : List Term} {t : Term} {ty : TermType} :
  t.typeOf = .option ty →
  (Factory.ifAllSome gs t).typeOf = .option ty
:= by
  intro hty
  simp only [Factory.ifAllSome, hty, Factory.ite, Factory.noneOf]
  exact typeOf_ite_simplify_option hty

end Cedar.Thm
