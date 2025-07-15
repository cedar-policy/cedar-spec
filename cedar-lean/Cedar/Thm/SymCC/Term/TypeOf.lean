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

import Cedar.Spec
import Cedar.SymCC
import Cedar.Thm.Data
import Cedar.Thm.SymCC.Data

/-!
# Properties of Terms

This file contains lemmas about the `typeOf` function on Terms.
-/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem typeOf_bool {b : Bool} :
  Term.typeOf (Term.prim (TermPrim.bool b)) = TermType.bool
:= by simp [Term.typeOf, TermPrim.typeOf]

theorem typeOf_bv {n : Nat} {bv : BitVec n} :
  Term.typeOf (Term.prim (TermPrim.bitvec bv)) = .bitvec n
:= by simp [Term.typeOf, TermPrim.typeOf, BitVec.width]

theorem typeOf_bv_width {n m : Nat} {bv : BitVec m} :
  Term.typeOf (Term.prim (TermPrim.bitvec bv)) = TermType.bitvec n →
  m = n
:= by
  intro h₁
  simp [Term.typeOf, TermPrim.typeOf, BitVec.width] at h₁
  exact h₁

theorem typeOf_term_none (ty : TermType) :
  Term.typeOf (Term.none ty) = TermType.option ty
:= by simp [Term.typeOf]

theorem typeOf_term_some {t : Term} :
  Term.typeOf (Term.some t) = TermType.option t.typeOf
:= by simp only [Term.typeOf]

theorem typeOf_term_some_iff {t : Term} {ty : TermType} :
  t.typeOf = ty ↔
  Term.typeOf (Term.some t) = TermType.option ty
:= by simp only [Term.typeOf, TermType.option.injEq]

theorem typeOf_term_prim_isPrimType (p : TermPrim) :
  (Term.prim p).typeOf.isPrimType
:= by
  simp only [Term.typeOf, TermPrim.typeOf]
  split <;>
  simp only [TermType.isPrimType]

theorem typeOf_term_prim_entity {uid : EntityUID} :
  (Term.entity uid).typeOf = TermType.entity uid.ty
:= by
  simp only [Term.typeOf, TermPrim.typeOf]

theorem typeOf_term_prim_string {s : String} :
  (Term.string s).typeOf = TermType.string
:= by
  simp only [Term.typeOf, TermPrim.typeOf]

theorem typeOf_term_prim_ext_decimal {d : Ext.Decimal} :
  (Term.prim (.ext (.decimal d))).typeOf = TermType.ext Validation.ExtType.decimal
:= by simp only [Term.typeOf, TermPrim.typeOf]

theorem typeOf_term_prim_ext_ipaddr {ip : Ext.IPAddr.IPNet} :
  (Term.prim (.ext (.ipaddr ip))).typeOf = TermType.ext Validation.ExtType.ipAddr
:= by simp only [Term.typeOf, TermPrim.typeOf]

theorem typeOf_term_prim_ext_datetime {d : Ext.Datetime} :
  (Term.prim (.ext (.datetime d))).typeOf = TermType.ext Validation.ExtType.datetime
:= by simp only [Term.typeOf, TermPrim.typeOf]

theorem typeOf_term_prim_ext_duration {d : Ext.Datetime.Duration} :
  (Term.prim (.ext (.duration d))).typeOf = TermType.ext Validation.ExtType.duration
:= by simp only [Term.typeOf, TermPrim.typeOf]

theorem typeOf_term_record_eq  {r : Map Attr Term}  :
  Term.typeOf (Term.record r) =
  TermType.record (Map.mk (List.map (fun (x : Attr × Term) => (x.fst, Term.typeOf x.snd)) r.1))
:= by
  rw [Term.typeOf]
  simp only [List.attach₃,
    List.map_pmap_subtype (fun (x : Attr × Term) => (x.fst, Term.typeOf x.snd))]

theorem typeOf_term_record_is_record_type {r : Map Attr Term} :
  ∃ rty, (Term.record r).typeOf = TermType.record rty
:= by
  unfold Term.typeOf
  simp only [TermType.record.injEq, exists_eq']

theorem typeOf_term_record_attr_value {r : Map Attr Term} {rty : Map Attr TermType} {a : Attr} {ty : TermType}
  (h₁ : (Term.record r).typeOf = TermType.record rty)
  (h₂ : rty.find? a = .some ty) :
  ∃ t, r.find? a = .some t ∧ t.typeOf = ty
:= by
  rw [typeOf_term_record_eq] at h₁
  simp [Map.find?, Map.kvs] at *
  subst h₁
  split at h₂ <;> simp only [Option.some.injEq, reduceCtorEq] at h₂
  subst h₂
  rename_i a' ty h₂
  have h₃ := List.find?_some h₂ ; simp at h₃ ; subst h₃
  have h₄ : Prod.map id Term.typeOf = (fun (x : Attr × Term) => (x.fst, Term.typeOf x.snd)) := by
    apply funext ; intro x ; simp only [Prod.map, id_eq]
  rw [←h₄] at h₂
  replace ⟨x, h₂⟩ := List.find?_fst_map_implies_find? h₂
  exists x.snd
  simp only [h₂, true_and]
  simp only [Prod.map, id_eq, Prod.mk.injEq] at h₂
  simp only [h₂]

theorem typeOf_term_record_attr_value_none {r : Map Attr Term} {rty : Map Attr TermType} {a : Attr}
  (h₁ : (Term.record r).typeOf = TermType.record rty)
  (h₂ : rty.find? a = none) :
  r.find? a = none
:= by
  rw [typeOf_term_record_eq] at h₁
  simp [Map.find?, Map.kvs] at *
  subst h₁
  split at h₂ <;> simp only [Option.some.injEq, reduceCtorEq] at h₂
  rename_i h₃
  split <;> simp only [reduceCtorEq]
  rename_i a t h₄
  apply h₃ a t.typeOf
  rw [← List.find?_pair_map, h₄, Option.map]

theorem typeOf_term_record_attr_value_typeOf {r : Map Attr Term} {a : Attr} {t : Term}
  (h₁ : (Term.record r).typeOf = TermType.record rty)
  (h₂ : r.find? a = .some t) :
  rty.find? a = .some t.typeOf
:= by
  rw [typeOf_term_record_eq] at h₁
  simp [Map.find?, Map.kvs] at *
  subst h₁
  have hmv : (r.mapOnValues Term.typeOf) = Map.mk (List.map (fun x => (x.fst, Term.typeOf x.snd)) r.1) := by
    simp only [Map.mapOnValues]
  rw [← hmv]
  exact Map.find?_mapOnValues_some _ h₂

theorem typeOf_term_record_attr_value_eq {r₁ r₂ : Map Attr Term} {rty : Map Attr TermType} {a : Attr} {t₁ t₂ : Term}
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

theorem typeOf_term_record_tail {a : Attr} {t₁ t₂ : Term} {tl₁ tl₂ : List (Attr × Term)} :
  Term.typeOf (Term.record (Map.mk ((a, t₁) :: tl₁))) = Term.typeOf (Term.record (Map.mk ((a, t₂) :: tl₂))) →
  Term.typeOf (Term.record (Map.mk tl₁)) = Term.typeOf (Term.record (Map.mk tl₂))
:= by
  simp only [typeOf_term_record_eq, List.map_cons, TermType.record.injEq, Map.mk.injEq,
    List.cons.injEq, Prod.mk.injEq, true_and, and_imp, imp_self, implies_true]

private theorem validEntityUID_implies_validEntityType {εs : SymEntities} {uid : EntityUID} :
  SymEntities.isValidEntityUID εs uid = true →
  SymEntities.isValidEntityType εs uid.ty = true
:= by
  simp only [SymEntities.isValidEntityUID, SymEntities.isValidEntityType]
  intro h₁
  cases h₂ : Map.find? εs uid.ty <;>
  simp only [h₂, Bool.false_eq_true] at h₁
  rw [Map.contains_iff_some_find?]
  rename_i εd
  exists εd

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
    simp only [List.mem_cons, List.mem_singleton, true_or, or_true]
  case uuf_wt h₂ =>
    exact h₂.right
  case set.inter_wt t₁ _ ty h₁ _ =>
    specialize ih t₁
    simp [List.mem_cons, true_or, or_true, forall_const, h₁] at ih
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
  simp only [List.attach₃, List.map_pmap_subtype (fun (x : Attr × Term) => (x.fst, Term.typeOf x.snd))]
  apply TermType.WellFormed.record_wf
  case h₁ =>
    intro a ty h
    simp only [Map.find?, Map.kvs] at h
    rw [←List.find?_pair_map, eq_comm] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rename_i heq
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at heq
    replace ⟨axt, heq, _, heq'⟩ := heq
    replace heq := List.mem_of_find?_eq_some heq
    have haxt : axt = (axt.fst, axt.snd) := by simp only
    specialize ih axt.fst axt.snd
    simp only [← haxt, Map.toList, Map.kvs, heq, heq', forall_const] at ih
    exact ih
  case h₂ =>
    simp only [Map.WellFormed] at *
    simp only [Map.make, Map.toList, Map.kvs, Map.mk.injEq] at *
    have hmap : (fun (x : Attr × Term) => (x.fst, Term.typeOf x.snd)) = Prod.map id Term.typeOf := by
      apply funext ; intro x  ; simp [Prod.map]
    simp only [hmap, List.canonicalize_of_map_fst r.1 Term.typeOf]
    rw [hwf]
    simp only [List.canonicalize_idempotent Prod.fst r.1]

theorem typeOf_wf_term_is_wf {εs : SymEntities} {t : Term} :
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

theorem typeOf_option_wf_terms_is_wf {εs : SymEntities} {hd : Term} {tl : List Term} {ts : List Term} {ty : TermType}:
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

theorem isCedarRecordType_implies_term_record_type {ty : TermType} :
  ty.isCedarRecordType → ∃ rty, ty = .record rty
:= by
  intro h
  simp [TermType.isCedarRecordType] at h
  split at h
  case h_1 heq =>
    unfold TermType.cedarType? at heq
    cases ty <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Validation.CedarType.record.injEq, and_false, exists_const, reduceCtorEq] at heq
    case prim pty =>
      cases pty <;> try { simp only [Option.some.injEq, reduceCtorEq] at heq  }
      case bitvec m =>
        by_cases h : m = 64
        case pos =>
          subst h
          simp only [Option.some.injEq, reduceCtorEq] at heq
        case neg =>
          split at heq <;> simp only [Option.bind_eq_some_iff, Option.some.injEq,
            Validation.CedarType.record.injEq, and_false, exists_const, reduceCtorEq] at heq
          rename_i heq'
          simp only [reduceCtorEq] at heq'
    case record rty =>
      exists rty
  case h_2 => contradiction

theorem typeOf_term_record_cedarType?_some_implies_attr_cedarType?_some {a : Attr} {t : Term} {r : List (Attr × Term)} {ty : Validation.CedarType} :
  (Term.record (Map.mk r)).typeOf.cedarType? = some ty →
  (a, t) ∈ r →
  ∃ (tty : TermType) (cty : Validation.CedarType),
    tty.cedarType? = some cty ∧
    (t.typeOf = tty ∨ t.typeOf = .option tty)
:= by
  intro hty hin
  simp only [typeOf_term_record_eq] at hty
  simp only [TermType.cedarType?,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hty
  replace ⟨atys, hty, _⟩ := hty
  simp only [List.mapM₃, List.attach₃,
    List.mapM_pmap_subtype λ (x : Attr × TermType) =>
    (TermType.cedarType?.qualifiedType? x.snd).bind
    λ qty => some (x.fst, qty)] at hty
  replace hty := List.mapM_some_implies_all_some hty (a, t.typeOf)
  simp only [List.mem_map, Prod.mk.injEq, Option.bind_eq_some_iff, Option.some.injEq,
    forall_exists_index, and_imp] at hty
  specialize hty (a, t) hin
  simp only [true_implies] at hty
  have ⟨_, _, _, hty, _⟩ := hty
  unfold TermType.cedarType?.qualifiedType? at hty
  split at hty <;>
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hty <;>
  replace ⟨cty, hty⟩ := hty
  · rename_i tty heq
    exists tty, cty
    simp only [hty, heq, or_true, and_self]
  · exists t.typeOf, cty
    simp only [hty, true_or, and_self]

theorem isPrimType_implies_prim_type {ty : TermType} :
  ty.isPrimType → ∃ pty, ty = .prim pty
:= by
  simp only [TermType.isPrimType]
  split <;>
  simp only [TermType.prim.injEq, exists_eq', imp_self, false_implies, Bool.false_eq_true]

theorem isEntityType_implies_entity_type {ty : TermType} :
  ty.isEntityType → ∃ ety, ty = .entity ety
:= by
  simp only [TermType.isEntityType]
  split
  · simp only [TermType.prim.injEq, TermPrimType.entity.injEq, exists_eq', imp_self]
  · simp only [Bool.false_eq_true, false_implies]

theorem isOptionEntityType_implies_option_entity_type {ty : TermType} :
  ty.isOptionEntityType → ∃ ety, ty = .option (.entity ety)
:= by
  simp only [TermType.isOptionEntityType]
  split
  · simp only [TermType.option.injEq, TermType.prim.injEq, TermPrimType.entity.injEq, exists_eq', imp_self]
  · simp only [Bool.false_eq_true, false_implies]

private theorem typeOf_ite_simplify_option {g t : Term} {ty : TermType} :
  t.typeOf = .option ty →
  (ite.simplify g (Term.none ty) t).typeOf = ty.option
:= by
  intro hty
  simp only [ite.simplify, Bool.or_eq_true, decide_eq_true_eq]
  split
  · simp only [Term.typeOf]
  · split
    · exact hty
    · split <;> simp [typeOf_bool, Term.typeOf] at *

theorem typeOf_ifSome_option {g t : Term} {ty : TermType} :
  t.typeOf = .option ty →
  (ifSome g t).typeOf = .option ty
:= by
  intro hty
  simp only [ifSome, hty, Factory.ite, noneOf]
  exact typeOf_ite_simplify_option hty

theorem typeOf_ifAllSome_option_type {gs : List Term} {t : Term} {ty : TermType} :
  t.typeOf = .option ty →
  (ifAllSome gs t).typeOf = .option ty
:= by
  intro hty
  simp only [ifAllSome, hty, Factory.ite, noneOf]
  exact typeOf_ite_simplify_option hty

end Cedar.Thm
