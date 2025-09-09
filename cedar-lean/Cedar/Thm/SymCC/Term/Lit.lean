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
import Cedar.Thm.SymCC.Term.TypeOf

/-!
# Properties of literal terms

This file proves basic lemmas about literal terms
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem lit_term_set_empty (ty : TermType) :
  Term.isLiteral (Term.set (Set.mk []) ty)
:= by
  unfold Term.isLiteral
  simp only [List.attach_def, List.pmap, List.all_nil]

theorem lit_term_set_implies_lit_elt {s : Set Term} {ty : TermType} {t : Term} :
  (Term.set s ty).isLiteral → t ∈ s → t.isLiteral
:= by
  intro h₁ h₂
  unfold Term.isLiteral at h₁
  simp only [List.attach_def, List.all_pmap_subtype Term.isLiteral, List.all_eq_true] at h₁
  rw [← Set.in_list_iff_in_set] at h₂
  simp only [Set.elts] at h₂
  exact h₁ t h₂

theorem lit_term_set_impliedBy_lit_elts {s : Set Term} {ty : TermType} :
  (∀ t ∈ s, t.isLiteral) → (Term.set s ty).isLiteral
:= by
  intro h₁
  unfold Term.isLiteral
  simp only [List.attach_def, List.all_pmap_subtype Term.isLiteral, List.all_eq_true]
  intro t h₂
  rw [Set.in_list_iff_in_set] at h₂
  exact h₁ t h₂

theorem lit_term_set_cons {hd : Term} {tl : List Term} {ty : TermType} :
  (Term.set (Set.mk (hd :: tl)) ty).isLiteral →
  (hd.isLiteral ∧ (Term.set (Set.mk tl) ty).isLiteral)
:= by
  intro h₁
  have h₂ := Set.mem_cons_self hd tl
  simp only [lit_term_set_implies_lit_elt h₁ h₂, true_and]
  apply lit_term_set_impliedBy_lit_elts
  intro t h₃
  rw [← Set.in_list_iff_in_mk] at h₃
  replace h₃ := List.mem_cons_of_mem hd h₃
  rw [Set.in_list_iff_in_set] at h₃
  exact lit_term_set_implies_lit_elt h₁ h₃

theorem lit_term_record_implies_lit_value {r : Map Attr Term} {a : Attr} {t : Term} :
  Term.isLiteral (Term.record r) → (a, t) ∈ r.1 → t.isLiteral
:= by
  intro h₁ h₂
  unfold Term.isLiteral at h₁
  simp only [List.attach₃, List.all_pmap_subtype (λ (x : Attr × Term) => Term.isLiteral x.snd), List.all_eq_true] at h₁
  exact h₁ (a, t) h₂

theorem lit_term_implies_lit_some {t : Term} :
  t.isLiteral → (Term.some t).isLiteral
:= by simp [Term.isLiteral]

theorem lit_term_some_implies_lit {t : Term} :
  (Term.some t).isLiteral → t.isLiteral
:= by simp [Term.isLiteral]

theorem term_prim_is_lit {p : TermPrim} :
  (Term.prim p).isLiteral
:= by simp only [Term.isLiteral]

theorem wfl_of_type_bool_is_bool {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .bool →
  ∃ b, t = .prim (.bool b)
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, Bool.false_eq_true] at h₃} <;>
  try {simp only [Term.typeOf, reduceCtorEq] at h₂}
  case prim p =>
    cases p <;>
    simp only [
      Term.typeOf, TermPrim.typeOf, TermType.bool,
      TermType.bitvec, TermType.string, TermType.entity,
      TermType.ext, TermType.prim.injEq, reduceCtorEq] at h₂
    case bool b =>
      exists b
    case ext =>
      split at h₂ <;>
      rename_i heq <;>
      simp only [TermPrim.ext.injEq, reduceCtorEq] at heq <;>
      simp only [TermType.prim.injEq, reduceCtorEq] at h₂
  case record r =>
    have ⟨_, h₄⟩ := @typeOf_term_record_is_record_type r
    simp only [h₂, reduceCtorEq] at h₄

theorem wfl_of_type_bool_is_true_or_false {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .bool →
  t = .prim (.bool true) ∨ t = .prim (.bool false)
:= by
  intro h₁ h₂
  have ⟨b, h₃⟩ := wfl_of_type_bool_is_bool h₁ h₂
  subst h₃
  cases b <;>
  simp only [Term.prim.injEq, TermPrim.bool.injEq, or_true, or_false, reduceCtorEq]

theorem wfl_of_type_bitvec_is_bitvec {εs : SymEntities} {t : Term} {n : Nat} :
  t.WellFormedLiteral εs →
  t.typeOf = .bitvec n →
  ∃ (bv : BitVec n), t = .prim (.bitvec bv)
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃} <;>
  try {simp only [Term.typeOf, reduceCtorEq] at h₂}
  case prim p =>
    cases p <;>
    simp only [
      Term.typeOf, TermPrim.typeOf, TermType.bool,
      TermType.bitvec, TermType.string, TermType.entity,
      TermType.ext, TermType.prim.injEq, reduceCtorEq] at h₂
    case bitvec m bv =>
      simp only [BitVec.width, TermPrimType.bitvec.injEq] at h₂
      subst h₂
      exists bv
    case ext =>
      split at h₂ <;>
      rename_i heq <;>
      simp only [TermPrim.ext.injEq, reduceCtorEq] at heq <;>
      simp only [TermType.prim.injEq, reduceCtorEq] at h₂
  case record r =>
    have ⟨_, h₄⟩ := @typeOf_term_record_is_record_type r
    simp only [h₂, reduceCtorEq] at h₄

theorem wfl_of_type_datetime_is_datetime {εs : SymEntities} {t : Term}:
  t.WellFormedLiteral εs →
  t.typeOf = .ext .datetime →
  ∃ (d : Cedar.Spec.Ext.Datetime), t = .prim (.ext (.datetime d))
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃} <;>
  try {simp only [Term.typeOf, reduceCtorEq] at h₂}
  case prim p =>
    cases p <;>
    simp only [
      Term.typeOf, TermPrim.typeOf, TermType.bool,
      TermType.bitvec, TermType.string, TermType.entity,
      TermType.ext, TermType.prim.injEq, reduceCtorEq] at h₂
    case ext =>
      split at h₂ <;>
      rename_i heq <;> simp at *
      rename_i dt
      exists dt
  case record r =>
    have ⟨_, h₄⟩ := @typeOf_term_record_is_record_type r
    simp only [h₂, reduceCtorEq] at h₄

theorem wfl_of_type_duration_is_duration {εs : SymEntities} {t : Term}:
  t.WellFormedLiteral εs →
  t.typeOf = .ext .duration →
  ∃ (d : Duration), t = .prim (.ext (.duration d))
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃} <;>
  try {simp only [Term.typeOf, reduceCtorEq] at h₂}
  case prim p =>
    cases p <;>
    simp only [
      Term.typeOf, TermPrim.typeOf, TermType.bool,
      TermType.bitvec, TermType.string, TermType.entity,
      TermType.ext, TermType.prim.injEq, reduceCtorEq] at h₂
    case ext =>
      split at h₂ <;>
      rename_i heq <;> simp at *
      rename_i dur
      exists dur
  case record r =>
    have ⟨_, h₄⟩ := @typeOf_term_record_is_record_type r
    simp only [h₂, reduceCtorEq] at h₄

theorem wfl_of_type_string_is_string {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .string →
  ∃ (s : String), t = .prim (.string s)
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃} <;>
  try {simp only [Term.typeOf, reduceCtorEq] at h₂}
  case prim p =>
    cases p <;>
    simp only [
      Term.typeOf, TermPrim.typeOf, TermType.bool,
      TermType.bitvec, TermType.string, TermType.entity,
      TermType.ext, TermType.prim.injEq, reduceCtorEq] at h₂
    case string s =>
      exists s
    case ext =>
      split at h₂ <;>
      rename_i heq <;>
      simp only [TermPrim.ext.injEq, reduceCtorEq] at heq <;>
      simp only [TermType.prim.injEq, reduceCtorEq] at h₂
  case record r =>
    have ⟨_, h₄⟩ := @typeOf_term_record_is_record_type r
    simp only [h₂, reduceCtorEq] at h₄

theorem wfl_of_type_entity_is_entity {εs : SymEntities} {t : Term} {ety : EntityType} :
  t.WellFormedLiteral εs →
  t.typeOf = .entity ety →
  ∃ (uid : EntityUID), t = .prim (.entity uid) ∧ uid.ty = ety
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃} <;>
  try {simp only [Term.typeOf, reduceCtorEq] at h₂}
  case prim p =>
    cases p <;>
    simp only [
      Term.typeOf, TermPrim.typeOf, TermType.bool,
      TermType.bitvec, TermType.string, TermType.entity,
      TermType.ext, TermType.prim.injEq, reduceCtorEq] at h₂
    case entity uid =>
      exists uid
      simp only [TermPrimType.entity.injEq] at h₂
      simp only [h₂, and_self]
    case ext =>
      split at h₂ <;>
      rename_i heq <;>
      simp only [TermPrim.ext.injEq, reduceCtorEq] at heq <;>
      simp only [TermType.prim.injEq, reduceCtorEq] at h₂
  case record r =>
    have ⟨_, h₄⟩ := @typeOf_term_record_is_record_type r
    simp only [h₂, reduceCtorEq] at h₄

theorem wfl_of_type_set_is_set {εs : SymEntities} {t : Term} {ty : TermType} :
  t.WellFormedLiteral εs →
  t.typeOf = .set ty →
  ∃ (s : Set Term), t = .set s ty
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃} <;>
  try {simp only [Term.typeOf, reduceCtorEq] at h₂}
  case prim p =>
    cases p <;>
    simp only [
      Term.typeOf, TermPrim.typeOf, TermType.bool,
      TermType.bitvec, TermType.string, TermType.entity,
      TermType.ext, reduceCtorEq] at h₂
    case ext x =>
      cases x <;>
      rename_i x <;>
      simp only [reduceCtorEq] at h₂
  case set s _ =>
    simp [Term.typeOf] at h₂
    subst h₂
    exists s
  case record r =>
    have ⟨_, h₄⟩ := @typeOf_term_record_is_record_type r
    simp only [h₂, reduceCtorEq] at h₄

theorem wfl_of_type_record_is_record {εs : SymEntities} {t : Term} {rty : Map Attr TermType} :
  t.WellFormedLiteral εs →
  t.typeOf = .record rty →
  ∃ (r : Map Attr Term), t = .record r
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃} <;>
  try {simp only [Term.typeOf, reduceCtorEq] at h₂}
  case prim p =>
    cases p <;>
    simp only [Term.typeOf, TermPrim.typeOf, reduceCtorEq] at h₂
    split at h₂ <;> simp only [reduceCtorEq] at h₂
  case record r => exists r

local macro "simp_wfl_of_type_ext" t:term : tactic => do
 `(tactic| (
    intro h₁ h₂
    replace ⟨h₁, h₃⟩ := h₁
    cases $t:term <;>
    try {simp only [Term.isLiteral, reduceCtorEq] at h₃} <;>
    try {simp only [Term.typeOf, reduceCtorEq] at h₂}
    case prim p =>
      cases p <;>
      simp only [
        Term.typeOf, TermPrim.typeOf, TermType.bool,
        TermType.bitvec, TermType.string, TermType.entity,
        TermType.ext, TermType.prim.injEq, reduceCtorEq] at h₂
      case ext x =>
        cases x <;>
        rename_i x <;>
        simp only [TermType.ext, TermType.prim.injEq, TermPrimType.ext.injEq, reduceCtorEq] at h₂
        exists x
    case record r =>
      have ⟨_, h₄⟩ := @typeOf_term_record_is_record_type r
      simp only [h₂, reduceCtorEq] at h₄
    ))

theorem wfl_of_type_ext_decimal_is_ext_decimal {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .ext .decimal →
  ∃ (d : Ext.Decimal), t = .prim (.ext (.decimal d))
:= by simp_wfl_of_type_ext t

theorem wfl_of_type_ext_ipaddr_is_ext_ipaddr {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .ext .ipAddr →
  ∃ (ip : IPAddr), t = .prim (.ext (.ipaddr ip))
:= by simp_wfl_of_type_ext t

theorem wfl_of_type_ext_datetime_is_ext_datetime {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .ext .datetime →
  ∃ (d : Ext.Datetime), t = .prim (.ext (.datetime d))
:= by simp_wfl_of_type_ext t

theorem wfl_of_type_ext_duration_is_ext_duration {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .ext .duration →
  ∃ (d : Ext.Datetime.Duration), t = .prim (.ext (.duration d))
:= by simp_wfl_of_type_ext t

theorem wfl_of_type_option_is_option {εs : SymEntities} {t : Term} {ty : TermType} :
  t.WellFormedLiteral εs →
  t.typeOf = .option ty →
  t = .none ty ∨ ∃ t', t = .some t' ∧ t'.typeOf = ty
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃} <;>
  try {simp only [Term.typeOf, reduceCtorEq] at h₂}
  case none =>
    simp only [Term.typeOf, TermType.option.injEq] at h₂
    simp only [h₂, reduceCtorEq, false_and, exists_const, or_false]
  case some t' =>
    simp only [Term.typeOf, TermType.option.injEq] at h₂
    simp only [← h₂, Term.some.injEq, exists_eq_left', or_true]
  case prim p =>
    cases p <;>
    simp [Term.typeOf, TermPrim.typeOf] at h₂
    split at h₂ <;>
    simp only [reduceCtorEq] at h₂
  case record r =>
    have ⟨_, h₄⟩ := @typeOf_term_record_is_record_type r
    simp only [h₂, reduceCtorEq] at h₄

theorem wfl_of_prim_type_is_prim {εs : SymEntities} {t : Term} {pty : TermPrimType} :
  t.WellFormedLiteral εs →
  t.typeOf = .prim pty →
  ∃ (p : TermPrim), t = .prim p
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃} <;>
  try {simp only [Term.typeOf, reduceCtorEq] at h₂}
  case prim p =>
    exists p
  case record r =>
    have ⟨_, h₄⟩ := @typeOf_term_record_is_record_type r
    simp only [h₂, reduceCtorEq] at h₄

end Cedar.Thm
