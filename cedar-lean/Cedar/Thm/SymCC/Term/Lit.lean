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

public import Cedar.SymCC.Env
public import Cedar.SymCC.Term
public import Cedar.Thm.Data
public import Cedar.Thm.SymCC.Data
import Cedar.Thm.SymCC.Term.TypeOf

/-!
# Properties of literal terms

This file proves basic lemmas about literal terms
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

@[simp]
public theorem isLiteral_empty (eltsTy : TermType) :
  Term.isLiteral (.set Set.empty eltsTy)
:= by simp [Term.isLiteral]

public theorem lit_term_set_implies_lit_elt {s : Set Term} {ty : TermType} {t : Term} :
  (Term.set s ty).isLiteral → t ∈ s → t.isLiteral
:= by
  simp only [Term.isLiteral, Set.all₁_eq_all, Set.all_eq_true]
  intro h₁ h₂
  exact h₁ t h₂

public theorem lit_term_set_impliedBy_lit_elts {s : Set Term} {ty : TermType} :
  (∀ t ∈ s, t.isLiteral) → (Term.set s ty).isLiteral
:= by simp [Term.isLiteral]

public theorem isLiteral_set_cons {hd : Term} {tl : List Term} {ty : TermType} :
  (Term.set (Set.mk (hd :: tl)) ty).isLiteral →
  (hd.isLiteral ∧ (Term.set (Set.mk tl) ty).isLiteral)
:= by
  intro h₁
  have h₂ := Set.mem_mk_hd hd tl
  simp only [lit_term_set_implies_lit_elt h₁ h₂, true_and]
  apply lit_term_set_impliedBy_lit_elts
  intro t h₃
  rw [← Set.mem_set_iff_mem_mk] at h₃
  replace h₃ := List.mem_cons_of_mem hd h₃
  rw [Set.mem_elts_iff_mem_set] at h₃
  exact lit_term_set_implies_lit_elt h₁ h₃

public theorem lit_term_record_implies_lit_value {r : Map Attr Term} {a : Attr} {t : Term} :
  Term.isLiteral (Term.record r) → (a, t) ∈ r.toList → t.isLiteral
:= by
  simp only [Term.isLiteral]
  rw [List.all_attach₂_snd]
  simp only [List.all_eq_true, Prod.forall]
  intro h₁ h₂
  exact h₁ a t h₂

public theorem isLiteral_record_mapOnValues {m : Map Attr β} {f : β → Term} :
  (Term.isLiteral (.record (m.mapOnValues f)) ↔ ∀ v ∈ m.values, (f v).isLiteral)
:= by
  constructor
  · intro h₁ b hb
    have ⟨a, ha⟩ := Map.in_values_exists_key hb
    apply lit_term_record_implies_lit_value h₁ (a := a)
    exact Map.in_toList_in_mapOnValues ha
  · simp only [Term.isLiteral, List.all_attach₂_snd, List.all_eq_true, Prod.forall]
    intro h₁ a t h₂
    replace ⟨b, hb, h₂⟩ := Map.in_mapOnValues_in_toList' h₂
    subst t
    apply h₁ b
    exact Map.in_list_in_values h₂

@[simp]
public theorem isLiteral_some {t : Term} :
  (Term.some t).isLiteral ↔ t.isLiteral
:= by simp [Term.isLiteral]

@[simp]
public theorem isLiteral_none {tty : TermType} :
  (Term.none tty).isLiteral = true
:= by simp [Term.isLiteral]

@[simp]
public theorem isLiteral_prim {p : TermPrim} :
  (Term.prim p).isLiteral
:= by simp only [Term.isLiteral]

public theorem wfl_of_type_bool_is_bool {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .bool →
  ∃ b, t = .prim (.bool b)
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, Bool.false_eq_true] at h₃}
  case prim p =>
    cases p
    case bool b => exists b
    case ext ext => cases ext <;> simp at h₂
    all_goals simp at h₂
  all_goals simp at h₂

public theorem wfl_of_type_bool_is_true_or_false {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .bool →
  t = .prim (.bool true) ∨ t = .prim (.bool false)
:= by
  intro h₁ h₂
  have ⟨b, h₃⟩ := wfl_of_type_bool_is_bool h₁ h₂
  simp [h₃]

public theorem wfl_of_type_bitvec_is_bitvec {εs : SymEntities} {t : Term} {n : Nat} :
  t.WellFormedLiteral εs →
  t.typeOf = .bitvec n →
  ∃ (bv : BitVec n), t = .prim (.bitvec bv)
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃}
  case prim p =>
    cases p
    case bitvec m bv =>
      simp only [typeOf_bv, TermType.prim.injEq, TermPrimType.bitvec.injEq] at h₂
      subst h₂
      exists bv
    case ext ext => cases ext <;> simp at h₂
    all_goals simp at h₂
  all_goals simp at h₂

public theorem wfl_of_type_datetime_is_datetime {εs : SymEntities} {t : Term}:
  t.WellFormedLiteral εs →
  t.typeOf = .ext .datetime →
  ∃ (d : Cedar.Spec.Ext.Datetime), t = .prim (.ext (.datetime d))
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃}
  case prim p =>
    cases p
    case ext ext => cases ext <;> simp at h₂ ⊢
    all_goals simp at h₂
  all_goals simp at h₂

public theorem wfl_of_type_duration_is_duration {εs : SymEntities} {t : Term}:
  t.WellFormedLiteral εs →
  t.typeOf = .ext .duration →
  ∃ (d : Duration), t = .prim (.ext (.duration d))
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃}
  case prim p =>
    cases p
    case ext ext => cases ext <;> simp at h₂ ⊢
    all_goals simp at h₂
  all_goals simp at h₂

public theorem wfl_of_type_string_is_string {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .string →
  ∃ (s : String), t = .prim (.string s)
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃}
  case prim p =>
    cases p
    case string s => exists s
    case ext ext => cases ext <;> simp at h₂
    all_goals simp at h₂
  all_goals simp at h₂

public theorem wfl_of_type_entity_is_entity {εs : SymEntities} {t : Term} {ety : EntityType} :
  t.WellFormedLiteral εs →
  t.typeOf = .entity ety →
  ∃ (uid : EntityUID), t = .prim (.entity uid) ∧ uid.ty = ety
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃}
  case prim p =>
    cases p
    case entity uid =>
      exists uid
      simp only [typeOf_term_prim_entity, TermType.prim.injEq, TermPrimType.entity.injEq] at h₂
      simp only [h₂, and_self]
    case ext ext => cases ext <;> simp at h₂
    all_goals simp at h₂
  all_goals simp at h₂

public theorem wfl_of_type_set_is_set {εs : SymEntities} {t : Term} {ty : TermType} :
  t.WellFormedLiteral εs →
  t.typeOf = .set ty →
  ∃ (s : Set Term), t = .set s ty
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃}
  case prim p =>
    cases p
    case ext ext => cases ext <;> simp at h₂
    all_goals simp at h₂
  case set s _ =>
    simp only [typeOf_term_set, TermType.set.injEq] at h₂
    subst h₂
    exists s
  all_goals simp at h₂

public theorem wfl_of_type_record_is_record {εs : SymEntities} {t : Term} {rty : Map Attr TermType} :
  t.WellFormedLiteral εs →
  t.typeOf = .record rty →
  ∃ (r : Map Attr Term), t = .record r
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃}
  case prim p =>
    cases p
    case ext ext => cases ext <;> simp at h₂
    all_goals simp at h₂
  case record r => exists r
  all_goals simp at h₂

local macro "simp_wfl_of_type_ext" t:term : tactic => do
 `(tactic| (
    intro h₁ h₂
    replace ⟨h₁, h₃⟩ := h₁
    cases $t:term <;>
    try {simp only [Term.isLiteral, reduceCtorEq] at h₃}
    case prim p =>
      cases p
      case ext ext =>
        cases ext <;> try (rename_i val ; exists val)
        all_goals simp at h₂
      all_goals simp at h₂
    all_goals simp at h₂
    ))

public theorem wfl_of_type_ext_decimal_is_ext_decimal {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .ext .decimal →
  ∃ (d : Ext.Decimal), t = .prim (.ext (.decimal d))
:= by simp_wfl_of_type_ext t

public theorem wfl_of_type_ext_ipaddr_is_ext_ipaddr {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .ext .ipAddr →
  ∃ (ip : IPAddr), t = .prim (.ext (.ipaddr ip))
:= by simp_wfl_of_type_ext t

public theorem wfl_of_type_ext_datetime_is_ext_datetime {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .ext .datetime →
  ∃ (d : Ext.Datetime), t = .prim (.ext (.datetime d))
:= by simp_wfl_of_type_ext t

public theorem wfl_of_type_ext_duration_is_ext_duration {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs →
  t.typeOf = .ext .duration →
  ∃ (d : Ext.Datetime.Duration), t = .prim (.ext (.duration d))
:= by simp_wfl_of_type_ext t

public theorem wfl_of_type_option_is_option {εs : SymEntities} {t : Term} {ty : TermType} :
  t.WellFormedLiteral εs →
  t.typeOf = .option ty →
  t = .none ty ∨ ∃ t', t = .some t' ∧ t'.typeOf = ty
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃}
  case none => simpa using h₂
  case some t' => simpa using h₂
  case prim p =>
    cases p
    case ext ext => cases ext <;> simp at h₂
    all_goals simp at h₂
  all_goals simp at h₂

public theorem wfl_of_prim_type_is_prim {εs : SymEntities} {t : Term} {pty : TermPrimType} :
  t.WellFormedLiteral εs →
  t.typeOf = .prim pty →
  ∃ (p : TermPrim), t = .prim p
:= by
  intro h₁ h₂
  replace ⟨h₁, h₃⟩ := h₁
  cases t <;>
  try {simp only [Term.isLiteral, reduceCtorEq] at h₃}
  case prim p =>
    exists p
  all_goals simp at h₂

end Cedar.Thm
