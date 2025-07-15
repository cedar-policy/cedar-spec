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
import Cedar.Thm.SymCC.Tactics
import Cedar.Thm.SymCC.Term.PE

/-!
# Properties of the `Same` predicate on Terms

This file contains lemmas about the `Same` predicate on Terms.
-/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem same_results_implies_exists_outcome {res : Spec.Result Value} {t : Term} :
  res ∼ t → ∃ (o : Outcome Value), res ∼ o ∧ o ∼ t
:= by
  simp [Same.same, SameResults, Spec.SameOutcomes, SymCC.SameOutcomes]
  intro h₁
  cases t <;> cases res <;> simp at h₁
  case none.error => exists (.error ())
  case some.ok v  => exists (.ok v)

theorem same_outcomes_implies_eq {o₁ o₂ : Outcome Value} {t : Term} :
  o₁ ∼ t → o₂ ∼ t → o₁ = o₂
:= by
  intros h₁ h₂
  simp [Same.same, SymCC.SameOutcomes] at h₁ h₂
  cases t <;> try { simp at h₁ }
  case none =>
    cases o₁ <;> simp at h₁
    cases o₂ <;> simp at h₂
    rfl
  case some t' =>
    cases o₁ <;> simp at h₁
    cases o₂ <;> simp at h₂
    simp only [SameValues] at h₁ h₂
    simp only [h₁, Option.some.injEq] at h₂
    simp only [h₂, Except.ok.injEq]

theorem same_error_implies {e : Spec.Error} {t : Term} :
  (Except.error e : Spec.Result Value) ∼ t →
  (¬ e = .entityDoesNotExist) ∧
  (∃ ty, t = Term.none ty)
:= by
  intro h₁
  simp only [Same.same, SameResults, ne_eq] at h₁
  split at h₁ <;> try { simp at * }
  rename_i ty heq
  simp only [Except.error.injEq] at heq
  subst heq
  simp only [h₁, not_false_eq_true, Term.none.injEq, exists_eq', and_self]

theorem same_error_implies_ifSome_error {e : Spec.Error} {t₁ t₂ : Term} {ty₂ : TermType} :
  (Except.error e : Spec.Result Value) ∼ t₁ →
  t₂.typeOf = .option ty₂ →
  (Except.error e : Spec.Result Value) ∼ ifSome t₁ t₂
:= by
  intro he hty
  have ⟨_, ty₁, ht⟩ := same_error_implies he
  subst ht
  simp only [pe_ifSome_none hty]
  simp only [Same.same, SameResults, ne_eq] at *
  exact he

theorem same_error_implies_ifAllSome_error {e : Spec.Error} {ts : List Term} {t₁ t₂ : Term} {ty₂ : TermType} :
  (Except.error e : Spec.Result Value) ∼ t₁ →
  t₁ ∈ ts →
  t₂.typeOf = .option ty₂ →
  (Except.error e : Spec.Result Value) ∼ ifAllSome ts t₂
:= by
  intro he ht hty
  have ⟨hne, ty₁, ht'⟩ := same_error_implies he
  subst ht'
  rw [pe_ifAllSome_none ht hty]
  simp only [Same.same, SameResults, hne, ne_eq, not_false_eq_true]

theorem same_error_implied_by {e : Spec.Error} {ty : TermType} :
  ¬e = Error.entityDoesNotExist →
  (Except.error e : Spec.Result Value) ∼ Term.none ty
:= by
  intro h₁ ; simp [Same.same, SameResults, h₁]

theorem same_ok_implies {v : Value} {t : Term} :
  (Except.ok v : Spec.Result Value) ∼ t →
  ∃ t', t = .some t' ∧ v ∼ t'
:= by
  intro h
  simp only [Same.same, SameResults] at h
  split at h <;> try (contradiction)
  rename_i t' heq
  simp only [Except.ok.injEq] at heq
  subst heq
  exists t'

theorem same_ok_some_implies {v : Value} {t : Term} :
  (Except.ok v : Spec.Result Value) ∼ (Term.some t) → v ∼ t
:= by
  intro h
  replace ⟨t', heq, h⟩ := same_ok_implies h
  simp only [Term.some.injEq] at heq
  subst heq
  exact h

theorem same_ok_some_iff {v : Value} {t : Term} :
  (Except.ok v : Spec.Result Value) ∼ (Term.some t) ↔ v ∼ t
:= by
  constructor
  · exact same_ok_some_implies
  · intro h
    simp only [Same.same, SameResults]
    exact h

theorem same_some_implies_ok {r : Spec.Result Value} {t : Term} :
  r ∼ (Term.some t) →
  ∃ v, r = .ok v ∧ v ∼ t
:= by
  intro h
  simp only [Same.same, SameResults] at h
  split at h <;> try (contradiction)
  rename_i v t' heq
  simp only [Term.some.injEq] at heq
  subst heq
  exists v

theorem same_values_def {v : Value} {t : Term} :
  v ∼ t ↔ t.value? = .some v
:= by simp only [Same.same, SameValues]

theorem same_value_implies_same {v : Value} {t : Term} :
  SameValues v t → v ∼ t
:= by
  intro h₁
  simp only [Same.same, h₁]

theorem same_implies_same_value {v : Value} {t : Term} :
  v ∼ t → SameValues v t
:= by simp only [Same.same, imp_self]

theorem same_value_implies_lit {v : Value} {t : Term} :
  v ∼ t → t.isLiteral
:= by
  intro h₁
  simp only [Same.same, SameValues] at h₁
  match t with
  | .var _
  | .none _
  | .some _
  | .app _ _ _ => simp [Term.value?] at h₁
  | .prim p    => simp [Term.isLiteral]
  | .set s _   =>
    unfold Term.isLiteral
    simp only [List.attach_def, List.all_pmap_subtype Term.isLiteral, List.all_eq_true]
    intro x h₂
    unfold Term.value? at h₁
    simp only [List.mapM₁_eq_mapM Term.value?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h₁
    replace ⟨vs, h₁, _⟩ := h₁
    rw [← List.mapM'_eq_mapM] at h₁
    replace ⟨v', _, h₁⟩ := List.mapM'_some_implies_all_some h₁ x h₂
    have _ := Set.sizeOf_lt_of_mem h₂ -- termination
    exact same_value_implies_lit (same_value_implies_same h₁)
  | .record r  =>
    unfold Term.isLiteral
    simp only [List.attach₃, List.all_pmap_subtype (λ (x : Attr × Term) => Term.isLiteral x.snd),
      List.all_eq_true]
    intro x h₂
    unfold Term.value? at h₁
    simp only [List.mapM₂, List.attach₂,
      List.mapM_pmap_subtype (λ (x : Attr × Term) => Term.value?.attrValue? x.fst x.snd),
      Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
    replace ⟨avs, h₁, _⟩ := h₁
    rw [← List.mapM'_eq_mapM] at h₁
    replace ⟨av', _, h₁⟩ := List.mapM'_some_implies_all_some h₁ x h₂
    have _ := Map.sizeOf_lt_of_value h₂ -- termination
    unfold Term.value?.attrValue? at h₁
    split at h₁
    case h_1 t' heq =>
      simp only [heq]
      cases hv : Term.value? t' <;>
      simp [hv, Option.bind_none_fun, Option.bind_some_fun, Option.some.injEq] at h₁
      simp only [Term.isLiteral]
      rename_i v'
      have _ : sizeOf t' < sizeOf x.snd := by simp only [heq, Term.some.sizeOf_spec]; omega -- termination
      exact same_value_implies_lit (same_value_implies_same hv)
    case h_2 heq =>
      simp [heq, Term.isLiteral]
    case h_3 =>
      cases hv : Term.value? x.snd <;>
      simp [hv, Option.bind_none_fun, Option.bind_some_fun, Option.some.injEq] at h₁
      rename_i v'
      exact same_value_implies_lit (same_value_implies_same hv)
termination_by sizeOf t
decreasing_by all_goals (simp_wf ; omega)

theorem same_ok_value_implies_lit {v : Value} {t : Term} :
  (Except.ok v : Spec.Result Value) ∼ t → t.isLiteral
:= by
  intro h₁
  simp only [Same.same, SameResults, ne_eq] at h₁
  split at h₁ <;>
  simp only [Except.ok.injEq, false_implies, forall_const, implies_true, reduceCtorEq] at *
  rename_i heq ; subst heq
  simp only [Term.isLiteral]
  exact same_value_implies_lit (same_value_implies_same h₁)

theorem same_bool_term_implies {v : Value} {b : Bool} :
  v ∼ (Term.prim (TermPrim.bool b)) →
  v = .prim (.bool b)
:= by
  intro h₁
  simp only [Same.same, SameValues, Term.value?, TermPrim.value?, Option.some.injEq] at h₁
  simp [h₁]

theorem same_ok_bool_term_implies {v : Value} {b : Bool} :
  (Except.ok v : Spec.Result Value) ∼ (Term.some (Term.prim (TermPrim.bool b))) →
  v = .prim (.bool b)
:= by
  intro h₁
  simp only [Same.same, SameResults] at h₁
  exact same_bool_term_implies h₁

local macro "simp_same_prim_implies" prim_injEq:ident : tactic => do
  `(tactic | (
    intro h₁
    simp only [Same.same, SameValues] at h₁
    unfold Term.value? at h₁
    split at h₁ <;>
    simp only [TermPrim.value?, Option.pure_def, Option.bind_eq_bind, reduceCtorEq] at h₁
    split at h₁ <;>
    try simp only [Option.some.injEq, Value.prim.injEq, $prim_injEq:ident, reduceCtorEq] at h₁
    any_goals simp only [h₁]
    all_goals {
      simp only [BitVec.int64?, Option.bind] at h₁
      split at h₁ <;>
      simp only [Option.bind_some, Option.some.injEq, Value.prim.injEq, Option.bind_none, reduceCtorEq] at h₁
    }
  ))

theorem same_bool_implies {b : Bool} {t : Term} :
  Value.prim (Prim.bool b) ∼ t →
  t = .prim (.bool b)
:= by simp_same_prim_implies Prim.bool.injEq

theorem same_ok_bool_implies {b : Bool} {t : Term} :
  (Except.ok (Value.prim (Prim.bool b)) : Spec.Result Value) ∼ t →
  t = .some (.prim (.bool b))
:= by
  intro h₁
  simp only [Same.same, SameResults, ne_eq] at h₁
  split at h₁ <;> simp at *
  rename_i heq ; subst heq
  exact same_bool_implies h₁

theorem same_bool {b : Bool} :
  Value.prim (Prim.bool b) ∼ Term.prim (TermPrim.bool b)
:= by
  simp only [Same.same, SameValues, Term.value?, TermPrim.value?]

theorem same_ok_bool {b : Bool} :
  (Except.ok (Value.prim (Prim.bool b)) : Spec.Result Value) ∼ Term.some (Term.prim (TermPrim.bool b))
:= by
  simp only [Same.same, SameResults, SameValues, Term.value?, TermPrim.value?]

theorem same_ok_bool_iff {b₁ b₂ : Bool} :
  b₁ = b₂ ↔
  (Except.ok (Value.prim (Prim.bool b₁)) : Spec.Result Value) ∼ Term.some (Term.prim (TermPrim.bool b₂))
:= by
  constructor
  · intro h
    subst h
    exact same_ok_bool
  · intro h
    simp only [Same.same, SameResults, SameValues, Term.value?, TermPrim.value?, Option.some.injEq,
      Value.prim.injEq, Prim.bool.injEq] at h
    simp only [h]

theorem same_set_term_implies {v : Value} {ts : Set Term} {ty : TermType} :
  v ∼ (Term.set ts ty) →
  ∃ vs, v = .set vs ∧ (Term.set ts ty).value? = vs
:= by
  intro h₁
  simp only [Same.same, SameValues] at h₁
  unfold Term.value? at h₁
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
  have ⟨vs', h₁⟩ := h₁
  exists (Set.make vs')
  simp only [h₁, true_and]
  unfold Term.value?
  simp only [h₁, Option.bind_some_fun]

theorem same_set_implies {vs : Set Value} {t : Term} {ty : TermType} :
  (Value.set vs) ∼ t → t.typeOf = .set ty →
  ∃ ts, t = .set ts ty ∧ (Term.set ts ty).value? = vs
:= by
  intro h₁ hty
  simp only [Same.same, SameValues] at h₁
  unfold Term.value? at h₁
  split at h₁
  case h_1 =>
    simp only [TermPrim.value?, Option.pure_def, Option.bind_eq_bind] at h₁ <;>
    split at h₁ <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, and_false, exists_const, reduceCtorEq] at h₁
  case h_2 =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Value.set.injEq] at h₁
    simp only [Term.typeOf, TermType.set.injEq] at hty
    subst hty
    rename_i ts _
    exists (Set.mk ts)
    simp only [Term.value?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Value.set.injEq, h₁, and_self]
  case h_3 r =>
    have ⟨_, h⟩ := @typeOf_term_record_is_record_type (Map.mk r)
    simp only [h, reduceCtorEq] at hty
  case h_4 =>
    simp only [reduceCtorEq] at h₁

theorem same_record_term_implies {v : Value} {rt : Map Attr Term} :
  SameValues v (Term.record rt) →
  ∃ rv, v = .record rv ∧ (Term.record rt).value? = rv
:= by
  rw [SameValues]
  intro h₁
  have h₂ := h₁
  unfold Term.value? at h₁
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
  have ⟨avs, h₁⟩ := h₁
  exists (Map.mk (List.filterMap (fun x => Option.map (Prod.mk x.fst) x.snd) avs))
  simp only [h₁, h₂, and_self]

theorem same_record_implies {avs : Map Attr Value} {t : Term} {rty : Map Attr TermType} :
  (Value.record avs) ∼ t → t.typeOf = .record rty →
  ∃ ats, t = .record ats ∧ (Term.record ats).value? = Value.record avs
:= by
  intro h₁ hty
  simp only [Same.same, SameValues] at h₁
  unfold Term.value? at h₁
  split at h₁
  case h_1 =>
    simp only [TermPrim.value?, Option.pure_def, Option.bind_eq_bind] at h₁ <;>
    split at h₁ <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, and_false, exists_const, reduceCtorEq] at h₁
  case h_2 | h_4 =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, and_false,
      exists_const, reduceCtorEq] at h₁
  case h_3 =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Value.record.injEq] at h₁
    rename_i ats
    exists (Map.mk ats)
    simp only [Term.value?, h₁, true_and, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Value.record.injEq]

theorem bool_value? {b : Bool} :
  (Term.prim (.bool b)).value? = some (Value.prim (.bool b))
:= by simp only [Term.value?, TermPrim.value?]

theorem entity_value? {uid : EntityUID} :
  (Term.prim (TermPrim.entity uid)).value? = some (Value.prim (.entityUID uid))
:= by simp only [Term.value?, TermPrim.value?]

theorem same_entity_term_implies {v : Value} {uid : EntityUID} :
  v ∼ Term.prim (TermPrim.entity uid) → v = Value.prim (.entityUID uid)
:= by
  simp only [Same.same, SameValues, entity_value?, Option.some.injEq]
  intro h
  simp only [h]

theorem same_entity_implies {uid : EntityUID} {t : Term} :
  Value.prim (Prim.entityUID uid) ∼ t →
  t = .prim (.entity uid)
:= by
  simp_same_prim_implies Prim.entityUID.injEq

theorem same_string_term_implies {v : Value} {s : String} :
  v ∼ Term.prim (TermPrim.string s) → v = Value.prim (.string s)
:= by
  simp only [Same.same, SameValues, Term.value?, TermPrim.value?, Option.some.injEq]
  intro h
  simp only [h]

theorem same_string_implies {s : String} {t : Term} :
  Value.prim (Prim.string s) ∼ t →
  t = .prim (.string s)
:= by
  simp_same_prim_implies Prim.string.injEq

theorem same_bitvec_term_implies {v : Value} {n : Nat} {bv : BitVec n} :
  v ∼ Term.prim (TermPrim.bitvec bv) →
  ∃ i, v = Value.prim (.int i) ∧ bv.toInt = i ∧ n = 64
:= by
  simp only [Same.same, SameValues, Term.value?, TermPrim.value?, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, forall_exists_index, and_imp]
  intro i h₁ h₂
  simp only [BitVec.int64?] at h₁
  exists i
  simp only [h₂, true_and]
  split at h₁ <;>
  simp only [Option.some.injEq, reduceCtorEq] at h₁
  rename_i h₃
  subst h₃
  simp only [Int64.toInt, ← h₁, Int64.ofIntChecked, and_true]
  congr
  simp only [BitVec.toInt_ofInt64_toBitVec]

theorem same_bitvec64_term_implies {v : Value} {bv : BitVec 64} :
  v ∼ Term.prim (TermPrim.bitvec bv) →
  ∃ i, v = Value.prim (.int i) ∧ bv.toInt = i
:= by
  intro h
  replace ⟨i, h⟩ := same_bitvec_term_implies h
  simp only [and_true] at h
  exists i

theorem same_int_implies {t : Term} {bv : BitVec 64} {i : Int64} :
  BitVec.toInt bv = i.toInt →
  Value.prim (Prim.int i) ∼ t →
  t = Term.prim (TermPrim.bitvec bv)
:= by
  intro h₁ h₂
  simp only [Same.same, SameValues] at h₂
  cases t
  case prim p =>
    simp only [Term.value?, TermPrim.value?] at h₂
    split at h₂ <;>
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq, Value.prim.injEq, Prim.int.injEq, exists_eq_right, reduceCtorEq] at h₂
    simp only [BitVec.int64?] at h₂
    split at h₂ <;>
    simp only [Option.some.injEq, Int64.ofIntChecked, reduceCtorEq] at h₂
    rename_i hn ; subst hn
    simp only [← h₂] at h₁
    simp only [BitVec.eq_of_toInt_eq h₁, BitVec.toInt_ofInt64_toBitVec]
  case var | none | some | app =>
    simp only [Term.value?, reduceCtorEq] at h₂
  case set | record =>
    unfold Term.value? at h₂
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, and_false,
      exists_const, reduceCtorEq] at h₂

theorem same_int {i : Int} {bv : BitVec 64}
  (h₁ : Int64.MIN ≤ i ∧ i ≤ Int64.MAX)
  (h₂ : BitVec.toInt bv = i) :
  Value.prim (Prim.int (Int64.ofIntChecked i h₁)) ∼ Term.prim (TermPrim.bitvec bv)
:= by
  simp only [Same.same, SameValues, Term.value?, TermPrim.value?, BitVec.int64?, Int64.ofIntChecked, ↓reduceIte, h₂,
    Option.pure_def, Option.bind_some_fun, Option.some.injEq, Value.prim.injEq, Prim.int.injEq]

theorem same_bv {bv : BitVec 64} :
  Value.prim (Prim.int (Int64.ofInt bv.toInt)) ∼ Term.prim (TermPrim.bitvec bv)
:= by
  simp only [Same.same, SameValues, Term.value?, TermPrim.value?, BitVec.int64?,
    ↓reduceIte, Option.pure_def, Option.bind_some_fun]

theorem same_int64 {i : Int64} :
  Value.prim (Prim.int i) ∼ Term.prim (TermPrim.bitvec i.toBitVec)
:= by
  simp only [Same.same, SameValues, Term.value?, TermPrim.value?, BitVec.int64?, ↓reduceIte,
    Option.pure_def, Option.bind_some_fun, Option.some.injEq, Value.prim.injEq, Prim.int.injEq]
  cases i; rename_i i; cases i; rename_i i
  simp only [Int64.toBitVec, UInt64.toBitVec, Int64.ofInt, BitVec.ofInt_toInt]

theorem same_ext {x : Ext} :
  Value.ext x ∼ Term.prim (TermPrim.ext x)
:= by
  simp only [same_values_def, Term.value?, TermPrim.value?]

theorem same_ext_term_implies {v : Value} {x : Ext} :
  v ∼ Term.prim (TermPrim.ext x) → v = Value.ext x
:= by
  simp only [Same.same, SameValues, Term.value?, TermPrim.value?, Option.some.injEq]
  intro h
  simp only [h]

theorem same_ext_implies  {x : Ext} {t : Term} :
  Value.ext x ∼ t →
  t = .prim (.ext x)
:= by
  simp_same_prim_implies Value.ext.injEq

theorem value?_some_implies_attrValue?_some {a : Attr} {tₐ : Term} {vₐ : Value}
  (hv : Term.value? tₐ = some vₐ) :
  Term.value?.attrValue? a tₐ = some (a, some vₐ)
:= by
  unfold Term.value?.attrValue?
  split
  case h_1 | h_2 =>
    simp only [Term.value?, reduceCtorEq] at hv
  case h_3 =>
    simp only [hv, Option.bind_some_fun]

private theorem value?_attrValue?_some_required {a : Attr} {tₐ : Term} {av : Attr × Option Value}
  (hty: ∀ (ty : TermType), Term.typeOf tₐ = TermType.option ty → False)
  (hv : Term.value?.attrValue? a tₐ = some av) :
  ∃ vₐ, Term.value? tₐ = some vₐ ∧ (a, some vₐ) = av
:= by
  unfold Term.value?.attrValue? at hv
  split at hv
  case h_1 | h_2 =>
    simp only [Term.typeOf, TermType.option.injEq, forall_eq'] at hty
  case h_3 =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
    exact hv

private theorem value?_attrValue?_some_optional {a : Attr} {tₐ : Term} {av : Attr × Option Value}
  (hv : Term.value?.attrValue? a (.some tₐ) = some av) :
  ∃ vₐ, Term.value? tₐ = some vₐ ∧ (a, some vₐ) = av
:= by
  simp only [Term.value?.attrValue?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hv
  replace ⟨vₐ, hv, hv'⟩ := hv
  exists vₐ

private theorem value?_attrValue?_none_optional {a : Attr} {ty : TermType} {av : Attr × Option Value}
  (hv : Term.value?.attrValue? a (.none ty) = some av) :
  Term.value? (.none ty) = none ∧ (a, none) = av
:= by
  simp only [Term.value?.attrValue?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hv
  simp only [Term.value?, hv, and_self]

theorem value?_attrValue?_none_implies_none {a : Attr} {t : Term}
  (hv : Term.value?.attrValue? a t = some (a, none)) :
  ∃ ty, t = .none ty
:= by
  unfold Term.value?.attrValue? at hv
  cases t <;>
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq,
    and_false, exists_const, reduceCtorEq] at hv
  rename_i ty
  exists ty

theorem value?_attrValue?_some_implies_same {a : Attr} {t : Term} {v : Value} :
  Term.value?.attrValue? a t = some (a, some v) →
  match t.typeOf with
  | .option _ => ∃ t', t = .some t' ∧ v ∼ t'
  | _         => v ∼ t
:= by
  intro hv
  unfold Term.value?.attrValue? at hv
  simp only [Option.bind_eq_bind] at hv
  split
  case h_1 heq =>
    split at hv <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq, true_and,
      exists_eq_right, and_false, reduceCtorEq] at hv
    case h_1 t =>
      exists t
    case h_3 =>
      unfold Term.value? at hv
      split at hv
      case h_1 p _ _ =>
        have hp := typeOf_term_prim_isPrimType p
        simp only [TermType.isPrimType, heq, reduceCtorEq] at hp
      case h_2 | h_3 =>
        simp only [Term.typeOf, reduceCtorEq] at heq
      case h_4 =>
        simp only [reduceCtorEq] at hv
  case h_2 h =>
    split at hv <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq, true_and,
      exists_eq_right, and_false, reduceCtorEq] at hv
    case h_1 t =>
      specialize h (t.typeOf)
      simp only [typeOf_term_some, forall_const] at h
    case h_3 =>
      exact hv

theorem value?_attrValue?_fst {a : Attr} {t : Term} {av : Attr × Option Value} :
  Term.value?.attrValue? a t = some av → a = av.fst
:= by
  intro hv
  unfold Term.value?.attrValue? at hv
  split at hv <;>
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hv
  case h_1 | h_3 =>
    replace ⟨_, _, hv⟩ := hv
    simp only [← hv]
  case h_2 => simp only [← hv]

private abbrev attrValue?' :=
  (fun (x : Attr × Term) =>
    Option.bind (Term.value?.attrValue? x.fst x.snd)
      fun x => Option.map (Prod.mk x.fst) x.snd)

private theorem filterMap_attrValue?'_wf {rt : Map Attr Term}
  (hw  : rt.WellFormed) :
  Map.WellFormed (Map.mk (List.filterMap attrValue?' rt.1))
:= by
  rw [Map.wf_iff_sorted, Map.toList, Map.kvs] at hw
  replace hw : (List.filterMap attrValue?' rt.1).SortedBy Prod.fst := by
    apply List.filterMap_sortedBy _ hw
    intro x y hfx
    simp only [attrValue?', Option.bind_eq_some_iff, Option.map_eq_some_iff] at hfx
    have ⟨a, hfx, a', hfx'⟩ := hfx
    simp only [← hfx'.right, value?_attrValue?_fst hfx]
  exact Map.mk_wf hw

theorem record_value?_mapM' {rt : Map Attr Term} {rv : Map Attr Value}
  (hr : Term.value? (Term.record rt) = some (Value.record rv)) :
  ∃ avs,
    List.mapM' (fun x => Term.value?.attrValue? x.fst x.snd) rt.1 = some avs ∧
    Map.mk (List.filterMap (fun x => Option.map (Prod.mk x.fst) x.snd) avs) = rv
:= by
  unfold Term.value? at hr
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Value.record.injEq] at hr
  replace ⟨avs, hr, hv⟩ := hr
  simp only [List.mapM₂, List.attach₂,
    List.mapM_pmap_subtype (fun (x : Attr × Term) => Term.value?.attrValue? x.fst x.snd)] at hr
  rw [← List.mapM'_eq_mapM] at hr
  exists avs

theorem record_value_find? {a : Attr} {tₐ : Term} {rt : Map Attr Term} {avs : List (Attr × Option Value)}
  (hf : Map.find? rt a = some tₐ)
  (hr : List.mapM' (fun x => Term.value?.attrValue? x.fst x.snd) rt.1 = some avs) :
  ∃ av, av ∈ avs ∧ Term.value?.attrValue? a tₐ = some av
:= by
  have hr' := List.mapM'_some_implies_all_some hr
  replace ⟨av, hmem, hr'⟩ := hr' (a, tₐ) (Map.find?_mem_toList hf)
  simp only at hr'
  exists av

theorem record_value?_find?_required {a : Attr} {tₐ : Term} {rt : Map Attr Term} {rv : Map Attr Value}
  (hw  : rt.WellFormed)
  (hty : ∀ (ty : TermType), tₐ.typeOf = TermType.option ty → False)
  (hf  : Map.find? rt a = some tₐ)
  (hr  : Term.value? (Term.record rt) = some (Value.record rv)) :
  ∃ vₐ, Map.find? rv a = some vₐ ∧ tₐ.value? = some vₐ
:= by
  replace ⟨avs, hr, hv⟩ := record_value?_mapM' hr
  replace ⟨av, hmem, hr'⟩ := record_value_find? hf hr
  replace ⟨vₐ, hr', hr''⟩ := value?_attrValue?_some_required hty hr'
  subst hr''
  exists vₐ
  simp only [hr', and_true]
  subst hv
  replace hr := List.mapM'_some_eq_filterMap hr
  subst hr
  replace hf := Map.find?_mem_toList hf
  simp only [Map.toList, Map.kvs] at hf
  replace hmem : (a, vₐ) ∈ List.filterMap (fun x => Option.map (Prod.mk x.fst) x.snd)
    (List.filterMap (fun x => Term.value?.attrValue? x.fst x.snd) rt.1) := by
    simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq, exists_eq_right_right]
    exists (a, some vₐ)
    simp only [and_self, and_true]
    exists (a, tₐ)
    simp only [hf, true_and]
    exact value?_some_implies_attrValue?_some hr'
  simp only [List.filterMap_filterMap] at *
  replace hw := filterMap_attrValue?'_wf hw
  apply Map.mem_toList_find? hw
  simp only [Map.toList, Map.kvs, hmem]

theorem record_value?_find?_optional_some {a : Attr} {tₐ : Term} {rt : Map Attr Term} {rv : Map Attr Value}
  (hw : rt.WellFormed)
  (hf : Map.find? rt a = some (.some tₐ))
  (hr : Term.value? (Term.record rt) = some (Value.record rv)) :
  ∃ vₐ, Map.find? rv a = some vₐ ∧ tₐ.value? = some vₐ
:= by
  replace ⟨avs, hr, hv⟩ := record_value?_mapM' hr
  replace ⟨av, hmem, hr'⟩ := record_value_find? hf hr
  replace ⟨vₐ, hr', hr''⟩ := value?_attrValue?_some_optional hr'
  subst hr''
  exists vₐ
  simp only [hr', and_true]
  subst hv
  replace hr := List.mapM'_some_eq_filterMap hr
  subst hr
  replace hf := Map.find?_mem_toList hf
  simp only [Map.toList, Map.kvs] at hf
  replace hmem : (a, vₐ) ∈ List.filterMap (fun x => Option.map (Prod.mk x.fst) x.snd)
    (List.filterMap (fun x => Term.value?.attrValue? x.fst x.snd) rt.1) := by
    simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq, exists_eq_right_right]
    exists (a, some vₐ)
    simp only [and_self, and_true]
    exists (a, .some tₐ)
    simp only [hf, Term.value?.attrValue?, hr', Option.bind_some_fun, and_self]
  simp only [List.filterMap_filterMap] at *
  replace hw := filterMap_attrValue?'_wf hw
  apply Map.mem_toList_find? hw
  simp only [Map.toList, Map.kvs, hmem]

theorem record_value?_find?_optional_none {a : Attr} {ty : TermType} {rt : Map Attr Term} {rv : Map Attr Value}
  (hw : rt.WellFormed)
  (hf : Map.find? rt a = some (.none ty))
  (hr : Term.value? (Term.record rt) = some (Value.record rv)) :
  Map.find? rv a = none
:= by
  rw [Map.wf_iff_sorted, Map.toList, Map.kvs] at hw
  replace ⟨avs, hr, hv⟩ := record_value?_mapM' hr
  replace ⟨av, hmem, hr'⟩ := record_value_find? hf hr
  replace ⟨_, hr'⟩ := value?_attrValue?_none_optional hr'
  subst hr'
  subst hv
  replace hr := List.mapM'_some_eq_filterMap hr
  subst hr
  simp only [Map.find?, Map.kvs]
  split <;> simp only [reduceCtorEq]
  rename_i heq
  have heq' := List.find?_some heq
  rw [beq_iff_eq, eq_comm] at heq'
  subst heq'
  replace heq := List.mem_of_find?_eq_some heq
  simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq, exists_eq_right_right] at heq
  replace ⟨_, ⟨p', hmem', heq⟩, hsnd, hfst⟩ := heq
  simp only [List.mem_filterMap] at hmem
  replace ⟨p, hmem, ha⟩ := hmem
  have h : p' = p := by
    replace ha := value?_attrValue?_fst ha
    simp only at ha
    replace heq := value?_attrValue?_fst heq
    simp only [hfst, ←ha] at heq
    exact List.mem_of_sortedBy_unique hw hmem' hmem heq
  subst h
  simp only [heq, Option.some.injEq] at ha
  simp only [ha, reduceCtorEq] at hsnd

theorem record_value?_find?_none {a : Attr} {rt : Map Attr Term} {rv : Map Attr Value}
  (hw : rt.WellFormed)
  (hf : Map.find? rt a = none)
  (hr : Term.value? (Term.record rt) = some (Value.record rv)) :
  Map.find? rv a = none
:= by
  rw [Map.wf_iff_sorted, Map.toList, Map.kvs] at hw
  replace ⟨avs, hr, hv⟩ := record_value?_mapM' hr
  subst hv
  replace hr := List.mapM'_some_eq_filterMap hr
  subst hr
  simp only [Map.find?, Map.kvs]
  split <;> simp only [reduceCtorEq]
  rename_i heq
  have heq' := List.find?_some heq
  rw [beq_iff_eq, eq_comm] at heq'
  subst heq'
  replace heq := List.mem_of_find?_eq_some heq
  simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq,
    exists_eq_right_right] at heq
  replace ⟨_, ⟨p, hmem', heq⟩, _, hfst⟩ := heq
  simp only [Map.find?, Map.kvs] at hf
  split at hf <;> simp only [reduceCtorEq] at hf
  rename_i h
  apply h p.fst p.snd
  replace heq := value?_attrValue?_fst heq
  replace hmem' := List.mem_of_sortedBy_implies_find? hmem' hw
  simp only [heq, hfst] at hmem'
  exact hmem'

theorem same_prim_value_inj {v : Value} {p : TermPrim} {t : Term} :
  v ∼ (Term.prim p) → v ∼ t → (Term.prim p) = t
:= by
  intro h₁ h₂
  cases p
  case bool b =>
    replace h₁ := same_bool_term_implies h₁
    subst h₁
    simp only [same_bool_implies h₂]
  case bitvec bv =>
    replace ⟨i, h₃, h₁, h₄⟩ := same_bitvec_term_implies h₁
    subst h₃ h₄
    simp only [same_int_implies h₁ h₂]
  case string s =>
    replace h₁ := same_string_term_implies h₁
    subst h₁
    simp only [same_string_implies h₂]
  case entity uid =>
    replace h₁ := same_entity_term_implies h₁
    subst h₁
    simp only [same_entity_implies h₂]
  case ext xt =>
    replace h₁ := same_ext_term_implies h₁
    subst h₁
    simp only [same_ext_implies h₂]

theorem set_value?_implies_in_value {vs : Set Value} {ts : Set Term} {ty : TermType} :
  Term.value? (Term.set ts ty) = some (Value.set vs) →
  ∀ t, t ∈ ts → ∃ v, v ∈ vs ∧ t.value? = some v
:= by
  intro hv t ht
  rw [Term.value?] at hv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Value.set.injEq] at hv
  replace ⟨ts', hv, hvs⟩ := hv
  subst hvs
  simp only [List.mapM₁_eq_mapM Term.value?, ← List.mapM'_eq_mapM] at hv
  rw [← Set.in_list_iff_in_set] at ht
  replace ⟨v, hv⟩ := List.mapM'_some_implies_all_some hv t ht
  exists v
  simp only [← Set.make_mem, hv, and_self]

theorem set_value?_implies_in_term {vs : Set Value} {ts : Set Term} {ty : TermType} :
  Term.value? (Term.set ts ty) = some (Value.set vs) →
  ∀ v, v ∈ vs → ∃ t, t ∈ ts ∧ t.value? = some v
:= by
  intro hv v ht
  rw [Term.value?] at hv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Value.set.injEq] at hv
  replace ⟨vs', hv, hvs⟩ := hv
  subst hvs
  simp only [List.mapM₁_eq_mapM Term.value?, ← List.mapM'_eq_mapM] at hv
  rw [← Set.make_mem] at ht
  replace ⟨t, hv⟩ := List.mapM'_some_implies_all_from_some hv v ht
  rw [Set.in_list_iff_in_set] at hv
  exists t

private theorem set_value?_eq_implies_subseteq {vs : Set Value} {ts₁ ts₂ : Set Term} {ty : TermType}
  (hv₁ : Term.value? (Term.set ts₁ ty) = some (Value.set vs))
  (hv₂ : Term.value? (Term.set ts₂ ty) = some (Value.set vs))
  (hsm : ∀ (v : Value) (t₁ t₂ : Term), t₁ ∈ ts₁ → t₂ ∈ ts₂ → v ∼ t₁ → v ∼ t₂ → t₁ = t₂) :
  ts₁ ⊆ ts₂
:= by
  rw [Set.subset_def]
  intro t₁ ht₁
  have ⟨v, h₁⟩ := set_value?_implies_in_value hv₁ t₁ ht₁
  have ⟨t₂, h₂⟩ := set_value?_implies_in_term hv₂ v h₁.left
  specialize hsm v t₁ t₂ ht₁ h₂.left
  simp only [Same.same, SameValues, h₁.right, h₂.right, forall_const] at hsm
  simp only [hsm, h₂.left]

theorem record_value?_some_implies {ats : List (Attr × Term)} {avs : List (Attr × Value)} :
  (Term.record (Map.mk ats)).value? = some (Value.record (Map.mk avs)) →
  ∃ (avs' : List (Attr × Option Value)),
    List.mapM' (λ (x : Attr × Term) => Term.value?.attrValue? x.fst x.snd) ats = some avs' ∧
    List.filterMap (λ (x : Attr × Option Value) => Option.map (Prod.mk x.fst) x.snd) avs' = avs
:= by
  intro hv
  simp only [Term.value?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Value.record.injEq, Map.mk.injEq] at hv
  replace ⟨avs', hv⟩ := hv
  rw [List.mapM₂, List.attach₂,
    List.mapM_pmap_subtype λ (x : Attr × Term) => Term.value?.attrValue? x.fst x.snd,
    ← List.mapM'_eq_mapM] at hv
  exists avs'

theorem record_value?_some_implied_by {ats : List (Attr × Term)} {avs : List (Attr × Value)} {avs' : List (Attr × Option Value)} :
  List.mapM' (λ (x : Attr × Term) => Term.value?.attrValue? x.fst x.snd) ats = some avs' →
  List.filterMap (λ (x : Attr × Option Value) => Option.map (Prod.mk x.fst) x.snd) avs' = avs →
  (Term.record (Map.mk ats)).value? = some (Value.record (Map.mk avs))
:= by
  intro h₁ h₂
  simp only [Term.value?, List.mapM₂, List.attach₂,
    List.mapM_pmap_subtype λ (x : Attr × Term) => Term.value?.attrValue? x.fst x.snd, ←
    List.mapM'_eq_mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Value.record.injEq, Map.mk.injEq, h₁]
  exists avs'

private theorem record_value?_cons {a : Attr} {t : Term} {ats : List (Attr × Term)} {avs : List (Attr × Value)} :
  (Term.record (Map.mk ((a, t) :: ats))).value? = some (Value.record (Map.mk avs)) →
  ∃ vₒ, Term.value?.attrValue? a t = .some (a, vₒ) ∧
    match vₒ with
    | .some v => ∃ avs', avs = (a, v) :: avs' ∧ (Term.record (Map.mk ats)).value? = some (Value.record (Map.mk avs'))
    | .none   => (Term.record (Map.mk ats)).value? = some (Value.record (Map.mk avs))
:= by
  intro hv
  replace ⟨ats', hv⟩ := record_value?_some_implies hv
  simp only [List.mapM'_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hv
  replace ⟨⟨av', ⟨hv, avs', hv', havs⟩⟩, h⟩ := hv
  subst havs
  exists av'.snd
  simp only [hv, Option.some.injEq]
  simp only [value?_attrValue?_fst hv, true_and]
  simp only [List.filterMap_cons] at h
  split
  case h_1 v hsome =>
    simp only [hsome, Option.map_some] at h
    exists (List.filterMap (fun x => Option.map (Prod.mk x.fst) x.snd) avs')
    simp only [h, true_and]
    exact record_value?_some_implied_by hv' rfl
  case h_2 hnone =>
    simp only [hnone, Option.map_none] at h
    exact record_value?_some_implied_by hv' h

private theorem record_value?_head_none {a : Attr} {t : Term} {ats : List (Attr × Term)} {avs : List (Attr × Value)} :
  ((a, t) :: ats).SortedBy Prod.fst →
  Term.value? (Term.record (Map.mk ((a, t) :: ats))) = some (Value.record (Map.mk avs)) →
  Term.value?.attrValue? a t = some (a, none) →
  Map.find? (Map.mk avs) a = none
:= by
  intro hw hv' ha
  have hm : ((a, t) :: ats) = (Map.mk ((a, t) :: ats)).toList := by simp only [Map.toList]
  rw [hm, ← Map.wf_iff_sorted] at hw
  replace ⟨ty, ha⟩ := value?_attrValue?_none_implies_none ha
  subst ha
  have hf : Map.find? (Map.mk ((a, Term.none ty) :: ats)) a = some (Term.none ty) := by
    simp only [Map.find?, List.find?, beq_self_eq_true]
  exact record_value?_find?_optional_none hw hf hv'


private theorem record_value?_eq' {rv : List (Attr × Value)} {r₁ r₂ : List (Attr × Term)}
  (hw₁ : r₁.SortedBy Prod.fst)
  (hw₂ : r₂.SortedBy Prod.fst)
  (hty : (Term.record (Map.mk r₁)).typeOf = (Term.record (Map.mk r₂)).typeOf)
  (hv₁ : Term.value? (Term.record (Map.mk r₁)) = some (Value.record (Map.mk rv)))
  (hv₂ : Term.value? (Term.record (Map.mk r₂)) = some (Value.record (Map.mk rv)))
  (ih₁  : ∀ (a : Attr) (v : Value) (t₁ t₂ : Term), (a, t₁) ∈ r₁ → (a, t₂) ∈ r₂ → v ∼ t₁ → v ∼ t₂ → t₁ = t₂)
  (ih₂  : ∀ (a : Attr) (v : Value) (t₁ t₂ : Term), (a, .some t₁) ∈ r₁ → (a, .some t₂) ∈ r₂ → v ∼ t₁ → v ∼ t₂ → t₁ = t₂) :
  r₁ = r₂
:= by
  have htyₘ := hty
  simp only [typeOf_term_record_eq, TermType.record.injEq, Map.mk.injEq] at htyₘ
  cases r₁ <;> cases r₂ <;>
  simp only [Map.mk.injEq, List.cons.injEq, reduceCtorEq] <;>
  simp only [List.map_nil, List.map_cons, List.cons.injEq, Prod.mk.injEq, reduceCtorEq] at htyₘ
  rename_i hd₁ tl₁ hd₂ tl₂
  cases hd₁ ; cases hd₂ ; rename_i a₁ t₁ a₂ t₂
  simp only [List.mem_cons, Prod.mk.injEq] at *
  replace ⟨⟨ha, htyₜ⟩, _⟩ := htyₘ
  subst ha
  simp only [true_and] at *
  have ⟨v₁', hv₁'⟩ := record_value?_cons hv₁
  have ⟨v₂', hv₂'⟩ := record_value?_cons hv₂
  cases v₁' <;> cases v₂' <;>
  simp only at *
  case none.none =>
    have ⟨ty₁, ht₁⟩ := value?_attrValue?_none_implies_none hv₁'.left
    have ⟨ty₂, ht₂⟩ := value?_attrValue?_none_implies_none hv₂'.left
    subst ht₁ ht₂
    simp only [Term.none.injEq] at *
    simp only [typeOf_term_none, TermType.option.injEq] at htyₜ
    subst htyₜ
    simp only [true_and] at *
    apply record_value?_eq'
      (List.tail_sortedBy hw₁) (List.tail_sortedBy hw₂)
      (typeOf_term_record_tail hty) hv₁'.right hv₂'.right
    · intro a v t₁ t₂ ht₁ ht₂ hs₁ hs₂
      exact ih₁ a v t₁ t₂ (Or.inr ht₁) (Or.inr ht₂) hs₁ hs₂
    · intro a v t₁ t₂ ht₁ ht₂ hs₁ hs₂
      exact ih₂ a v t₁ t₂ (Or.inr ht₁) (Or.inr ht₂) hs₁ hs₂
  case none.some =>
    have hc := record_value?_head_none hw₁ hv₁ hv₁'.left
    replace ⟨_, avs', hv₂', _⟩ := hv₂'
    simp only [Map.find?, hv₂', List.find?, beq_self_eq_true, reduceCtorEq] at hc
  case some.none =>
    have hc := record_value?_head_none hw₂ hv₂ hv₂'.left
    replace ⟨_, avs', hv₁', _⟩ := hv₁'
    simp only [Map.find?, hv₁', List.find?, beq_self_eq_true, reduceCtorEq] at hc
  case some.some v₁ v₂ =>
    replace ⟨hva₁, ⟨avs₁', hv₁', htl₁⟩⟩ := hv₁'
    replace ⟨hva₂, avs₂', hv₂', htl₂⟩ := hv₂'
    simp only [hv₁', List.cons.injEq, Prod.mk.injEq, true_and] at hv₂'
    replace ⟨hv₂', hv₃⟩ := hv₂'
    subst hv₂' hv₃
    constructor
    · replace hva₁ := value?_attrValue?_some_implies_same hva₁
      replace hva₂ := value?_attrValue?_some_implies_same hva₂
      simp only [htyₜ] at hva₁
      split at hva₁
      case h_1 heq =>
        simp only [heq] at hva₂
        replace ⟨t₁', ht₁, hva₁⟩ := hva₁
        replace ⟨t₂', ht₂, hva₂⟩ := hva₂
        subst ht₁ ht₂
        specialize ih₂ a₁ v₁ t₁' t₂'
        simp only [and_self, true_or, forall_const] at ih₂
        simp only [Term.some.injEq]
        exact ih₂ hva₁ hva₂
      case h_2 =>
        simp only at hva₂
        specialize ih₁ a₁ v₁ t₁ t₂
        simp only [and_self, true_or, forall_const] at ih₁
        exact ih₁ hva₁ hva₂
    · apply record_value?_eq'
        (List.tail_sortedBy hw₁) (List.tail_sortedBy hw₂)
        (typeOf_term_record_tail hty) htl₁ htl₂
      · intro a v t₁ t₂ ht₁ ht₂ hs₁ hs₂
        exact ih₁ a v t₁ t₂ (Or.inr ht₁) (Or.inr ht₂) hs₁ hs₂
      · intro a v t₁ t₂ ht₁ ht₂ hs₁ hs₂
        exact ih₂ a v t₁ t₂ (Or.inr ht₁) (Or.inr ht₂) hs₁ hs₂

private theorem record_value?_eq {rv : Map Attr Value} {r₁ r₂ : Map Attr Term} {rty : Map Attr TermType}
  (hw₁  : r₁.WellFormed)
  (hw₂  : r₂.WellFormed)
  (hty₁ : (Term.record r₁).typeOf = .record rty)
  (hty₂ : (Term.record r₂).typeOf = .record rty)
  (hv₁  : Term.value? (Term.record r₁) = some (Value.record rv))
  (hv₂  : Term.value? (Term.record r₂) = some (Value.record rv))
  (ih₁  : ∀ (a : Attr) (v : Value) (t₁ t₂ : Term), (a, t₁) ∈ r₁.1 → (a, t₂) ∈ r₂.1 → v ∼ t₁ → v ∼ t₂ → t₁ = t₂)
  (ih₂  : ∀ (a : Attr) (v : Value) (t₁ t₂ : Term), (a, .some t₁) ∈ r₁.1 → (a, .some t₂) ∈ r₂.1 → v ∼ t₁ → v ∼ t₂ → t₁ = t₂) :
  r₁ = r₂
:= by
  cases r₁ ; cases r₂ ; rename_i r₁ r₂
  simp only [Map.mk.injEq] at *
  rw [← hty₂] at hty₁ ; clear hty₂
  rw [Map.wf_iff_sorted] at hw₁ hw₂
  simp only [Map.toList, Map.kvs] at hw₁ hw₂
  exact record_value?_eq' hw₁ hw₂ hty₁ hv₁ hv₂ ih₁ ih₂

private theorem same_value_inj' {t₁ t₂ : Term} {v : Value} {εs : SymEntities} :
  t₁.WellFormed εs → t₂.WellFormed εs → t₁.typeOf = t₂.typeOf →
  v ∼ t₁ → v ∼ t₂ → Term.some t₁ = Term.some t₂
:= by
  intro hw₁ hw₂ hty h₁ h₂
  simp only [Term.some.injEq]
  cases t₁
  case var | none | app | some =>
    simp only [Same.same, SameValues, Term.value?, reduceCtorEq] at h₁
  case prim p =>
    exact same_prim_value_inj h₁ h₂
  case set s₁ ty =>
    replace ⟨vs₁, hv, h₁⟩ := same_set_term_implies h₁
    subst hv
    rw [Term.typeOf, eq_comm] at hty
    replace ⟨s₂, ht, hv⟩ := same_set_implies h₂ hty
    subst ht
    have ih : ∀ (v' : Value) (t₁' t₂' : Term), t₁' ∈ s₁ → t₂' ∈ s₂ → v' ∼ t₁' → v' ∼ t₂' → t₁' = t₂' := by
      intro v' t₁' t₂' ht₁ ht₂ hs₁ hs₂
      rw [← Term.some.injEq]
      exact same_value_inj'
        (wf_term_set_implies_wf_elt hw₁ ht₁)
        (wf_term_set_implies_wf_elt hw₂ ht₂)
        (by simp only [wf_term_set_implies_typeOf_elt hw₁ ht₁, wf_term_set_implies_typeOf_elt hw₂ ht₂])
        hs₁ hs₂
    have ih' : (∀ (v : Value) (t₁' t₂' : Term), t₁' ∈ s₂ → t₂' ∈ s₁ → v ∼ t₁' → v ∼ t₂' → t₁' = t₂') := by
      intro v' t₁' t₂' ht₁ ht₂ hs₁ hs₂
      simp only [ih v' t₂' t₁' ht₂ ht₁ hs₂ hs₁]
    have hs₁ := set_value?_eq_implies_subseteq h₁ hv ih
    have hs₂ := set_value?_eq_implies_subseteq hv h₁ ih'
    have heq := Set.subset_iff_eq (wf_term_set_implies_wf_set hw₁) (wf_term_set_implies_wf_set hw₂)
    simp only [Term.set.injEq, and_true, ← heq, hs₁, hs₂]
  case record r₁ =>
    replace ⟨rv₁, hv, h₁⟩ := same_record_term_implies h₁
    subst hv
    have ⟨rty, hrty⟩ := @typeOf_term_record_is_record_type r₁
    rw [hrty, eq_comm] at hty
    have ⟨r₂, ht, hv⟩  := same_record_implies h₂ hty
    subst ht
    simp only [Term.record.injEq]
    have ih₁ : ∀ (a : Attr) (v' : Value) (t₁' t₂' : Term), (a, t₁') ∈ r₁.1 → (a, t₂') ∈ r₂.1 → v' ∼ t₁' → v' ∼ t₂' → t₁' = t₂' := by
      intro a v' t₁' t₂' ht₁ ht₂ hr₁ hr₂
      rw [← Term.some.injEq]
      have hf₁ := Map.mem_toList_find? (wf_term_record_implies_wf_map hw₁) ht₁
      have hf₂ := Map.mem_toList_find? (wf_term_record_implies_wf_map hw₂) ht₂
      exact same_value_inj'
        (wf_term_record_implies_wf_value hw₁ ht₁)
        (wf_term_record_implies_wf_value hw₂ ht₂)
        (typeOf_term_record_attr_value_eq hrty hty hf₁ hf₂)
        hr₁ hr₂
    have ih₂ :  ∀ (a : Attr) (v' : Value) (t₁' t₂' : Term), (a, .some t₁') ∈ r₁.1 → (a, .some t₂') ∈ r₂.1 → v' ∼ t₁' → v' ∼ t₂' → t₁' = t₂' := by
      intro a v' t₁' t₂' ht₁ ht₂ hr₁ hr₂
      rw [← Term.some.injEq]
      have hf₁ := Map.mem_toList_find? (wf_term_record_implies_wf_map hw₁) ht₁
      have hf₂ := Map.mem_toList_find? (wf_term_record_implies_wf_map hw₂) ht₂
      have hty' := typeOf_term_record_attr_value_eq hrty hty hf₁ hf₂
      simp only [typeOf_term_some, TermType.option.injEq] at hty'
      exact same_value_inj'
        (wf_term_some_implies (wf_term_record_implies_wf_value hw₁ ht₁))
        (wf_term_some_implies (wf_term_record_implies_wf_value hw₂ ht₂))
        hty' hr₁ hr₂
    exact record_value?_eq
      (wf_term_record_implies_wf_map hw₁)
      (wf_term_record_implies_wf_map hw₂)
      hrty hty h₁ hv ih₁ ih₂
termination_by sizeOf t₁
decreasing_by
  all_goals ( simp_wf ; rename_i hsz _ _ _ _ )
  . simp only [hsz, Term.set.sizeOf_spec]
    have _ := Set.sizeOf_lt_of_mem ht₁
    omega
  · simp only [hsz, Term.record.sizeOf_spec, gt_iff_lt]
    have _ := Map.sizeOf_lt_of_value ht₁
    omega
  · simp only [hsz, Term.record.sizeOf_spec, gt_iff_lt]
    have h := Map.sizeOf_lt_of_value ht₁
    simp only [Term.some.sizeOf_spec] at h
    omega

theorem same_value_inj {t₁ t₂ : Term} {v : Value} {εs : SymEntities} :
  t₁.WellFormed εs → t₂.WellFormed εs → t₁.typeOf = t₂.typeOf →
  v ∼ t₁ → v ∼ t₂ → t₁ = t₂
:= by
  intro hw₁ hw₂ hty h₁ h₂
  rw [← Term.some.injEq]
  exact same_value_inj' hw₁ hw₂ hty h₁ h₂

private theorem prim_value?_exists {p : TermPrim} {ty : Validation.CedarType} {εs : SymEntities} :
  p.WellFormed εs →
  p.typeOf.cedarType? = .some ty →
  ∃ (v : Value), p.value? = some v
:= by
  intro hw hty
  cases p <;>
  simp only [TermPrim.value?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, exists_eq']
  simp only [TermPrim.typeOf] at hty
  unfold TermType.cedarType? at hty
  split at hty <;>
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] at hty <;>
  rename_i heq <;>
  simp only [TermType.prim.injEq, TermPrimType.bitvec.injEq, reduceCtorEq] at heq
  rename_i bv _
  simp only [BitVec.width] at heq
  subst heq
  simp only [BitVec.int64?, ↓reduceIte, Option.some.injEq, exists_eq_left', exists_eq']

private theorem wfl_isCedarRecordType_implies_attr_wfl_cedarType? {a : Attr} {t : Term} {r : List (Attr × Term)} {ty : Validation.CedarType} :
  Term.WellFormed εs (Term.record (Map.mk r)) →
  (Term.record (Map.mk r)).isLiteral →
  (Term.record (Map.mk r)).typeOf.cedarType? = some ty →
  (a, t) ∈ r →
  ∃ (cty : Validation.CedarType),
    match t with
    | .none tty => tty.cedarType? = .some cty
    | .some t'  => t = Term.some t' ∧ t'.WellFormedLiteral εs ∧ t'.typeOf.cedarType? = cty
    | _         => t.WellFormedLiteral εs ∧ t.typeOf.cedarType? = .some cty
:= by
  intro hwf hlit hcty hin
  have ⟨tty, cty, hcty', hty⟩ := typeOf_term_record_cedarType?_some_implies_attr_cedarType?_some hcty hin
  have hwf' := wf_term_record_implies_wf_value hwf hin
  have hlit' := lit_term_record_implies_lit_value hlit hin
  exists cty
  split
  · simp only [typeOf_term_none, TermType.option.injEq] at hty
    rcases hty with hty | hty <;> subst hty
    · simp only [TermType.cedarType?, reduceCtorEq] at hcty'
    · exact hcty'
  · simp only [true_and]
    simp only [typeOf_term_some, TermType.option.injEq] at hty
    rcases hty with hty | hty <;> subst hty
    · simp only [TermType.cedarType?, reduceCtorEq] at hcty'
    · simp only [hcty', and_true]
      replace hlit' := lit_term_some_implies_lit hlit'
      replace hwf' := wf_term_some_implies hwf'
      exact (And.intro hwf' hlit')
  · rcases hty with hty | hty
    · subst hty
      simp only [hcty', and_true]
      exact (And.intro hwf' hlit')
    · rename_i h₁ h₂
      have h₃ := wfl_of_type_option_is_option (And.intro hwf' hlit') hty
      rcases h₃ with h₃ | ⟨t', h₃, _⟩ <;> subst h₃ <;>
      simp only [Term.none.injEq, imp_false, imp_self,
        implies_true, Term.some.injEq, forall_eq'] at h₁ h₂

theorem term_value?_exists {t : Term} {ty : Validation.CedarType} {εs : SymEntities} :
  t.WellFormedLiteral εs →
  t.typeOf.cedarType? = .some ty →
  ∃ (v : Value), t.value? = some v
:= by
  intro hwfl hcty
  have ⟨hwf, hlit⟩ := hwfl
  unfold Term.value?
  cases t <;>
  simp only [exists_const, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
  case var | app =>
    simp only [Term.isLiteral, Bool.false_eq_true] at hlit
  case none | some =>
    simp only [Term.typeOf, TermType.cedarType?, reduceCtorEq] at hcty
  case prim =>
    cases hwf ; rename_i hwf
    simp only [Term.typeOf] at hcty
    exact prim_value?_exists hwf hcty
  case set ts sty =>
    cases ts ; rename_i ts
    simp only [Term.typeOf, TermType.cedarType?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hcty
    have ⟨ty', hcty', _⟩ := hcty
    have ih : ∀ t' ∈ ts, ∃ (v' : Value), t'.value? = some v' := by
      intro t' hin
      have hlit' := lit_term_set_implies_lit_elt hlit hin
      have hwf'  := wf_term_set_implies_wf_elt hwf hin
      have hty'  := wf_term_set_implies_typeOf_elt hwf hin
      subst hty'
      exact term_value?_exists (And.intro hwf' hlit') hcty'
    replace ⟨vs, ih⟩ := List.all_some_implies_mapM_some ih
    exists (Value.set (Set.make vs)), vs
    simp only [List.mapM₁_eq_mapM, ih, and_self]
  case record ats =>
    cases ats ; rename_i ats
    have ih : ∀ p, p ∈ ats → ∃ aov, Term.value?.attrValue? p.1 p.2 = some aov := by
      intro (a', t') hin
      have ⟨cty, ht⟩ := wfl_isCedarRecordType_implies_attr_wfl_cedarType? hwf hlit hcty hin
      split at ht
      · simp only [Term.value?.attrValue?, Option.some.injEq, exists_eq']
      · simp only [true_and] at ht
        simp only [Term.value?.attrValue?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
        have ⟨v', hv'⟩ := term_value?_exists ht.left ht.right
        exists (a', some v'), v'
      · have ⟨v', hv'⟩ := term_value?_exists ht.left ht.right
        exists (a', some v')
        simp only [value?_some_implies_attrValue?_some hv']
    replace ⟨avs, ih⟩ := List.all_some_implies_mapM_some ih
    exists Value.record (Map.mk (List.filterMap (fun x => Option.map (Prod.mk x.fst) x.snd) avs))
    exists avs
    simp only [List.mapM₂, List.attach₂,
      List.mapM_pmap_subtype λ (x : Attr × Term) => Term.value?.attrValue? x.fst x.snd,
      ih, and_true]
termination_by t
decreasing_by
  all_goals (simp_wf)
  · rename_i h _ _ _ _ _ _ ; subst h
    rename_i h ; subst h
    simp only [Term.set.sizeOf_spec, Set.mk.sizeOf_spec]
    have _ := List.sizeOf_lt_of_mem hin
    omega
  · rename_i h ; subst h
    rename_i h _ _ _ ; subst h
    rename_i h ; subst h
    simp only [Term.record.sizeOf_spec, Map.mk.sizeOf_spec]
    have hs := List.sizeOf_lt_of_mem hin
    simp only [Prod.mk.sizeOf_spec, Term.some.sizeOf_spec] at hs
    omega
  · rename_i h _ _ ; subst h
    rename_i h _ _ _ _ _ ; subst h
    rename_i h ; subst h
    simp only [Term.record.sizeOf_spec, Map.mk.sizeOf_spec]
    have hs := List.sizeOf_lt_of_mem hin
    simp only [Prod.mk.sizeOf_spec] at hs
    omega

end Cedar.Thm
