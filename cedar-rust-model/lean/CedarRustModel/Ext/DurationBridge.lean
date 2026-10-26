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

public import CedarRustModel.Ext.Duration
public import Cedar.Thm.Ext.Duration
import all Cedar.Spec.Ext.Datetime
import all Cedar.Spec.Ext.Util
import all Cedar.Thm.Data.String
import all Cedar.Thm.Ext.Duration.Grammar
import all Cedar.Data.Int64

/-! `XL.parseDuration` (the shadow of the model's duration parser) is Lean's
`Duration.parse`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.deprecated false

namespace CedarRustModel.XL

open Cedar.Spec.Ext Cedar.Thm String
open Cedar.Thm.Duration (Components IsWfDuration IsDurationValue DurationProduction parse_sound
  parse_eq_none_iff optionalNatOf IsWfOptionalQuantity)

section

/-! ## Units -/

/-- A unit `ds u` of a duration body -/
def chunkL : Option (List Char) → Char → List Char
  | none, _ => []
  | some ds, u => ds ++ [u]

/-- The milliseconds `ds ms` of a duration body -/
def chunkMs : Option (List Char) → List Char
  | none => []
  | some ds => ds ++ ['m', 's']

/-- A present quantity: one or more ASCII digits -/
def QOk : Option (List Char) → Prop
  | none => True
  | some ds => ds ≠ [] ∧ allDigits ds = true

theorem takeWhile_digits {ds : List Char} (hd : allDigits ds = true) {c : Char} (hc : c.isDigit = false)
    (rest : List Char) : (ds ++ c :: rest).takeWhile Char.isDigit = ds := by
  induction ds with
  | nil => simp [hc]
  | cons d ds ih =>
    simp only [allDigits, List.all_cons, Bool.and_eq_true] at hd
    simp [hd.1, ih hd.2]

theorem dropWhile_digits {ds : List Char} (hd : allDigits ds = true) {c : Char} (hc : c.isDigit = false)
    (rest : List Char) : (ds ++ c :: rest).dropWhile Char.isDigit = c :: rest := by
  induction ds with
  | nil => simp [hc]
  | cons d ds ih =>
    simp only [allDigits, List.all_cons, Bool.and_eq_true] at hd
    simp [hd.1, ih hd.2]

theorem takeUnit_digits {ds : List Char} (hne : ds ≠ []) (hd : allDigits ds = true) {c : Char}
    (hc : c.isDigit = false) (u : Char) (noS : Bool) (rest : List Char) :
    takeUnit u noS (ds ++ c :: rest) =
      if c = u ∧ ¬ (noS = true ∧ rest.head? = some 's') then (some ds, rest)
      else (none, ds ++ c :: rest) := by
  simp only [takeUnit, takeWhile_digits hd hc, dropWhile_digits hd hc, hne, ite_false]
  by_cases h : c = u <;> simp [h]
  split_ifs <;> simp_all

theorem takeUnit_nil (u : Char) (noS : Bool) : takeUnit u noS [] = (none, []) := by
  simp [takeUnit]

theorem takeMs_digits {ds : List Char} (hne : ds ≠ []) (hd : allDigits ds = true) {c : Char}
    (hc : c.isDigit = false) (rest : List Char) :
    takeMs (ds ++ c :: rest) =
      match takeChar 'm' (c :: rest) with
      | none => (none, ds ++ c :: rest)
      | some r1 => match takeChar 's' r1 with
        | none => (none, ds ++ c :: rest)
        | some r2 => (some ds, r2) := by
  simp only [takeMs, takeWhile_digits hd hc, dropWhile_digits hd hc, hne, ite_false]
  rfl

theorem takeMs_nil : takeMs [] = (none, []) := by simp [takeMs]

theorem head?_digits {ds : List Char} (hne : ds ≠ []) (hd : allDigits ds = true) {c : Char}
    (hc : c.isDigit = false) (rest : List Char) : (ds ++ rest).head? = some c ↔ False := by
  cases ds with
  | nil => contradiction
  | cons d ds =>
    simp only [allDigits, List.all_cons, Bool.and_eq_true] at hd
    simp only [List.cons_append, List.head?_cons, Option.some.injEq, iff_false]
    intro h; subst h; simp_all

theorem head?_getD_digits {ds : List Char} (hne : ds ≠ []) (hd : allDigits ds = true) (x : Char) {c : Char}
    (hc : c.isDigit = false) : (ds.head?.getD x = c) ↔ False := by
  cases ds with
  | nil => contradiction
  | cons d ds =>
    simp only [allDigits, List.all_cons, Bool.and_eq_true] at hd
    simp only [List.head?_cons, Option.getD_some, iff_false]
    intro h; subst h; simp_all

theorem durBody_digits {ds : List Char} (hne : ds ≠ []) (hd : allDigits ds = true) (rest : List Char) :
    durBody (ds ++ rest) = ds ++ rest := by
  cases ds with
  | nil => contradiction
  | cons d ds =>
    simp only [allDigits, List.all_cons, Bool.and_eq_true] at hd
    have : d ≠ '-' := by intro h; subst h; simp at hd
    simp [durBody, this]

/-! ## The value -/

theorem durStep_pos (a : Int) (y : Nat) (mul : Int) (hm : 2 ≤ mul) (ha : 0 ≤ a) :
    durStep a y mul false = chk (a + y * mul) := by
  have h1 : (y : Int) ≤ y * mul := by nlinarith
  simp only [durStep, chk, inI64_iff, Bool.false_eq_true, ite_false]
  split_ifs <;> first | rfl | omega

theorem durStep_neg (a : Int) (y : Nat) (mul : Int) (hm : 2 ≤ mul) (h5 : (5 : Int) ∣ mul) (ha : a ≤ 0) :
    durStep a y mul true = chk (a - y * mul) := by
  have h1 : 2 * (y : Int) ≤ y * mul := by nlinarith
  have h2 : (5 : Int) ∣ y * mul := Dvd.dvd.mul_left h5 _
  simp only [durStep, chk, inI64_iff, ite_true]
  split_ifs <;> first | rfl | omega

theorem durInit_eq (ms : Nat) (neg : Bool) :
    durInit ms neg = chk (if neg then -(ms : Int) else ms) := by
  cases neg <;> simp only [durInit, chk, inI64_iff, ite_true, Bool.false_eq_true, ite_false] <;>
    split_ifs <;> first | rfl | omega

theorem chk_bind_step (x : Int) (y : Nat) (mul : Int) (hm : 2 ≤ mul) (h5 : (5 : Int) ∣ mul) (neg : Bool)
    (hx : if neg then x ≤ 0 else 0 ≤ x) (k : Int → Option Int) :
    (chk x).bind (fun a => (durStep a y mul neg).bind k) =
      (chk (if neg then x - y * mul else x + y * mul)).bind k := by
  unfold chk
  by_cases hin : inI64 x = true
  · simp only [hin, ite_true, Option.bind_some]
    cases neg
    · simp only [Bool.false_eq_true, ite_false] at hx ⊢; rw [durStep_pos _ _ _ hm hx]; rfl
    · simp only [ite_true] at hx ⊢; rw [durStep_neg _ _ _ hm h5 hx]; rfl
  · have h1 : (y : Int) ≤ y * mul := by nlinarith
    simp only [hin, Bool.false_eq_true, ite_false, Option.bind_none]
    rw [inI64_iff] at hin
    cases neg <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hx ⊢ <;>
      (rw [if_neg (by rw [inI64_iff]; omega)]; rfl)

theorem chk_bind_step_last (x : Int) (y : Nat) (mul : Int) (hm : 2 ≤ mul) (h5 : (5 : Int) ∣ mul)
    (neg : Bool) (hx : if neg then x ≤ 0 else 0 ≤ x) :
    (chk x).bind (fun a => durStep a y mul neg) = chk (if neg then x - y * mul else x + y * mul) := by
  have := chk_bind_step x y mul hm h5 neg hx some
  simpa using this

/-- The chain of checked steps of the model computes the total, checked once -/
theorem chain_eq (ms sec m h d : Nat) (neg : Bool) :
    ((durInit ms neg).bind fun a0 => (durStep a0 sec 1000 neg).bind fun a1 =>
      (durStep a1 m 60000 neg).bind fun a2 => (durStep a2 h 3600000 neg).bind fun a3 =>
        durStep a3 d 86400000 neg) =
      chk ((if neg then -1 else 1) * ((d : Int) * 86400000 + h * 3600000 + m * 60000 + sec * 1000 + ms)) := by
  rw [durInit_eq]
  rw [chk_bind_step _ _ _ (by omega) (by decide) _ (by cases neg <;> simp)]
  rw [chk_bind_step _ _ _ (by omega) (by decide) _ (by cases neg <;> simp <;> omega)]
  rw [chk_bind_step _ _ _ (by omega) (by decide) _ (by cases neg <;> simp <;> omega)]
  rw [chk_bind_step_last _ _ _ (by omega) (by decide) _ (by cases neg <;> simp <;> omega)]
  congr 1
  cases neg <;> simp <;> ring

/-! ## Bodies -/

/-- The body of a duration with the given units -/
def bodyL (D H M S MS : Option (List Char)) : List Char :=
  chunkL D 'd' ++ chunkL H 'h' ++ chunkL M 'm' ++ chunkL S 's' ++ chunkMs MS

theorem qok_some {ds : List Char} : QOk (some ds) ↔ ds ≠ [] ∧ allDigits ds = true := Iff.rfl

theorem digit_d : 'd'.isDigit = false := by decide
theorem digit_h : 'h'.isDigit = false := by decide
theorem digit_m : 'm'.isDigit = false := by decide
theorem digit_s : 's'.isDigit = false := by decide

set_option maxHeartbeats 4000000 in
theorem regex_bodyL (D H M S MS : Option (List Char)) (hD : QOk D) (hH : QOk H) (hM : QOk M)
    (hS : QOk S) (hMS : QOk MS) (l : List Char) (hb : durBody l = bodyL D H M S MS) :
    durationRegex l = some ⟨D, H, M, S, MS⟩ := by
  simp only [durationRegex, hb, bodyL]
  cases D <;> cases H <;> cases M <;> cases S <;> cases MS <;>
    simp only [QOk, true_and, and_true] at hD hH hM hS hMS <;>
    simp [chunkL, chunkMs, List.append_assoc, takeUnit_digits, takeUnit_nil, takeMs_digits, takeMs_nil,
      head?_digits, head?_getD_digits, takeChar, digit_d, digit_h, digit_m, digit_s, *]

theorem bodyL_cases (D H M S MS : Option (List Char)) (hD : QOk D) (hH : QOk H) (hM : QOk M)
    (hS : QOk S) (hMS : QOk MS) :
    (D = none ∧ H = none ∧ M = none ∧ S = none ∧ MS = none ∧ bodyL D H M S MS = []) ∨
    ∃ ds rest, ds ≠ [] ∧ allDigits ds = true ∧ bodyL D H M S MS = ds ++ rest := by
  cases D with
  | some ds => exact Or.inr ⟨ds, _, hD.1, hD.2, by simp only [bodyL, chunkL, List.append_assoc]; rfl⟩
  | none =>
  cases H with
  | some ds => exact Or.inr ⟨ds, _, hH.1, hH.2, by simp only [bodyL, chunkL, List.append_assoc]; rfl⟩
  | none =>
  cases M with
  | some ds => exact Or.inr ⟨ds, _, hM.1, hM.2, by simp only [bodyL, chunkL, List.append_assoc]; rfl⟩
  | none =>
  cases S with
  | some ds => exact Or.inr ⟨ds, _, hS.1, hS.2, by simp only [bodyL, chunkL, List.append_assoc]; rfl⟩
  | none =>
  cases MS with
  | some ds => exact Or.inr ⟨ds, _, hMS.1, hMS.2, by simp only [bodyL, chunkL, chunkMs, List.append_assoc]; rfl⟩
  | none => exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, by simp [bodyL, chunkL, chunkMs]⟩

/-! ## Values -/

/-- The quantity of a unit -/
def qv : Option (List Char) → Nat
  | none => 0
  | some ds => digitsVal 0 ds

theorem durQuantity_eq (q : Option (List Char)) (hq : QOk q) :
    durQuantity q = if qv q ≤ Aeneas.Std.U64.max then some (qv q) else none := by
  cases q with
  | none => simp [durQuantity, qv]
  | some ds => simp only [durQuantity, qv]; exact parseU64'_digits ds hq.1 hq.2

/-- The value of a duration with the given sign and units -/
def durVal (neg : Bool) (D H M S MS : Option (List Char)) : Int :=
  (if neg then -1 else 1) * ((qv D : Int) * 86400000 + qv H * 3600000 + qv M * 60000 + qv S * 1000 + qv MS)

set_option maxHeartbeats 4000000 in
theorem parseDuration_of_regex {l : List Char} {D H M S MS : Option (List Char)} (hD : QOk D) (hH : QOk H)
    (hM : QOk M) (hS : QOk S) (hMS : QOk MS) (hl : l ≠ []) (hl' : l ≠ ['-'])
    (hr : durationRegex l = some ⟨D, H, M, S, MS⟩) :
    parseDuration l = chk (durVal (decide (l.head? = some '-')) D H M S MS) := by
  simp only [parseDuration, hl, hl', hr, ite_false, durQuantity_eq _ hD, durQuantity_eq _ hH,
    durQuantity_eq _ hM, durQuantity_eq _ hS, durQuantity_eq _ hMS]
  rw [U64_max_eq]
  split_ifs <;> simp only [chain_eq, durVal]
  all_goals (simp only [chk, inI64_iff]; split_ifs <;> first | rfl | (exfalso; omega))

/-! ## Inversion -/

theorem takeUnit_inv {u : Char} {noS : Bool} {l : List Char} {q : Option (List Char)} {r : List Char}
    (h : takeUnit u noS l = (q, r)) : QOk q ∧ l = chunkL q u ++ r := by
  unfold takeUnit at h
  split at h
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [QOk, chunkL]
  · rename_i hne
    split at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [QOk, chunkL]
    · rename_i c rest2 hdrop
      split at h
      · split at h
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [QOk, chunkL]
        · rename_i hcu _
          simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨⟨hne, ?_⟩, ?_⟩
          · simp only [allDigits]; exact List.all_takeWhile
          · subst hcu
            have := List.takeWhile_append_dropWhile (p := Char.isDigit) (l := l)
            rw [hdrop] at this
            conv_lhs => rw [← this]
            simp [chunkL]
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [QOk, chunkL]

theorem takeChar_some' {c : Char} {l r : List Char} (h : takeChar c l = some r) : l = c :: r := by
  cases l with
  | nil => simp [takeChar] at h
  | cons d l =>
    simp only [takeChar] at h
    split at h
    · simp_all
    · simp at h

theorem takeMs_inv {l : List Char} {q : Option (List Char)} {r : List Char}
    (h : takeMs l = (q, r)) : QOk q ∧ l = chunkMs q ++ r := by
  unfold takeMs at h
  split at h
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [QOk, chunkMs]
  · rename_i hne
    split at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [QOk, chunkMs]
    · rename_i r1 h1
      split at h
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [QOk, chunkMs]
      · rename_i r2 h2
        simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨⟨hne, ?_⟩, ?_⟩
        · simp only [allDigits]; exact List.all_takeWhile
        · have := List.takeWhile_append_dropWhile (p := Char.isDigit) (l := l)
          rw [takeChar_some' h1, takeChar_some' h2] at this
          conv_lhs => rw [← this]
          simp [chunkMs]

theorem regex_inv {l : List Char} {p : DP} (h : durationRegex l = some p) :
    QOk p.d ∧ QOk p.h ∧ QOk p.m ∧ QOk p.s ∧ QOk p.ms ∧ durBody l = bodyL p.d p.h p.m p.s p.ms := by
  unfold durationRegex at h
  set t1 := takeUnit 'd' false (durBody l) with ht1
  set t2 := takeUnit 'h' false t1.2 with ht2
  set t3 := takeUnit 'm' true t2.2 with ht3
  set t4 := takeUnit 's' false t3.2 with ht4
  set t5 := takeMs t4.2 with ht5
  obtain ⟨q1, e1⟩ := takeUnit_inv (show takeUnit 'd' false (durBody l) = (t1.1, t1.2) from rfl)
  obtain ⟨q2, e2⟩ := takeUnit_inv (show takeUnit 'h' false t1.2 = (t2.1, t2.2) from rfl)
  obtain ⟨q3, e3⟩ := takeUnit_inv (show takeUnit 'm' true t2.2 = (t3.1, t3.2) from rfl)
  obtain ⟨q4, e4⟩ := takeUnit_inv (show takeUnit 's' false t3.2 = (t4.1, t4.2) from rfl)
  obtain ⟨q5, e5⟩ := takeMs_inv (show takeMs t4.2 = (t5.1, t5.2) from rfl)
  simp only at h
  split at h
  · rename_i hr5
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨q1, q2, q3, q4, q5, ?_⟩
    change t5.2 = [] at hr5
    show durBody l = bodyL t1.1 t2.1 t3.1 t4.1 t5.1
    simp only [bodyL]
    rw [e1, e2, e3, e4, e5, hr5]
    simp only [List.append_nil, List.append_assoc]
  · simp at h

/-! ## Correspondence with the grammar -/

def optL (q : Option String) : Option (List Char) := q.map String.toList

theorem toList_asString (c : Components) :
    c.asString.toList = bodyL (optL c.days) (optL c.hours) (optL c.minutes) (optL c.seconds)
      (optL c.milliseconds) := by
  simp only [Components.asString, String.toList_append, bodyL, optL]
  cases c.days <;> cases c.hours <;> cases c.minutes <;> cases c.seconds <;> cases c.milliseconds <;>
    simp [Cedar.Thm.Duration.durationChunk, chunkL, chunkMs]

theorem qok_optL {q : Option String} (h : IsWfOptionalQuantity q) : QOk (optL q) := by
  cases q with
  | none => trivial
  | some ds =>
    have := (isDigits_ofList ds.toList).1 (by simpa [Cedar.Thm.Duration.IsWfOptionalQuantity] using h)
    exact this

theorem qv_optL {q : Option String} (h : IsWfOptionalQuantity q) : qv (optL q) = optionalNatOf q := by
  cases q with
  | none => rfl
  | some ds =>
    have := (isDigits_ofList ds.toList).1 (by simpa [Cedar.Thm.Duration.IsWfOptionalQuantity] using h)
    simp only [qv, optL, Option.map_some, optionalNatOf]
    rw [← natOf_ofList _ this, String.ofList_toList]

theorem parseDuration_complete {l : List Char} {v : Int} (h : IsDurationValue (String.ofList l) v) :
    parseDuration l = chk v := by
  obtain ⟨sign, c, ⟨hstr, hsign, hne, hq⟩, rfl⟩ := h
  obtain ⟨qd, qh, qm, qs, qms⟩ := hq
  have hl : l = sign.toList ++ c.asString.toList := by
    rw [← String.toList_append, ← hstr, String.toList_ofList]
  rw [toList_asString] at hl
  have hD := qok_optL qd
  have hH := qok_optL qh
  have hM := qok_optL qm
  have hS := qok_optL qs
  have hMS := qok_optL qms
  rcases bodyL_cases _ _ _ _ _ hD hH hM hS hMS with ⟨e1, e2, e3, e4, e5, _⟩ | ⟨ds, rest, hds, hdd, hb⟩
  · exfalso
    simp only [optL, Option.map_eq_none_iff] at e1 e2 e3 e4 e5
    rcases hne with h | h | h | h | h <;> exact h (by assumption)
  · rw [hb] at hl
    have hval : Cedar.Thm.Duration.value sign c =
        durVal (decide (sign = "-")) (optL c.days) (optL c.hours) (optL c.minutes) (optL c.seconds)
          (optL c.milliseconds) := by
      simp only [Cedar.Thm.Duration.value, Components.toMillis, durVal, qv_optL qd, qv_optL qh,
        qv_optL qm, qv_optL qs, qv_optL qms, Datetime.MILLISECONDS_PER_DAY,
        Datetime.MILLISECONDS_PER_HOUR, Datetime.MILLISECONDS_PER_MINUTE, Datetime.MILLISECONDS_PER_SECOND]
      rcases hsign with rfl | rfl <;> simp [signOf]
    rw [hval]
    have hds' : ds = ds.head! :: ds.tail := by cases ds <;> simp_all
    have hhd : ds.head!.isDigit = true := by
      cases ds with
      | nil => contradiction
      | cons d ds => simp only [allDigits, List.all_cons, Bool.and_eq_true] at hdd; simpa using hdd.1
    have hneg : ds.head! ≠ '-' := by intro h; rw [h] at hhd; simp at hhd
    rcases hsign with rfl | rfl
    · have hl1 : l = '-' :: (ds ++ rest) := by simpa using hl
      rw [parseDuration_of_regex hD hH hM hS hMS (by simp [hl1]) (by rw [hl1]; intro h; simp at h; exact hds h.1)
        (regex_bodyL _ _ _ _ _ hD hH hM hS hMS l (by rw [hl1, ← hb]; simp [durBody]))]
      simp [hl1]
    · have hl1 : l = ds ++ rest := by simpa using hl
      have hhead : l.head? = some ds.head! := by rw [hl1, hds']; simp
      rw [parseDuration_of_regex hD hH hM hS hMS (by rw [hl1, hds']; simp)
        (by rw [hl1, hds']; intro h; simp at h; exact hneg h.1)
        (regex_bodyL _ _ _ _ _ hD hH hM hS hMS l (by rw [hl1, durBody_digits hds hdd, ← hb]))]
      simp [hhead, hneg]

theorem parseDuration_sound {l : List Char} {v : Int} (h : parseDuration l = some v) :
    IsWfDuration (String.ofList l) := by
  unfold parseDuration at h
  split_ifs at h with h0 h1
  split at h; · simp at h
  rename_i p hp
  obtain ⟨qd, qh, qm, qs, qms, hb⟩ := regex_inv hp
  have hne : ¬ (p.d = none ∧ p.h = none ∧ p.m = none ∧ p.s = none ∧ p.ms = none) := by
    rintro ⟨e1, e2, e3, e4, e5⟩
    rw [e1, e2, e3, e4, e5] at hb
    simp only [bodyL, chunkL, chunkMs, List.append_nil] at hb
    cases l with
    | nil => exact h0 rfl
    | cons c rest =>
      simp only [durBody] at hb
      split at hb
      · subst hb; rename_i hc; exact h1 (by rw [hc])
      · simp at hb
  let c : Components := ⟨p.d.map String.ofList, p.h.map String.ofList, p.m.map String.ofList,
    p.s.map String.ofList, p.ms.map String.ofList⟩
  have hoptL : ∀ q : Option (List Char), optL (q.map String.ofList) = q := by
    intro q; cases q <;> simp [optL]
  have hwfq : ∀ q : Option (List Char), QOk q → IsWfOptionalQuantity (q.map String.ofList) := by
    intro q hq; cases q with
    | none => trivial
    | some ds => exact (isDigits_ofList ds).2 hq
  have hcs : c.asString.toList = durBody l := by
    rw [toList_asString, hb]; simp only [c, hoptL]
  cases l with
  | nil => exact absurd rfl h0
  | cons x rest =>
    by_cases hx : x = '-'
    · subst hx
      refine ⟨"-", c, ?_, Or.inl rfl, ?_, ⟨hwfq _ qd, hwfq _ qh, hwfq _ qm, hwfq _ qs, hwfq _ qms⟩⟩
      · apply String.toList_inj.mp
        rw [String.toList_append, hcs]; simp [durBody]
      · simp only [Components.nonempty, c, ne_eq, Option.map_eq_none_iff]
        by_contra hc; simp only [not_or, not_not] at hc; exact hne hc
    · refine ⟨"", c, ?_, Or.inr rfl, ?_, ⟨hwfq _ qd, hwfq _ qh, hwfq _ qm, hwfq _ qs, hwfq _ qms⟩⟩
      · apply String.toList_inj.mp
        rw [String.toList_append, hcs]; simp [durBody, hx]
      · simp only [Components.nonempty, c, ne_eq, Option.map_eq_none_iff]
        by_contra hc; simp only [not_or, not_not] at hc; exact hne hc

public theorem parseDuration_eq (l : List Char) :
    parseDuration l = (Datetime.Duration.parse (String.ofList l)).map (fun d => d.val.toInt) := by
  cases hp : Datetime.Duration.parse (String.ofList l) with
  | some d =>
    rw [parseDuration_complete (parse_sound _ d hp)]
    have h1 := Int64.toInt_lt d.val
    have h2 := Int64.le_toInt d.val
    simp only [chk, inI64_iff, Option.map_some]
    rw [if_pos (by omega)]
  | none =>
    rcases (parse_eq_none_iff _).1 hp with hnwf | ⟨v, hv, hov⟩
    · cases hq : parseDuration l with
      | none => rfl
      | some v => exact absurd (parseDuration_sound hq) hnwf
    · rw [parseDuration_complete hv]
      simp only [chk, inI64_iff, Option.map_none]
      simp only [Int64.MIN, Int64.MAX] at hov
      rw [if_neg (by omega)]

end

end CedarRustModel.XL
