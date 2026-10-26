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

public import CedarRustModel.Ext.Basic
public import Cedar.Thm.Data.String
import all Cedar.Thm.Data.String
import all Cedar.Spec.Ext.Util
import all Cedar.Data.Int64
import all Cedar.Thm.Ext.Datetime.Lemmas

/-! Pure lemmas about the shadows of `Ext.Basic`, and their relation to the
string predicates of the Lean grammars (`Cedar.Thm.Data.String`). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CedarRustModel.XL

open Cedar.Spec.Ext String Aeneas.Std

public section

/-! ## Digits -/

theorem digitsVal_cons (acc : Nat) (c : Char) (l : List Char) :
    digitsVal acc (c :: l) = digitsVal (acc * 10 + (c.toNat - 48)) l := by
  simp only [digitsVal, List.foldl_cons]

theorem digitsVal_eq (acc : Nat) (l : List Char) :
    digitsVal acc l = acc * 10 ^ l.length + digitsVal 0 l := by
  induction l generalizing acc with
  | nil => simp [digitsVal]
  | cons c l ih =>
    rw [digitsVal_cons, digitsVal_cons, ih, ih (0 * 10 + _)]
    simp only [List.length_cons, Nat.pow_succ]
    ring

theorem digitsVal_lt (l : List Char) (h : allDigits l = true) : digitsVal 0 l < 10 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [digitsVal]
  | append_singleton l c ih =>
    simp only [allDigits, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h
    have hc := (isDigit_iff c).1 h.2
    have := ih h.1
    simp only [digitsVal, List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton, Nat.pow_succ] at this ⊢
    omega

theorem allDigits_append (a b : List Char) : allDigits (a ++ b) = (allDigits a && allDigits b) := by
  simp [allDigits]

theorem digitsVal_append (a b : List Char) :
    digitsVal 0 (a ++ b) = digitsVal 0 a * 10 ^ b.length + digitsVal 0 b := by
  simp only [digitsVal, List.foldl_append]
  exact digitsVal_eq _ b

theorem digI64_cons (neg : Bool) (acc : Int) (c : Char) (l : List Char) :
    digI64 neg acc (c :: l) =
      if c.isDigit ∧ inI64 (acc * 10) ∧
        inI64 (if neg then acc * 10 - (c.toNat - 48 : Nat) else acc * 10 + (c.toNat - 48 : Nat))
      then digI64 neg (if neg then acc * 10 - (c.toNat - 48 : Nat) else acc * 10 + (c.toNat - 48 : Nat)) l
      else none := by
  simp only [digI64]

/-- The closed form of `digI64` -/
theorem digI64_eq (neg : Bool) (acc : Int) (l : List Char)
    (hacc : if neg then acc ≤ 0 else 0 ≤ acc) (hin : inI64 acc = true) :
    digI64 neg acc l =
      if allDigits l ∧ inI64 (if neg then acc * 10 ^ l.length - digitsVal 0 l
          else acc * 10 ^ l.length + digitsVal 0 l)
      then some (if neg then acc * 10 ^ l.length - digitsVal 0 l else acc * 10 ^ l.length + digitsVal 0 l)
      else none := by
  induction l generalizing acc with
  | nil => simp_all [digI64, digitsVal]
  | cons c l ih =>
    rw [digI64_cons]
    by_cases hc : c.isDigit = true
    · have hcv := (isDigit_iff c).1 hc
      have hD : (digitsVal 0 (c :: l) : Int) = (c.toNat - 48 : Nat) * 10 ^ l.length + digitsVal 0 l := by
        rw [digitsVal_cons, digitsVal_eq]; push_cast; ring
      have hP : (1 : Int) ≤ 10 ^ l.length := by
        have := Nat.one_le_pow l.length 10 (by omega); exact_mod_cast this
      have hDl : (0 : Int) ≤ digitsVal 0 l := by positivity
      have hd0 : (0 : Int) ≤ ((c.toNat - 48 : Nat) : Int) := by positivity
      simp only [List.length_cons, pow_succ, allDigits_cons, hc, Bool.true_and, hD]
      set d := ((c.toNat - 48 : Nat) : Int) with hd
      set P := (10 : Int) ^ l.length with hPd
      set D := ((digitsVal 0 l : Nat) : Int) with hDd
      have hmin : I64.min ≤ 0 := by scalar_tac
      have hmax : 0 ≤ I64.max := by scalar_tac
      simp only [inI64, decide_eq_true_eq, true_and] at hin ih ⊢
      cases neg with
      | true =>
        simp only [ite_true] at hacc ih ⊢
        have e : acc * (P * 10) - (d * P + D) = (acc * 10 - d) * P - D := by ring
        rw [e]
        by_cases h1 : I64.min ≤ acc * 10 ∧ acc * 10 ≤ I64.max
        · by_cases h2 : I64.min ≤ acc * 10 - d ∧ acc * 10 - d ≤ I64.max
          · rw [if_pos ⟨h1, h2⟩, ih _ (by omega) h2]
          · rw [if_neg (by tauto)]
            have : acc * 10 - d < I64.min := by
              by_contra hh; apply h2; constructor <;> omega
            have : (acc * 10 - d) * P ≤ acc * 10 - d := by nlinarith
            rw [if_neg]; intro ⟨_, h3, _⟩; omega
        · rw [if_neg (by tauto)]
          have : acc * 10 < I64.min := by
            by_contra hh; apply h1; constructor <;> omega
          have : (acc * 10 - d) * P ≤ acc * 10 - d := by nlinarith
          rw [if_neg]; intro ⟨_, h3, _⟩; omega
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hacc ih ⊢
        have e : acc * (P * 10) + (d * P + D) = (acc * 10 + d) * P + D := by ring
        rw [e]
        by_cases h1 : I64.min ≤ acc * 10 ∧ acc * 10 ≤ I64.max
        · by_cases h2 : I64.min ≤ acc * 10 + d ∧ acc * 10 + d ≤ I64.max
          · rw [if_pos ⟨h1, h2⟩, ih _ (by omega) h2]
          · rw [if_neg (by tauto)]
            have : I64.max < acc * 10 + d := by
              by_contra hh; apply h2; constructor <;> omega
            have : acc * 10 + d ≤ (acc * 10 + d) * P := by nlinarith
            rw [if_neg]; intro ⟨_, _, h3⟩; omega
        · rw [if_neg (by tauto)]
          have : I64.max < acc * 10 := by
            by_contra hh; apply h1; constructor <;> omega
          have : acc * 10 + d ≤ (acc * 10 + d) * P := by nlinarith
          rw [if_neg]; intro ⟨_, _, h3⟩; omega
    · simp [hc]

theorem digU64_eq (acc : Nat) (l : List Char) (hin : acc ≤ U64.max) :
    digU64 acc l =
      if allDigits l ∧ acc * 10 ^ l.length + digitsVal 0 l ≤ U64.max
      then some (acc * 10 ^ l.length + digitsVal 0 l) else none := by
  induction l generalizing acc with
  | nil => simp_all [digU64, digitsVal]
  | cons c l ih =>
    simp only [digU64]
    by_cases hc : c.isDigit = true
    · have hcv := (isDigit_iff c).1 hc
      have hD : digitsVal 0 (c :: l) = (c.toNat - 48) * 10 ^ l.length + digitsVal 0 l := by
        rw [digitsVal_cons, digitsVal_eq]; ring
      have hP : 1 ≤ 10 ^ l.length := Nat.one_le_pow l.length 10 (by omega)
      simp only [List.length_cons, pow_succ, allDigits_cons, hc, Bool.true_and, hD]
      set d := c.toNat - 48 with hd
      set P := 10 ^ l.length with hPd
      set D := digitsVal 0 l with hDd
      have e : acc * (P * 10) + (d * P + D) = (acc * 10 + d) * P + D := by ring
      rw [e]
      by_cases h1 : acc * 10 ≤ U64.max ∧ acc * 10 + d ≤ U64.max
      · rw [if_pos ⟨trivial, h1⟩, ih _ h1.2]
      · rw [if_neg (by tauto)]
        have : U64.max < acc * 10 + d := by omega
        have : acc * 10 + d ≤ (acc * 10 + d) * P := Nat.le_mul_of_pos_right _ hP
        rw [if_neg]; intro ⟨_, h3⟩; omega
    · simp [hc]

theorem parseI64'_eq (l : List Char) :
    parseI64' l =
      match l with
      | [] => none
      | c :: rest =>
        if c = '-' then
          (if rest ≠ [] ∧ allDigits rest ∧ inI64 (-(digitsVal 0 rest : Int))
           then some (-(digitsVal 0 rest : Int)) else none)
        else if c = '+' then
          (if rest ≠ [] ∧ allDigits rest ∧ inI64 (digitsVal 0 rest)
           then some (digitsVal 0 rest : Int) else none)
        else (if allDigits l ∧ inI64 (digitsVal 0 l) then some (digitsVal 0 l : Int) else none) := by
  have h0 : inI64 0 = true := by simp [inI64]; scalar_tac
  cases l with
  | nil => rfl
  | cons c rest =>
    simp only [parseI64']
    by_cases hm : c = '-'
    · simp only [hm, ite_true]
      by_cases hr : rest = [] <;> simp [hr, digI64_eq true 0 rest (by simp) h0]
    · by_cases hp : c = '+'
      · simp only [hp, ite_true, show ('+' = '-') = False by decide, ite_false]
        by_cases hr : rest = [] <;> simp [hr, digI64_eq false 0 rest (by simp) h0]
      · simp [hm, hp, digI64_eq false 0 _ (by simp) h0]

theorem parseU64'_eq (l : List Char) :
    parseU64' l =
      match l with
      | [] => none
      | c :: rest =>
        if c = '+' then
          (if rest ≠ [] ∧ allDigits rest ∧ digitsVal 0 rest ≤ U64.max
           then some (digitsVal 0 rest) else none)
        else (if allDigits l ∧ digitsVal 0 l ≤ U64.max then some (digitsVal 0 l) else none) := by
  have h0 : 0 ≤ U64.max := by scalar_tac
  cases l with
  | nil => rfl
  | cons c rest =>
    simp only [parseU64']
    by_cases hp : c = '+'
    · simp only [hp, ite_true]
      by_cases hr : rest = [] <;> simp [hr, digU64_eq 0 rest h0]
    · simp [hp, digU64_eq 0 _ h0]

/-- `parse_u64` on a nonempty list of digits -/
theorem parseU64'_digits (l : List Char) (hl : l ≠ []) (hd : allDigits l = true) :
    parseU64' l = if digitsVal 0 l ≤ U64.max then some (digitsVal 0 l) else none := by
  rw [parseU64'_eq]
  cases l with
  | nil => contradiction
  | cons c rest =>
    have : c ≠ '+' := by
      intro h; subst h; simp [allDigits] at hd
    simp [this, hd]

/-- `parse_i64` on a nonempty list of digits -/
theorem parseI64'_digits (l : List Char) (hl : l ≠ []) (hd : allDigits l = true) :
    parseI64' l = if inI64 (digitsVal 0 l) then some (digitsVal 0 l : Int) else none := by
  rw [parseI64'_eq]
  cases l with
  | nil => contradiction
  | cons c rest =>
    have h1 : c ≠ '+' := by
      intro h; subst h; simp [allDigits] at hd
    have h2 : c ≠ '-' := by
      intro h; subst h; simp [allDigits] at hd
    simp [h1, h2, hd]

/-- `parse_i64` on `-` followed by a nonempty list of digits -/
theorem parseI64'_neg_digits (l : List Char) (hl : l ≠ []) (hd : allDigits l = true) :
    parseI64' ('-' :: l) = if inI64 (-(digitsVal 0 l : Int)) then some (-(digitsVal 0 l : Int)) else none := by
  rw [parseI64'_eq]; simp [hl, hd]

theorem I64_max_eq : I64.max = 9223372036854775807 := by scalar_tac
theorem I64_min_eq : I64.min = -9223372036854775808 := by scalar_tac
theorem U64_max_eq : U64.max = 18446744073709551615 := by scalar_tac

theorem inI64_iff (v : Int) :
    inI64 v = true ↔ -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807 := by
  simp [inI64, I64_max_eq, I64_min_eq]

theorem chk_eq (v : Int) :
    chk v = if -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807 then some v else none := by
  simp only [chk]; by_cases h : inI64 v = true
  · rw [if_pos h, if_pos ((inI64_iff v).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((inI64_iff v).2 h'))]

theorem toInt_range (d : Int64) : -9223372036854775808 ≤ d.toInt ∧ d.toInt ≤ 9223372036854775807 := by
  have h := Int64.ofInt?_toInt d
  unfold Int64.ofInt? at h
  split at h
  · rename_i hr; simp only [Int64.MIN, Int64.MAX] at hr; omega
  · simp at h

theorem ofInt_toInt' (v : Int) (h : -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807) :
    (Int64.ofInt v).toInt = v :=
  Int64.ofInt?_some_toInt (Int64.ofInt?_some_iff.mp (by simp [Int64.MIN, Int64.MAX]; omega))

/-! ## Splitting -/

theorem splitFirst_append (c : Char) (a b : List Char) (h : c ∉ a) :
    splitFirst c (a ++ c :: b) = some (a, b) := by
  induction a with
  | nil => simp [splitFirst]
  | cons d a ih =>
    simp only [List.mem_cons, not_or] at h
    simp [splitFirst, Ne.symm h.1, ih h.2]

theorem splitFirst_some {c : Char} {l a b : List Char} (h : splitFirst c l = some (a, b)) :
    l = a ++ c :: b ∧ c ∉ a := by
  induction l generalizing a b with
  | nil => simp [splitFirst] at h
  | cons d l ih =>
    simp only [splitFirst] at h
    split at h
    · simp_all
    · rename_i hd
      cases hs : splitFirst c l with
      | none => simp [hs] at h
      | some p =>
        obtain ⟨a', b'⟩ := p
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := ih hs
        subst h1
        simp [Ne.symm hd, h2]

theorem splitFirst_none {c : Char} {l : List Char} (h : splitFirst c l = none) : c ∉ l := by
  induction l with
  | nil => simp
  | cons d l ih =>
    simp only [splitFirst] at h
    split at h
    · simp at h
    · rename_i hd
      cases hs : splitFirst c l with
      | none => simp [Ne.symm hd, ih hs]
      | some p => simp [hs] at h

theorem not_mem_of_allDigits {c : Char} {l : List Char} (hc : c.isDigit = false) (h : allDigits l = true) :
    c ∉ l := by
  intro hm
  simp only [allDigits, List.all_eq_true] at h
  have := h c hm; simp_all

/-! ## Strings -/

theorem isDigits_ofList (l : List Char) : IsDigits (String.ofList l) ↔ l ≠ [] ∧ allDigits l = true := by
  simp only [IsDigits, String.length_ofList, String.toList_ofList, allDigits, List.all_eq_true,
    List.length_pos_iff]

theorem natOf_ofList (l : List Char) (h : l ≠ [] ∧ allDigits l = true) :
    natOf (String.ofList l) = digitsVal 0 l := by
  rw [Cedar.Thm.Datetime.natOf_isDigits _ ((isDigits_ofList l).2 h)]
  simp [digitsVal]

end

end CedarRustModel.XL
