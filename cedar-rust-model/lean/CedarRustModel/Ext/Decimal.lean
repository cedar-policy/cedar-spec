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

public import CedarRustModel.Ext.Bridge
public import Cedar.Thm.Ext.Decimal
import all Cedar.Thm.Data.String
import all Cedar.Spec.Ext.Decimal
import all Cedar.Thm.Ext.Decimal.Grammar
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Sub
import all Aeneas.Std.Scalar.CheckedOps.Mul

/-! The decimal parser of the model computes `XL.parseDecimal`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model

public section

@[step] theorem is_signed_digits_spec (s : value.List Char) :
    ext.is_signed_digits s ⦃ b => b = XL.isSignedDigits (List.toList s) ⦄ := by
  unfold ext.is_signed_digits
  cases s with
  | Nil => simp [XL.isSignedDigits, WP.spec_ok]
  | Cons c rest => step* <;> simp_all [XL.isSignedDigits]

@[step] theorem decimal_split_spec (s : value.List Char) :
    ext.decimal_split s ⦃ r =>
      XL.decimalSplit (List.toList s) = r.map (fun p => (List.toList p.1, List.toList p.2)) ⦄ := by
  unfold ext.decimal_split
  step*
  all_goals (try obtain ⟨_, _⟩ := p)
  all_goals (try step*)
  all_goals (subst_vars; simp_all [XL.decimalSplit])

@[step] theorem frac_scale_spec (s : value.List Char) :
    ext.frac_scale s ⦃ r => XL.fracScale (List.toList s) = r.map (·.val) ⦄ := by
  unfold ext.frac_scale
  rcases s with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
    simp [XL.fracScale, WP.spec_ok] <;> decide

theorem checked_val_some {o : Option I64} {a : I64} {v : Option Int} (h : o.map (·.val) = v)
    (ho : o = some a) : v = some a.val := by rw [← h, ho]; rfl

@[step] theorem parse_decimal_spec (s : value.List Char) :
    ext.parse_decimal s ⦃ r => XL.parseDecimal (List.toList s) = r.map (·.val) ⦄ := by
  unfold ext.parse_decimal
  step*
  all_goals (try obtain ⟨_, _⟩ := p)
  all_goals (try step*)
  all_goals (subst_vars; simp_all [XL.parseDecimal, XL.chk, checked_sub_eq, checked_add_eq])

end -- public section

/-! ## The shadow and the Lean grammar -/

namespace XL

open Cedar.Spec.Ext Cedar.Thm Cedar.Thm.Decimal String

public section

theorem fracScale_eq (b : List Char) (h1 : b ≠ []) (h2 : b.length ≤ 4) :
    fracScale b = some (10 ^ (4 - b.length) : Int) := by
  have : 0 < b.length := List.length_pos_iff.2 h1
  unfold fracScale
  obtain h | h | h | h : b.length = 1 ∨ b.length = 2 ∨ b.length = 3 ∨ b.length = 4 := by omega
  all_goals (rw [h]; rfl)

theorem fracScale_some {b : List Char} {k : Int} (h : fracScale b = some k) :
    b ≠ [] ∧ b.length ≤ 4 := by
  unfold fracScale at h
  split at h <;> simp at h <;> rename_i _ h' <;>
    exact ⟨fun hb => by subst hb; simp at h', by omega⟩

/-- The decimal parser on a decomposed literal -/
theorem parseDecimal_parts (sg : Bool) (n b : List Char) (hn : n ≠ [] ∧ allDigits n = true)
    (hb : b ≠ [] ∧ allDigits b = true) (hlen : b.length ≤ 4) :
    parseDecimal ((if sg then '-' :: n else n) ++ '.' :: b) =
      chk ((if sg then -1 else 1) *
        ((digitsVal 0 n : Int) * 10000 + (digitsVal 0 b : Int) * 10 ^ (4 - b.length))) := by
  have hdot : '.' ∉ (if sg then '-' :: n else n) := by
    have := not_mem_of_allDigits (c := '.') (by decide) hn.2
    cases sg <;> simp [this]
  have hhead : ∀ c, n.head? = some c → c ≠ '-' := by
    intro c hc h; subst h
    cases n with
    | nil => simp at hc
    | cons d n => simp at hc; subst hc; simp [allDigits] at hn
  have hsd : isSignedDigits (if sg then '-' :: n else n) = true := by
    cases sg
    · cases n with
      | nil => exact absurd rfl hn.1
      | cons d n' =>
        have := hhead d rfl
        simp [isSignedDigits, this, hn.2]
    · simp [isSignedDigits, hn.1, hn.2]
  have hsplit : decimalSplit ((if sg then '-' :: n else n) ++ '.' :: b) =
      some ((if sg then '-' :: n else n), b) := by
    simp [decimalSplit, splitFirst_append _ _ _ hdot, hsd, hb.1, hb.2]
  have hDb := digitsVal_lt b hb.2
  have hP : (10 : Nat) ^ b.length * 10 ^ (4 - b.length) = 10000 := by
    rw [← pow_add, show b.length + (4 - b.length) = 4 by omega]; norm_num
  have hPi : (10 : Int) ^ (4 - b.length) * 10 ^ b.length = 10000 := by
    rw [← pow_add, show 4 - b.length + b.length = 4 by omega]; norm_num
  have hFk : (digitsVal 0 b : Int) * 10 ^ (4 - b.length) < 10000 := by
    have : ((digitsVal 0 b : Nat) : Int) < 10 ^ b.length := by exact_mod_cast hDb
    have h0 : (0 : Int) < 10 ^ (4 - b.length) := by positivity
    nlinarith
  have hF0 : (0 : Int) ≤ (digitsVal 0 b : Int) * 10 ^ (4 - b.length) := by positivity
  have hFlt : inI64 (digitsVal 0 b) = true := by
    rw [inI64_iff]; have : ((digitsVal 0 b : Nat) : Int) < 10 ^ b.length := by exact_mod_cast hDb
    have : (10 : Int) ^ b.length ≤ 10000 := by
      calc (10 : Int) ^ b.length ≤ 10 ^ 4 := pow_le_pow_right₀ (by norm_num) hlen
        _ = 10000 := by norm_num
    constructor <;> omega
  simp only [parseDecimal, hsplit, fracScale_eq b hb.1 hlen, parseI64'_digits b hb.1 hb.2, hFlt,
    ite_true]
  set F := (digitsVal 0 b : Int) * 10 ^ (4 - b.length) with hFdef
  have hN0 : (0 : Int) ≤ digitsVal 0 n := by positivity
  cases sg with
  | true =>
    simp only [ite_true, parseI64'_neg_digits n hn.1 hn.2, List.head?_cons]
    set N := ((digitsVal 0 n : Nat) : Int)
    by_cases h1 : inI64 (-N) = true
    · simp only [h1, ite_true]
      by_cases h2 : inI64 (-N * 10000) = true
      · simp only [h2, ite_true, show inI64 F = true by rw [inI64_iff]; omega]
        simp only [chk]; rw [show -N * 10000 - F = -1 * (N * 10000 + F) by ring]
      · simp only [h2, Bool.false_eq_true, ite_false]
        rw [inI64_iff] at h2; rw [chk_eq, if_neg]; omega
    · simp only [h1, Bool.false_eq_true, ite_false]
      rw [inI64_iff] at h1; rw [chk_eq, if_neg]; omega
  | false =>
    simp only [Bool.false_eq_true, ite_false, parseI64'_digits n hn.1 hn.2]
    have hhd : (n.head? = some '-') = False := by
      cases n with
      | nil => exact absurd rfl hn.1
      | cons d n' => simp; exact hhead d rfl
    set N := ((digitsVal 0 n : Nat) : Int)
    by_cases h1 : inI64 N = true
    · simp only [h1, ite_true]
      by_cases h2 : inI64 (N * 10000) = true
      · simp only [h2, ite_true, show inI64 F = true by rw [inI64_iff]; omega, hhd, ite_false]
        simp only [chk, one_mul]
      · simp only [h2, Bool.false_eq_true, ite_false]
        rw [inI64_iff] at h2; rw [chk_eq, if_neg]; omega
    · simp only [h1, Bool.false_eq_true, ite_false]
      rw [inI64_iff] at h1; rw [chk_eq, if_neg]; omega

theorem parseDecimal_some {l : List Char} {v : Int} (h : parseDecimal l = some v) :
    ∃ (sg : Bool) (n b : List Char), l = (if sg then '-' :: n else n) ++ '.' :: b ∧ (n ≠ [] ∧ allDigits n = true) ∧
      (b ≠ [] ∧ allDigits b = true) ∧ b.length ≤ 4 := by
  unfold parseDecimal at h
  cases hs : decimalSplit l with
  | none => simp [hs] at h
  | some p =>
    obtain ⟨a, b⟩ := p
    have hk : ∃ k, fracScale b = some k := by
      rw [hs] at h; simp only at h
      split at h; · simp at h
      split at h; swap; · simp at h
      split at h; · simp at h
      exact ⟨_, by assumption⟩
    obtain ⟨k, hk⟩ := hk
    have hb4 := (fracScale_some hk).2
    unfold decimalSplit at hs
    cases hf : splitFirst '.' l with
    | none => simp [hf] at hs
    | some q =>
      obtain ⟨a', b'⟩ := q
      simp only [hf] at hs
      split at hs; swap; · simp at hs
      rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hl, _⟩ := splitFirst_some hf
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
      obtain ⟨hsd, hbne, hbd⟩ := hc
      cases a' with
      | nil => simp [isSignedDigits] at hsd
      | cons c rest =>
        by_cases hcm : c = '-'
        · subst hcm
          simp [isSignedDigits] at hsd
          exact ⟨true, rest, b', by simp [hl], ⟨hsd.1, hsd.2⟩, ⟨hbne, hbd⟩, hb4⟩
        · simp [isSignedDigits, hcm] at hsd
          exact ⟨false, c :: rest, b', by simp [hl], ⟨by simp, by simpa [allDigits] using hsd⟩,
            ⟨hbne, hbd⟩, hb4⟩

theorem ofList_parts (sg : Bool) (n b : List Char) :
    String.ofList ((if sg then '-' :: n else n) ++ '.' :: b) =
      (if sg then "-" else "") ++ String.ofList n ++ "." ++ String.ofList b := by
  apply String.toList_inj.1
  cases sg <;> simp [String.toList_append]

theorem value_parts (sg : Bool) (n b : List Char) (hn : n ≠ [] ∧ allDigits n = true)
    (hb : b ≠ [] ∧ allDigits b = true) (hlen : b.length ≤ 4) :
    Decimal.value (if sg then "-" else "") (String.ofList n) (String.ofList b) =
      (if sg then -1 else 1) *
        ((digitsVal 0 n : Int) * 10000 + (digitsVal 0 b : Int) * 10 ^ (4 - b.length)) := by
  simp only [Decimal.value, natOf_ofList n hn, natOf_ofList b hb, lenOf, String.length_ofList,
    DECIMAL_DIGITS, signOf]
  rw [show ((4 : ℕ) : ℤ) - (b.length : ℤ) = ((4 - b.length : ℕ) : ℤ) by omega, Int.toNat_natCast]
  cases sg <;> simp [Int.pow_eq] <;> ring

theorem isDecimalValue_parts (sg : Bool) (n b : List Char) (hn : n ≠ [] ∧ allDigits n = true)
    (hb : b ≠ [] ∧ allDigits b = true) (hlen : b.length ≤ 4) :
    IsDecimalValue (String.ofList ((if sg then '-' :: n else n) ++ '.' :: b))
      ((if sg then -1 else 1) *
        ((digitsVal 0 n : Int) * 10000 + (digitsVal 0 b : Int) * 10 ^ (4 - b.length))) := by
  unfold IsDecimalValue
  refine ⟨if sg then "-" else "", String.ofList n, String.ofList b,
    ⟨ofList_parts sg n b, ?_, (isDigits_ofList n).2 hn, ⟨(isDigits_ofList b).2 hb, by simpa using hlen⟩⟩,
    (value_parts sg n b hn hb hlen).symm⟩
  cases sg <;> simp [IsWfSign]

theorem parts_of_isDecimalValue {l : List Char} {v : Int} (h : IsDecimalValue (String.ofList l) v) :
    ∃ (sg : Bool) (n b : List Char), l = (if sg then '-' :: n else n) ++ '.' :: b ∧
      (n ≠ [] ∧ allDigits n = true) ∧ (b ≠ [] ∧ allDigits b = true) ∧ b.length ≤ 4 ∧
      v = (if sg then -1 else 1) *
        ((digitsVal 0 n : Int) * 10000 + (digitsVal 0 b : Int) * 10 ^ (4 - b.length)) := by
  unfold IsDecimalValue at h
  obtain ⟨sign, natural, fraction, ⟨hs, hsign, hnat, hfrac, hlen⟩, hv⟩ := h
  have hn := (isDigits_ofList natural.toList).1 (by simpa using hnat)
  have hb := (isDigits_ofList fraction.toList).1 (by simpa using hfrac)
  have hb4 : fraction.toList.length ≤ 4 := by
    have : fraction.length ≤ 4 := hlen
    rwa [← String.length_toList] at this
  have hfl : String.ofList fraction.toList = fraction := by simp
  have hnl : String.ofList natural.toList = natural := by simp
  have hl := congrArg String.toList hs
  rw [← hnl, ← hfl] at hv
  rcases hsign with rfl | rfl
  · refine ⟨true, natural.toList, fraction.toList, ?_, hn, hb, hb4, ?_⟩
    · simpa [String.toList_append] using hl
    · rw [hv, ← value_parts true _ _ hn hb hb4]; rfl
  · refine ⟨false, natural.toList, fraction.toList, ?_, hn, hb, hb4, ?_⟩
    · simpa [String.toList_append] using hl
    · rw [hv, ← value_parts false _ _ hn hb hb4]; rfl

/-- The model's decimal parser is Lean's `Decimal.parse` -/
theorem parseDecimal_eq (l : List Char) :
    parseDecimal l = (Decimal.parse (String.ofList l)).map Int64.toInt := by
  cases hp : Decimal.parse (String.ofList l) with
  | some d =>
    obtain ⟨sg, n, b, rfl, hn, hb, hb4, hv⟩ := parts_of_isDecimalValue (parse_sound _ d hp)
    rw [parseDecimal_parts sg n b hn hb hb4, ← hv, chk_eq, if_pos (toInt_range d)]
    rfl
  | none =>
    cases hm : parseDecimal l with
    | none => rfl
    | some v =>
      exfalso
      obtain ⟨sg, n, b, rfl, hn, hb, hb4⟩ := parseDecimal_some hm
      rw [parseDecimal_parts sg n b hn hb hb4, chk_eq] at hm
      have hval := isDecimalValue_parts sg n b hn hb hb4
      generalize ((if sg = true then -1 else 1) *
        ((digitsVal 0 n : Int) * 10000 + (digitsVal 0 b : Int) * 10 ^ (4 - b.length))) = V at hm hval
      by_cases hr : -9223372036854775808 ≤ V ∧ V ≤ 9223372036854775807
      · rw [if_pos hr] at hm
        have := parse_complete _ (Int64.ofInt V) (by rw [ofInt_toInt' V hr]; exact hval)
        rw [hp] at this; simp at this
      · rw [if_neg hr] at hm; simp at hm

end

end XL


end CedarRustModel
