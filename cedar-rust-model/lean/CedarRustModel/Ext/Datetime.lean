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
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Sub
import all Aeneas.Std.Scalar.CheckedOps.Mul

/-! The datetime parser of the model computes `XL.parseDatetime`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model

@[expose] public section

namespace XL

abbrev L := _root_.List Char

def matchDate (l : L) : Option (L × L × L × L) :=
  match takeDigits 4 l with
  | none => none
  | some (y, r1) => match takeChar '-' r1 with
    | none => none
    | some r2 => match takeDigits 2 r2 with
      | none => none
      | some (m, r3) => match takeChar '-' r3 with
        | none => none
        | some r4 => match takeDigits 2 r4 with
          | none => none
          | some (d, r5) => some (y, m, d, r5)

def matchHms (l : L) : Option (L × L × L × L) :=
  match takeChar 'T' l with
  | none => none
  | some r0 => match takeDigits 2 r0 with
    | none => none
    | some (h, r1) => match takeChar ':' r1 with
      | none => none
      | some r2 => match takeDigits 2 r2 with
        | none => none
        | some (m, r3) => match takeChar ':' r3 with
          | none => none
          | some r4 => match takeDigits 2 r4 with
            | none => none
            | some (s, r5) => some (h, m, s, r5)

def matchOffset : L → Option (Option (Bool × L × L))
  | [] => none
  | c :: rest =>
    if c = 'Z' then (if rest = [] then some none else none)
    else if c = '+' ∨ c = '-' then
      match takeDigits 2 rest with
      | none => none
      | some (hh, r1) => match takeDigits 2 r1 with
        | none => none
        | some (mm, r2) => if r2 = [] then some (some (decide (c = '+'), hh, mm)) else none
    else none

def matchMsOffset (l : L) : Option (Option L × Option (Bool × L × L)) :=
  match takeChar '.' l with
  | some r0 => match takeDigits 3 r0 with
    | none => none
    | some (ms, r1) => (matchOffset r1).map fun off => (some ms, off)
  | none => (matchOffset l).map fun off => (none, off)

def smallNat (l : L) : Int :=
  match digU64 0 l with
  | some n => if n ≤ 9999 then n else 0
  | none => 0

def isLeapYear (y : Int) : Bool :=
  y.tmod 4 = 0 ∧ (y.tmod 100 ≠ 0 ∨ y.tmod 400 = 0)

def daysInMonth (y m : Int) : Int :=
  if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30
  else if m = 2 then (if isLeapYear y then 29 else 28)
  else 31

def validDate (y m d : Int) : Bool :=
  1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysInMonth y m

def daysFromCivil (y m d : Int) : Int :=
  let y1 := if m > 2 then y else y - 1
  let era := (if y1 ≥ 0 then y1 else y1 - 399).tdiv 400
  let yoe := y1 - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2).tdiv 5 + d - 1
  let doe := yoe * 365 + yoe.tdiv 4 - yoe.tdiv 100 + doy
  era * 146097 + doe - 719468

def offsetDelta : Option (Bool × L × L) → Option Int
  | none => some 0
  | some (pos, hh, mm) =>
    if smallNat hh < 24 ∧ smallNat mm < 60 then
      some (if pos then 0 - (smallNat hh * 3600 + smallNat mm * 60) else smallNat hh * 3600 + smallNat mm * 60)
    else none

def optSmallNat : Option L → Int
  | some m => smallNat m
  | none => 0

def parseTime (l : L) : Option Int :=
  match matchHms l with
  | none => none
  | some (hs, mis, ss, rest) => match matchMsOffset rest with
    | none => none
    | some (msopt, off) =>
      match offsetDelta off with
      | none => none
      | some dl =>
        if smallNat hs < 24 ∧ smallNat mis < 60 ∧ smallNat ss < 60 then
          some (((smallNat hs * 3600 + smallNat mis * 60 + smallNat ss) * 1000 +
            optSmallNat msopt) + dl * 1000)
        else none

def parseDatetime (l : L) : Option Int :=
  match matchDate l with
  | none => none
  | some (ys, mos, ds, rest) =>
    if ¬ validDate (smallNat ys) (smallNat mos) (smallNat ds) then none
    else if rest = [] then some (daysFromCivil (smallNat ys) (smallNat mos) (smallNat ds) * 86400000)
    else match parseTime rest with
      | none => none
      | some t => some (daysFromCivil (smallNat ys) (smallNat mos) (smallNat ds) * 86400000 + t)

theorem smallNat_bounds (l : L) : 0 ≤ smallNat l ∧ smallNat l ≤ 9999 := by
  unfold smallNat; split
  · split <;> omega
  · omega

end XL

end

public section

def quad (r : value.List Char × value.List Char × value.List Char × value.List Char) : XL.L × XL.L × XL.L × XL.L :=
  (List.toList r.1, List.toList r.2.1, List.toList r.2.2.1, List.toList r.2.2.2)

@[step] theorem match_date_spec (s : value.List Char) :
    ext.match_date s ⦃ r => XL.matchDate (List.toList s) = r.map quad ⦄ := by
  unfold ext.match_date
  xstep
  all_goals (subst_vars; simp_all [XL.matchDate, quad])

@[step] theorem match_hms_spec (s : value.List Char) :
    ext.match_hms s ⦃ r => XL.matchHms (List.toList s) = r.map quad ⦄ := by
  unfold ext.match_hms
  xstep
  all_goals (subst_vars; simp_all [XL.matchHms, quad])

def offToSpec (o : Option (Bool × value.List Char × value.List Char)) : Option (Bool × XL.L × XL.L) :=
  o.map fun p => (p.1, List.toList p.2.1, List.toList p.2.2)

@[step] theorem match_offset_spec (s : value.List Char) :
    ext.match_offset s ⦃ r => XL.matchOffset (List.toList s) = r.map offToSpec ⦄ := by
  unfold ext.match_offset
  cases s with
  | Nil => simp [XL.matchOffset, WP.spec_ok]
  | Cons c rest =>
    xstep
    all_goals (subst_vars; simp_all [XL.matchOffset, offToSpec])

@[step] theorem match_ms_offset_spec (s : value.List Char) :
    ext.match_ms_offset s ⦃ r => XL.matchMsOffset (List.toList s) =
      r.map (fun p => (p.1.map List.toList, offToSpec p.2)) ⦄ := by
  unfold ext.match_ms_offset
  xstep
  all_goals (subst_vars; simp_all [XL.matchMsOffset, offToSpec])

@[step] theorem lift_hcast_u64_i64 (n : U64) (h : n.val ≤ 9223372036854775807) :
    lift (UScalar.hcast .I64 n) ⦃ y => y.val = n.val ⦄ :=
  UScalar.hcast_inBounds_spec _ _ (by scalar_tac)

theorem hcast_u64_i64_val (n : U64) (h : n.val ≤ 9223372036854775807) :
    (UScalar.hcast .I64 n).val = n.val := by
  have := UScalar.hcast_inBounds_spec (tgt_ty := .I64) n (by scalar_tac)
  simpa [WP.spec_ok] using this

@[step] theorem small_nat_spec (s : value.List Char) :
    ext.small_nat s ⦃ r => r.val = XL.smallNat (List.toList s) ∧ 0 ≤ r.val ∧ r.val ≤ 9999 ⦄ := by
  unfold ext.small_nat
  step*
  all_goals (subst_vars; simp_all [XL.smallNat])
  all_goals (rw [Int.bmod_eq_of_le (by omega) (by omega)]; omega)

@[step] theorem is_leap_year_spec (y : I64) : ext.is_leap_year y ⦃ b => b = XL.isLeapYear y.val ⦄ := by
  unfold ext.is_leap_year
  step*
  all_goals (simp only [XL.isLeapYear, bne_iff_ne, ne_eq, IScalar.eq_equiv] at *)
  all_goals (first | (simp only [@eq_comm _ true, @eq_comm _ false, decide_eq_true_eq, decide_eq_false_iff_not];
                      scalar_tac)
                   | (simp only [decide_eq_decide]; scalar_tac))

@[step] theorem days_in_month_spec (y m : I64) :
    ext.days_in_month y m ⦃ r => r.val = XL.daysInMonth y.val m.val ⦄ := by
  unfold ext.days_in_month
  step*
  all_goals (subst_vars; simp_all [XL.daysInMonth])
  all_goals (split_ifs <;> simp_all <;> scalar_tac)

@[step] theorem valid_date_spec (y m d : I64) :
    ext.valid_date y m d ⦃ b => b = XL.validDate y.val m.val d.val ⦄ := by
  unfold ext.valid_date
  step*
  all_goals (subst_vars; simp_all [XL.validDate])



theorem tdiv_400_bounds (a : Int) (h1 : -400 ≤ a) (h2 : a ≤ 9999) :
    -1 ≤ a.tdiv 400 ∧ a.tdiv 400 ≤ 24 ∧ 0 ≤ a - a.tdiv 400 * 400 + (if a < 0 then 400 else 0) := by
  rcases Int.lt_or_le a 0 with ha | ha
  · have : a.tdiv 400 = -((-a).tdiv 400) := by rw [Int.neg_tdiv, neg_neg]
    rw [this, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    simp only [ha, if_true]; omega
  · rw [Int.tdiv_eq_ediv_of_nonneg ha]; simp only [show ¬ a < 0 by omega, if_false]; omega

theorem tdiv_nonneg_eq (a b : Int) (ha : 0 ≤ a) : a.tdiv b = a / b := Int.tdiv_eq_ediv_of_nonneg ha

/-- Truncating division, for `omega` -/
theorem tdiv_eq_gen (a b : Int) : a.tdiv b = if 0 ≤ a then a / b else -((-a) / b) := by
  split_ifs with h
  · exact Int.tdiv_eq_ediv_of_nonneg h
  · rw [show a = -(-a) by omega, Int.neg_tdiv, neg_neg, Int.tdiv_eq_ediv_of_nonneg (by omega)]

theorem tdiv_bounds_gen (a b : Int) (hb : 0 < b) :
    (0 ≤ a → a.tdiv b * b ≤ a ∧ a < a.tdiv b * b + b) ∧ (a < 0 → a ≤ a.tdiv b * b ∧ a.tdiv b * b < a + b) := by
  rw [tdiv_eq_gen]
  constructor
  · intro h; rw [if_pos h]
    have := Int.emod_add_ediv_mul a b; have := Int.emod_nonneg a (b := b) (by omega); have := Int.emod_lt_of_pos a hb
    constructor <;> nlinarith
  · intro h; rw [if_neg (by omega)]
    have := Int.emod_add_ediv_mul (-a) b; have := Int.emod_nonneg (-a) (b := b) (by omega)
    have := Int.emod_lt_of_pos (-a) hb
    constructor <;> nlinarith

@[scalar_tac a.tdiv 400] theorem tdiv400_bounds (a : Int) :
    (0 ≤ a → a.tdiv 400 * 400 ≤ a ∧ a < a.tdiv 400 * 400 + 400) ∧
      (a < 0 → a ≤ a.tdiv 400 * 400 ∧ a.tdiv 400 * 400 < a + 400) := tdiv_bounds_gen a 400 (by omega)
@[scalar_tac a.tdiv 5] theorem tdiv5_bounds (a : Int) :
    (0 ≤ a → a.tdiv 5 * 5 ≤ a ∧ a < a.tdiv 5 * 5 + 5) ∧
      (a < 0 → a ≤ a.tdiv 5 * 5 ∧ a.tdiv 5 * 5 < a + 5) := tdiv_bounds_gen a 5 (by omega)
@[scalar_tac a.tdiv 4] theorem tdiv4_bounds (a : Int) :
    (0 ≤ a → a.tdiv 4 * 4 ≤ a ∧ a < a.tdiv 4 * 4 + 4) ∧
      (a < 0 → a ≤ a.tdiv 4 * 4 ∧ a.tdiv 4 * 4 < a + 4) := tdiv_bounds_gen a 4 (by omega)
@[scalar_tac a.tdiv 100] theorem tdiv100_bounds (a : Int) :
    (0 ≤ a → a.tdiv 100 * 100 ≤ a ∧ a < a.tdiv 100 * 100 + 100) ∧
      (a < 0 → a ≤ a.tdiv 100 * 100 ∧ a.tdiv 100 * 100 < a + 100) := tdiv_bounds_gen a 100 (by omega)

theorem tdiv_eq' (a : Int) : a.tdiv 400 = if 0 ≤ a then a / 400 else -((-a) / 400) := tdiv_eq_gen _ _
theorem tdiv_eq5 (a : Int) : a.tdiv 5 = if 0 ≤ a then a / 5 else -((-a) / 5) := tdiv_eq_gen _ _
theorem tdiv_eq4 (a : Int) : a.tdiv 4 = if 0 ≤ a then a / 4 else -((-a) / 4) := tdiv_eq_gen _ _
theorem tdiv_eq100 (a : Int) : a.tdiv 100 = if 0 ≤ a then a / 100 else -((-a) / 100) := tdiv_eq_gen _ _

set_option maxHeartbeats 4000000 in
@[step] theorem days_from_civil_spec (y m d : I64) (hy : 0 ≤ y.val ∧ y.val ≤ 9999)
    (hm : 1 ≤ m.val ∧ m.val ≤ 12) (hd : 1 ≤ d.val ∧ d.val ≤ 31) :
    ext.days_from_civil y m d ⦃ r => r.val = XL.daysFromCivil y.val m.val d.val ∧
      -900000 ≤ r.val ∧ r.val ≤ 3000000 ⦄ := by
  unfold ext.days_from_civil
  by_cases hm2 : m > 2#i64
  · have hy0 : y ≥ 0#i64 := by scalar_tac
    simp only [hm2, hy0, ite_true, bind_ok]
    step*
    all_goals (try have := (tdiv400_bounds (↑y : Int)).1 (by scalar_tac))
    all_goals (try have := (tdiv400_bounds (↑y : Int)).2 (by scalar_tac))
    all_goals (try have := (tdiv5_bounds (↑i2 : Int)).1 (by scalar_tac))
    all_goals (try have := (tdiv4_bounds (↑yoe : Int)).1 (by scalar_tac))
    all_goals (try have := (tdiv100_bounds (↑yoe : Int)).1 (by scalar_tac))
    all_goals (try simp only [XL.daysFromCivil, show (↑m : Int) > 2 by scalar_tac, ite_true, ite_false])
    all_goals scalar_tac
  · simp only [hm2, ite_false]
    step
    by_cases hy1 : y1 ≥ 0#i64
    · simp only [hy1, ite_true, bind_ok]
      step*
      all_goals (try have := (tdiv400_bounds (↑y1 : Int)).1 (by scalar_tac))
      all_goals (try have := (tdiv400_bounds (↑y1 : Int)).2 (by scalar_tac))
      all_goals (try have := (tdiv5_bounds (↑i2 : Int)).1 (by scalar_tac))
      all_goals (try have := (tdiv4_bounds (↑yoe : Int)).1 (by scalar_tac))
      all_goals (try have := (tdiv100_bounds (↑yoe : Int)).1 (by scalar_tac))
      all_goals (try simp only [XL.daysFromCivil, show ¬ (↑m : Int) > 2 by scalar_tac, ite_true, ite_false])
      all_goals scalar_tac
    · simp only [hy1, ite_false]
      step*
      all_goals (try have := (tdiv400_bounds (↑y11 : Int)).1 (by scalar_tac))
      all_goals (try have := (tdiv400_bounds (↑y11 : Int)).2 (by scalar_tac))
      all_goals (try have := (tdiv5_bounds (↑i2 : Int)).1 (by scalar_tac))
      all_goals (try have := (tdiv4_bounds (↑yoe : Int)).1 (by scalar_tac))
      all_goals (try have := (tdiv100_bounds (↑yoe : Int)).1 (by scalar_tac))
      all_goals (try simp only [XL.daysFromCivil, show ¬ (↑m : Int) > 2 by scalar_tac, ite_true, ite_false])
      all_goals scalar_tac

@[simp] theorem ms_per_day_val : ext.MS_PER_DAY.val = 86400000 := by
  simp [ext.MS_PER_DAY]

theorem XL.daysInMonth_le (y m : Int) : XL.daysInMonth y m ≤ 31 := by
  unfold XL.daysInMonth; split_ifs <;> omega

theorem XL.validDate_bounds {y m d : Int} (h : XL.validDate y m d = true) :
    1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ 31 := by
  simp only [XL.validDate, decide_eq_true_eq] at h
  have := XL.daysInMonth_le y m
  omega

@[step] theorem offset_delta_spec (off : Option (Bool × value.List Char × value.List Char)) :
    ext.offset_delta off ⦃ r => XL.offsetDelta (offToSpec off) = r.map (·.val) ∧
      (∀ x, r = some x → -86340 ≤ x.val ∧ x.val ≤ 86340) ⦄ := by
  unfold ext.offset_delta
  rcases off with _ | ⟨pos, hh, mm⟩
  · simp [XL.offsetDelta, offToSpec, WP.spec_ok]
  · step*
    all_goals (subst_vars; simp_all [XL.offsetDelta, offToSpec])
    all_goals scalar_tac

@[step] theorem opt_small_nat_spec (m : Option (value.List Char)) :
    ext.opt_small_nat m ⦃ r => r.val = XL.optSmallNat (m.map List.toList) ∧ 0 ≤ r.val ∧ r.val ≤ 9999 ⦄ := by
  unfold ext.opt_small_nat
  cases m with
  | none => simp [XL.optSmallNat, WP.spec_ok]
  | some m => simpa [XL.optSmallNat] using small_nat_spec m

@[step] theorem parse_time_spec (s : value.List Char) :
    ext.parse_time s ⦃ r => XL.parseTime (List.toList s) = r.map (·.val) ∧
      (∀ x, r = some x → -86400000 < x.val ∧ x.val < 2 * 86400000) ⦄ := by
  unfold ext.parse_time
  xstep
  all_goals (subst_vars; simp_all [XL.parseTime, quad, offToSpec])
  all_goals (try omega)

@[step] theorem parse_datetime_spec (s : value.List Char) :
    ext.parse_datetime s ⦃ r => XL.parseDatetime (List.toList s) = r.map (·.val) ⦄ := by
  unfold ext.parse_datetime
  xstep
  all_goals (subst_vars; simp_all [XL.parseDatetime, quad])
  all_goals (try have := XL.validDate_bounds ‹_›)
  all_goals scalar_tac

end

end CedarRustModel
