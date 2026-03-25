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

public import Cedar.Spec.Ext.Datetime
import all Cedar.Spec.Ext.Datetime

/-!
# Extension function rewriting lemmas

This file contains lemmas that rewrite Cedar extension function definitions
into equivalent forms that are easier to reason about in SymCC proofs.
-/

namespace Cedar.Thm

open Cedar.Spec.Ext.Datetime

/-- The `Int64` encoding of `MILLISECONDS_PER_DAY`. -/
private abbrev msPerDay : Int64 := Int64.ofIntChecked MILLISECONDS_PER_DAY (by decide)

private theorem msPerDay_eq : msPerDay = (86400000 : Int64) := by native_decide
private theorem msPerDay_toInt : msPerDay.toInt = 86400000 := by native_decide
private theorem msPerDay_gt_one : msPerDay.toInt > 1 := by native_decide

private theorem toInt_div_msPerDay (v : Int64) :
  (v / msPerDay).toInt = v.toInt.tdiv msPerDay.toInt := by
  rw [msPerDay_toInt, msPerDay_eq, Int64.toInt_div,
    show (86400000 : Int64).toInt = (86400000 : Int) from by native_decide]
  -- The result of tdiv is in Int64 range because |v / 86400000| ≤ ⌊(2^63-1)/86400000⌋ = 106751991167
  apply Int.bmod_eq_of_le
  · have := Int.tdiv_le_tdiv (by omega : (0 : Int) < 86400000)
      (show -(2 ^ (64 - 1) : Int) ≤ v.toInt from by
        rw [← Int64.toInt_toBitVec]; exact @BitVec.le_toInt 64 v.toBitVec)
    have : (-(2 : Int) ^ (64 - 1)).tdiv 86400000 = -106751991167 := by native_decide
    omega
  · have := Int.tdiv_le_tdiv (by omega : (0 : Int) < 86400000)
      (show v.toInt ≤ 2 ^ (64 - 1) - 1 from by
        rw [← Int64.toInt_toBitVec]; have := @BitVec.toInt_lt 64 v.toBitVec; omega)
    have : ((2 : Int) ^ (64 - 1) - 1).tdiv 86400000 = 106751991167 := by native_decide
    omega

private theorem toInt_mod_msPerDay (v : Int64) :
  (v % msPerDay).toInt = v.toInt.tmod msPerDay.toInt := by
  rw [Int64.toInt_mod, msPerDay_toInt]

private theorem toInt_smod_msPerDay (v : Int64) :
  (v.smod msPerDay).toInt = v.toInt.fmod msPerDay.toInt := by
  rw [Int64.toInt_smod, msPerDay_toInt]

/-- Equivalent formulation of `toDate` using `Int64.smod`, useful for symbolic compilation. -/
public theorem toDate_eq_smod (datetime : Spec.Ext.Datetime) :
  toDate datetime =
  let millisPerDayI64 := Int64.ofIntChecked MILLISECONDS_PER_DAY (by decide)
  datetime? (datetime.val - Int64.smod datetime.val millisPerDayI64)
:= by
  simp only [toDate, MILLISECONDS_PER_DAY]
  obtain ⟨v⟩ := datetime
  show (if v ≥ 0 then datetime? (msPerDay.toInt * (v / msPerDay).toInt)
    else if (v % msPerDay == 0) = true then some ⟨v⟩
    else datetime? (((v / msPerDay).toInt - 1) * msPerDay.toInt)) =
    datetime? (v.toInt - (v.smod msPerDay).toInt)
  rw [msPerDay_toInt, toInt_div_msPerDay, toInt_smod_msPerDay, msPerDay_toInt]
  -- After rewriting, all three branches are pure Int arithmetic over v.toInt
  split
  case isTrue h_ge =>
    -- v ≥ 0: d * v.toInt.tdiv d = v.toInt - v.toInt.fmod d
    congr 1
    have hfmod := Int.fmod_def v.toInt 86400000
    have hfdiv : v.toInt.fdiv 86400000 = v.toInt.tdiv 86400000 := by
      have := Int64.toInt_nonneg_of_ge_zero h_ge
      simp only [Int.fdiv_eq_tdiv]; split <;> omega
    omega
  case isFalse h_neg =>
    have h_neg_int := Int64.toInt_neg_of_not_ge_zero h_neg
    have hmod := toInt_mod_msPerDay v
    rw [msPerDay_toInt] at hmod
    split
    case isTrue h_mod_zero =>
      -- v < 0, v % d = 0: fmod = 0, so datetime?(v.toInt - 0) = some ⟨v⟩
      simp only [BEq.beq, decide_eq_true_eq] at h_mod_zero
      have h_tmod_zero : v.toInt.tmod 86400000 = 0 := by
        rw [← hmod, h_mod_zero]
        exact show (0 : Int64).toInt = 0 from by native_decide
      have h_fmod_zero : v.toInt.fmod 86400000 = 0 := by
        have : (86400000 : Int) ∣ v.toInt := (Int.dvd_iff_tmod_eq_zero).mpr h_tmod_zero
        simp only [Int.fmod_eq_tmod, this, ↓reduceIte]; omega
      rw [h_fmod_zero, Int.sub_zero]; symm
      unfold datetime?
      simp only [Int64.ofInt?_toInt, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
    case isFalse h_mod_nonzero =>
      -- v < 0, v % d ≠ 0: (v.tdiv d - 1) * d = v - v.fmod d
      simp only [BEq.beq, decide_eq_true_eq] at h_mod_nonzero
      have h_tmod_nonzero : v.toInt.tmod 86400000 ≠ 0 := by
        intro h; exact h_mod_nonzero (Int64.toInt_inj.mp (by
          rw [hmod, h]; exact (show (0 : Int64).toInt = 0 from by native_decide).symm))
      congr 1
      have hndvd : ¬((86400000 : Int) ∣ v.toInt) := by
        rw [Int.dvd_iff_tmod_eq_zero]; exact h_tmod_nonzero
      have hfmod := Int.fmod_def v.toInt 86400000
      have hfdiv : v.toInt.fdiv 86400000 = v.toInt.tdiv 86400000 - 1 := by
        simp only [Int.fdiv_eq_tdiv, hndvd, ↓reduceIte, show ¬(0 ≤ v.toInt) from by omega,
          show (0 ≤ (86400000 : Int)) from by omega]
        have : (86400000 : Int).sign = 1 := Int.sign_eq_one_of_pos (by omega)
        omega
      rw [hfdiv] at hfmod
      omega

end Cedar.Thm
