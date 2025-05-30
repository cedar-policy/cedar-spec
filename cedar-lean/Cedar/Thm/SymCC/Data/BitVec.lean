import Cedar.Data
import Cedar.SymCC.Data
import Init.Data.BitVec.Basic
import Init.Data.Int.DivMod

/-!
# Bitvector utilities

This file contains definitions and lemmas for working with bitvectors. These
lemmas are true in general, but the general proofs are much harder. So, we prove
them only for the specific bitwidths we need.
-/


namespace BitVec

open Cedar.Data

theorem toInt_ofInt64_toBitVec {bv : BitVec 64} :
  (Int64.ofInt bv.toInt).toBitVec = bv
:= by
  simp only [Int64.toBitVec, Int64.ofInt, ofInt_toInt]

theorem Int64_toBitVec_toInt_eq_toInt (x : Int64) : x.toBitVec.toInt = x.toInt := by rfl

theorem eq_iff_UInt64_toInt64_eq_64 {bv₁ bv₂ : BitVec 64} :
  bv₁ = bv₂ ↔ (UInt64.toInt64 {toBitVec := bv₁}) = (UInt64.toInt64 {toBitVec := bv₂})
:= by
  constructor <;> intro h₁
  · simp only [h₁]
  · simp [UInt64.toInt64] at h₁
    exact h₁

theorem toInt_min_64 {bv : BitVec 64} :
  BitVec.signedMin 64 ≤ bv.toInt
:= by
  simp only [signedMin, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, Int.reducePow, Int.reduceNeg,
    BitVec.toInt, Nat.reducePow]
  omega

theorem toInt_max_64 {bv : BitVec 64} :
  bv.toInt ≤ BitVec.signedMax 64
:= by
  simp only [BitVec.toInt, Nat.reducePow, signedMax, Nat.succ_sub_succ_eq_sub,
    Nat.sub_zero, Int.reducePow, Int.reduceSub]
  omega

theorem toInt_ge_INT64_MIN (bv : BitVec 64) :
  Int64.MIN ≤ bv.toInt
:= by exact toInt_min_64

theorem toInt_le_INT64_MAX (bv : BitVec 64) :
  bv.toInt ≤ Int64.MAX
:= by exact toInt_max_64

theorem signedMin_eq_INT64_MIN :
  BitVec.signedMin 64 = Int64.MIN
:= by
  simp only [signedMin, Int64.MIN]
  decide

theorem signedMax_eq_INT64_MAX :
  BitVec.signedMax 64 = Int64.MAX
:= by
  simp only [signedMax, Int64.MAX]
  decide

theorem toInt_ofInt_64 {bv : BitVec 64} :
  BitVec.ofInt 64 (BitVec.toInt bv) = bv
:= by
  simp only [BitVec.ofInt, BitVec.toInt, Nat.reducePow, Int.ofNat_eq_coe, toNat_eq, toNat_ofNatLT]
  generalize hn : BitVec.toNat bv = n
  have heq : (n : Int) % 18446744073709551616 = n := by omega
  split
  · simp only [Int.cast_ofNat_Int, heq, Int.toNat_ofNat]
  · simp only [Int.toNat, Int.cast_ofNat_Int, Int.emod_sub_cancel, heq]

theorem overflows_false_64 {i : Int}
  (h : Int64.MIN ≤ i ∧ i ≤ Int64.MAX) :
  BitVec.overflows 64 i = false
:= by
  simp only [BitVec.overflows]
  by_contra hc
  simp only [signedMin_eq_INT64_MIN, signedMax_eq_INT64_MAX, gt_iff_lt, Bool.not_eq_false,
    Bool.or_eq_true, decide_eq_true_eq] at hc
  omega

theorem overflows_true_64 {i : Int}
  (h : ¬ (Int64.MIN ≤ i ∧ i ≤ Int64.MAX)) :
  BitVec.overflows 64 i = true
:= by
  simp only [BitVec.overflows]
  by_contra hc
  simp only [signedMin_eq_INT64_MIN, signedMax_eq_INT64_MAX, gt_iff_lt, Bool.or_eq_true,
    decide_eq_true_eq] at hc
  omega

theorem Int64_ofInt?_eq_none_iff_overflows {i : Int} :
  Int64.ofInt? i = none ↔ BitVec.overflows 64 i
:= by
  simp only [Int64.ofInt?]
  split <;> rename_i h
  case isTrue => simp only [reduceCtorEq, overflows_false_64 h, Bool.false_eq_true]
  case isFalse => simp only [overflows_true_64 h]

theorem neg_toInt_eq_neg_64 {bv : BitVec 64} {i : Int64}
  (h₁ : Int64.MIN ≤ -i.toInt ∧ -i.toInt ≤ Int64.MAX)
  (h₂ : BitVec.toInt bv = i.toInt) :
  BitVec.toInt (-bv) = -i.toInt
:= by
  generalize hv : i.toInt = j
  simp only [hv, Int64.MIN, Int64.MAX] at h₁
  simp only [Int.reduceNeg, toInt_eq_toNat_cond, Nat.reducePow, toNat_neg, Int.ofNat_emod] at *
  split <;> omega

theorem add_toInt_eq_add_64 {bv₁ bv₂ : BitVec 64} {i₁ i₂ : Int64}
  (h₀ : Int64.MIN ≤ i₁.toInt + i₂.toInt ∧ i₁.toInt + i₂.toInt ≤ Int64.MAX)
  (h₁ : BitVec.toInt bv₁ = i₁.toInt)
  (h₂ : BitVec.toInt bv₂ = i₂.toInt) :
  BitVec.toInt (bv₁ + bv₂) = i₁.toInt + i₂.toInt
:= by
  generalize hv₁ : i₁.toInt = j₁
  generalize hv₂ : i₂.toInt = j₂
  simp only [hv₁, hv₂, Int64.MIN, Int64.MAX] at h₀
  simp only [toInt_eq_toNat_cond, Nat.reducePow, Int.reduceNeg, toNat_add, Int.ofNat_emod, Int.natCast_add] at *
  split <;> omega

theorem sub_toInt_eq_sub_64 {bv₁ bv₂ : BitVec 64} {i₁ i₂ : Int64}
  (h₀ : Int64.MIN ≤ i₁.toInt - i₂.toInt ∧ i₁.toInt - i₂.toInt ≤ Int64.MAX)
  (h₁ : BitVec.toInt bv₁ = i₁.toInt)
  (h₂ : BitVec.toInt bv₂ = i₂.toInt) :
  BitVec.toInt (bv₁ - bv₂) = i₁.toInt - i₂.toInt
:= by
  generalize hv₁ : i₁.toInt = j₁
  generalize hv₂ : i₂.toInt = j₂
  simp only [hv₁, hv₂, Int64.MIN, Int64.MAX] at h₀
  simp only [Int.reduceNeg, toInt_eq_toNat_cond, Nat.reducePow, toNat_sub, Int.ofNat_emod, Int.natCast_add] at *
  split <;> omega

theorem mul_eq_toInt_mul_ofInt_64 {bv₁ bv₂ : BitVec 64} :
  bv₁ * bv₂ = BitVec.ofInt 64 (BitVec.toInt bv₁ * BitVec.toInt bv₂)
:= by
  simp only [mul_def, Fin.mul_def, val_toFin, Nat.reducePow, BitVec.ofInt, BitVec.ofNatLT,
    BitVec.toInt, Int.ofNat_eq_coe, ofFin.injEq, Fin.mk.injEq]
  generalize h₁ : BitVec.toNat bv₁ = n₁
  generalize h₂ : BitVec.toNat bv₂ = n₂
  have h₄ : (n₁ : Int) % 18446744073709551616 = (n₁ : Int) := by omega
  have h₅ : (n₂ : Int) % 18446744073709551616 = n₂ := by omega
  split <;> split
  case isTrue.isTrue =>
    norm_cast
  case isTrue.isFalse | isFalse.isTrue | isFalse.isFalse =>
    rw [Int.mul_emod]
    simp only [Int.emod_sub_cancel, h₄, h₅]
    norm_cast
    simp only [Int.toNat_ofNat, Nat.mul_mod_mod, Nat.mod_mul_mod]

theorem mul_toInt_eq_mul_64 {bv₁ bv₂ : BitVec 64} {i₁ i₂ : Int64}
  (h₀ : Int64.MIN ≤ i₁.toInt * i₂.toInt ∧ i₁.toInt * i₂.toInt ≤ Int64.MAX)
  (h₁ : BitVec.toInt bv₁ = i₁.toInt)
  (h₂ : BitVec.toInt bv₂ = i₂.toInt) :
  BitVec.toInt (bv₁ * bv₂) = i₁.toInt * i₂.toInt
:= by
  generalize hj₁ : i₁.toInt = j₁
  generalize hj₂ : i₂.toInt = j₂
  simp only [Int64.MIN, Int.reduceNeg, hj₁, hj₂, Int64.MAX] at h₀ h₁ h₂
  simp only [mul_eq_toInt_mul_ofInt_64, h₁, h₂, toInt_ofInt, Nat.reducePow]
  generalize hj₃ : j₁ * j₂ = j₃
  simp only [Int.reduceNeg, hj₃] at h₀
  simp only [Int.bmod_def, Int.reduceAdd, Int.reduceDiv]
  split <;> omega

theorem mul_toInt_eq_toInt_mul {bv₁ bv₂ : BitVec 64}
  (h : Int64.MIN ≤ bv₁.toInt * bv₂.toInt ∧ bv₁.toInt * bv₂.toInt ≤ Int64.MAX) :
  BitVec.toInt (bv₁ * bv₂) = bv₁.toInt * bv₂.toInt
:= by
  generalize hi₁ : UInt64.toInt64 (UInt64.ofBitVec bv₁) = i₁
  generalize hi₂ : UInt64.toInt64 (UInt64.ofBitVec bv₂) = i₂
  have heq₁ : bv₁.toInt = i₁.toInt := by simp only [← hi₁]; rfl
  have heq₂ : bv₂.toInt = i₂.toInt := by simp only [← hi₂]; rfl
  rw [heq₁, heq₂] at h ⊢
  exact mul_toInt_eq_mul_64 h heq₁ heq₂

private theorem mul_left_tdiv_right_pos_le {i₁ i₂ : Int}
  (h₁ : 0 ≤ i₁)
  (h₂ : 0 ≤ i₂) :
  i₂ * (i₁.tdiv i₂) ≤ i₁
:= by
  replace h₁ := Int.eq_ofNat_of_zero_le h₁
  replace h₂ := Int.eq_ofNat_of_zero_le h₂
  cases h₁ ; cases h₂ ; rename_i n₁ h₁ n₂ h₂; subst h₁ h₂
  simp only [Int.tdiv, Int.ofNat_eq_coe, Int.ofNat_mul_ofNat,
    Int.ofNat_le, Nat.mul_comm, Nat.mul_div_le]

private theorem le_mul_left_tdiv_right_neg {i₁ i₂ : Int}
  (h₁ : i₁ ≤ 0)
  (h₂ : 0 ≤ i₂) :
  i₁ ≤ i₂ * (i₁.tdiv i₂)
:= by
  apply Int.le_of_neg_le_neg
  simp only [← Int.mul_neg, ← Int.neg_tdiv]
  replace h₁ := Int.neg_le_neg h₁
  simp only [Int.neg_zero] at h₁
  exact mul_left_tdiv_right_pos_le h₁ h₂

private theorem msb_true_implies_neg_msb_eq {n : Nat} {bv : BitVec n}
  (h : bv.msb = true) :
  bv.neg.msb = false ∨ bv.neg = intMin n
:= by
  simp only [BitVec.neg_eq, BitVec.msb_neg]
  cases h₁: bv == 0#n
  case true =>
    simp only [beq_iff_eq] at h₁; subst h₁
    simp only [BitVec.msb, getMsbD_zero, Bool.false_eq_true] at h
  case false =>
    simp only [beq_eq_false_iff_ne, ← bne_iff_ne] at h₁
    simp only [h₁, Bool.true_and]; clear h₁
    cases h₁: bv == intMin n
    case true =>
      simp only [beq_iff_eq] at h₁; subst h₁; right
      exact BitVec.neg_intMin
    case false =>
      simp only [beq_eq_false_iff_ne, ← bne_iff_ne] at h₁
      simp only [h, h₁, bne_self_eq_false, true_or]

private theorem msb_false_implies_neg_msb_eq {n : Nat} {bv : BitVec n}
  (h : bv.msb = false) :
  bv.neg = 0#n ∨ (bv.neg.msb = true ∧ (intMin n).toInt < bv.neg.toInt)
:= by
  simp only [BitVec.neg_eq, BitVec.msb_neg, h, Bool.xor_false]
  cases h₁ : bv == 0#n
  case true =>
    simp only [beq_iff_eq] at h₁; subst h₁; left
    simp only [neg_zero, ofNat_eq_ofNat]
  case false =>
    simp only [beq_eq_false_iff_ne, ← bne_iff_ne] at h₁; right
    simp only [h₁, Bool.true_and]
    cases h₂ : bv == intMin n
    case true =>
      simp only [beq_iff_eq] at h₂; subst h₂
      simp only [BitVec.msb_eq_false_iff_two_mul_lt] at h
      simp only [toNat_intMin] at h
      cases n
      case zero =>
        simp only [bne_iff_ne, ne_eq] at h₁
        exfalso; apply h₁; clear h h₁
        bv_omega
      case succ n =>
        simp only [Nat.add_one_sub_one] at h
        simp only [@Nat.mod_eq_of_lt (2^n) (2^(n+1)) (by omega)] at h
        omega
    case false =>
      simp only [beq_eq_false_iff_ne, ← bne_iff_ne] at h₂
      simp only [h₂, true_and]
      simp only [bne_iff_ne, ne_eq] at h₂
      simp only [Int.lt_iff_le_and_ne, BitVec.toInt_intMin_le, true_and, ne_eq, BitVec.toInt_inj]
      intro h₃; apply h₂; symm
      rw [← BitVec.neg_inj, BitVec.neg_intMin]
      exact h₃

theorem sdiv_pos_lt_INT64_MAX {bv₁ bv₂ : BitVec 64}
  (h : 1 < bv₂.toInt) :
  (bv₁.sdiv bv₂).toInt < Int64.MAX
:= by
  have h₀ : bv₂.msb = false := by
    simp only [msb_eq_toInt, decide_eq_false_iff_not, Int.not_lt]
    exact Int.le_trans (by simp only [Int.reduceLE]) (Int.le_of_lt h)
  cases h₁ : bv₁.msb <;> simp only [BitVec.sdiv, h₀, h₁]
  case false =>
    simp only [BitVec.udiv_eq , BitVec.toInt_udiv_of_msb h₁]
    simp only [← Int.ofNat_ediv]
    replace h : 1 < bv₂.toNat := by
      simp only [BitVec.msb_eq_false_iff_two_mul_lt] at h₀
      simp only [BitVec.toInt, h₀, ↓reduceIte] at h
      simp only [← Int.ofNat_lt, Int.cast_ofNat_Int, h]
    simp only [Int64.MAX, Int.ofNat_lt]
    have h₃ : bv₁.toNat ≤ 9223372036854775807 := by
      simp only [msb_eq_false_iff_two_mul_lt] at h₁; omega
    generalize bv₁.toNat = n₁ at *
    generalize bv₂.toNat = n₂ at *
    clear h₀ h₁ bv₁ bv₂
    cases n₁
    case zero => simp only [Nat.zero_div, Int.cast_ofNat_Int, Int.reduceLT]
    case succ n₁ =>
      have h₄ : 9223372036854775807 = Int.ofNat 9223372036854775807 := by rfl
      simp only [h₄, Int.ofNat_eq_coe, Int.ofNat_lt]
      exact Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.zero_lt_succ n₁) h) h₃
  case true =>
    replace h₁ := msb_true_implies_neg_msb_eq h₁
    generalize bv₁.neg = bv₁ at *
    cases h₁
    case inl h₁ =>
      replace h₁ := msb_false_implies_neg_msb_eq (@BitVec.msb_udiv_eq_false_of _ _ bv₂ h₁)
      cases h₁
      case inl h₁ =>
        simp only [BitVec.udiv_eq, h₁, Int64.MAX]
        simp only [ofNat_eq_ofNat, toInt_zero, Int.reduceLT]
      case inr h₁ =>
        generalize (bv₁.udiv bv₂).neg = bv₁ at *
        apply @Int.lt_trans _ 0
        simp only [BitVec.msb_eq_toInt, decide_eq_true_eq] at h₁; exact h₁.left
        simp only [Int64.MAX, Int.reduceLT]
    case inr h₁ =>
      subst h₁
      simp only [BitVec.neg, Int64.MAX, BitVec.udiv_eq, BitVec.udiv_def]
      simp only [Nat.reducePow, toNat_intMin, Nat.add_one_sub_one, Nat.reduceMod, toNat_ofNat,
        gt_iff_lt]
      simp only [BitVec.toInt_ofNat]
      simp only [BitVec.msb_eq_false_iff_two_mul_lt] at h₀
      replace h : 1 < bv₂.toNat := by
        simp only [BitVec.toInt, h₀, ↓reduceIte] at h
        simp only [← Int.ofNat_lt, Int.cast_ofNat_Int, h]
      generalize bv₂.toNat = n₂ at *
      simp only [Int.bmod_def]
      cases h₁ : decide ((Int.ofNat (18446744073709551616 - 9223372036854775808 / n₂ % 18446744073709551616)) % Int.ofNat (2 ^ 64) < (Int.ofNat (2 ^ 64) + 1) / 2) == true
      case false =>
        simp only [beq_eq_false_iff_ne, ne_eq, eq_false_of_ne_true] at h₁
        simp only [decide_eq_true_eq, Int.ofNat_eq_coe] at h₁
        simp only [h₁, ↓reduceIte]
        omega
      case true =>
        replace h₀ : n₂ < 2^63 := by omega
        simp only [beq_true, decide_eq_true_eq, Int.ofNat_eq_coe] at h₁
        simp only [h₁, ↓reduceIte, ← Int.not_le]
        intro h₂
        simp only [← Int.not_le] at h₁
        apply h₁; clear h₁ h₂ bv₁ bv₂
        have h₁ : 0 < 2^63/ n₂ := by
          apply Nat.zero_lt_of_ne_zero
          intros h₁
          replace h₁ := Nat.lt_of_div_eq_zero (Nat.zero_lt_of_lt h) h₁
          omega
        have h₂ : 2^63 / n₂ < 2^64 := by
          apply Nat.div_lt_of_lt_mul
          rw [← Nat.one_mul (2^63)]
          apply Nat.mul_lt_mul_of_lt_of_lt h
          simp only [Nat.reducePow, Nat.reduceLT]
        have h₃ : 2^64  - (2^63 / n₂) < 2^64 := by omega
        have h₄ : ((Int.ofNat (2^64)) + 1) / 2 = Int.ofNat ((2^64 + 1) / 2) := by
          simp only [Int.ofNat_eq_coe, Int.ofNat_ediv, Int.ofNat_add]; rfl
        simp only [Int.ofNat_eq_coe] at h₄
        simp only [Int.ofNat_mod_ofNat]
        simp only [Nat.mod_eq_of_lt h₂, Nat.mod_eq_of_lt h₃]
        simp only [h₄, Int.ofNat_le]
        replace h₄ : 2^63 / n₂ < 2^63 := by
          apply Nat.div_lt_of_lt_mul
          rw [← Nat.one_mul (2^63)]
          apply Nat.mul_lt_mul_of_lt_of_le h
          simp only [Nat.reducePow, Nat.reduceLT, Nat.one_mul, Nat.le_refl]
          simp only [Nat.reducePow, Nat.one_mul, Nat.zero_lt_succ]
        omega

theorem sdiv_pos_gt_INT64_MIN {bv₁ bv₂ : BitVec 64}
  (h : 1 < bv₂.toInt) :
  Int64.MIN < (bv₁.sdiv bv₂).toInt
:= by
  have h₀ : bv₂.msb = false := by
    simp only [msb_eq_toInt, decide_eq_false_iff_not, Int.not_lt]
    exact Int.le_trans (by simp only [Int.reduceLE]) (Int.le_of_lt h)
  cases h₁ : bv₁.msb <;> simp only [BitVec.sdiv, h₀, h₁]
  case false =>
    simp only [BitVec.udiv_eq , BitVec.toInt_udiv_of_msb h₁]
    simp only [← Int.ofNat_ediv]
    exact Int.lt_of_lt_of_le (Int.sign_eq_neg_one_iff_neg.mp rfl) (Int.ofNat_zero_le (bv₁.toNat / bv₂.toNat))
  case true =>
    cases msb_true_implies_neg_msb_eq h₁
    case inl h₂ =>
      replace h₃ := @BitVec.msb_udiv_eq_false_of _ _ bv₂ h₂
      cases msb_false_implies_neg_msb_eq h₃
      case inl h₃ =>
        simp only [BitVec.udiv_eq, h₃]
        simp only [Int64.MIN, Int.reduceNeg, toInt_zero, Int.reduceLT]
      case inr h₃ =>
        apply Int.lt_of_le_of_lt _ h₃.right
        simp only [Int64.MIN, Int.reduceNeg, toInt_intMin, Nat.add_one_sub_one, Nat.reducePow,
          Nat.reduceMod, Int.cast_ofNat_Int, Int.le_refl]
    case inr h₂ =>
      simp only [h₂]
      have h₃ := BitVec.msb_udiv (intMin 64) bv₂
      have h₄ : (bv₂ == 1#64) = false := by
        simp only [beq_eq_false_iff_ne]
        have h₅ := Int.ne_of_lt h
        intro h; apply h₅
        simp only [h, BitVec.reduceToInt]
      simp only [h₄, Bool.and_false] at h₃
      cases msb_false_implies_neg_msb_eq h₃
      case inl h₅ =>
        simp only [BitVec.udiv_eq, h₅, Int64.MIN, Int.reduceNeg, toInt_zero, Int.reduceLT]
      case inr h₅ =>
        exact h₅.right

private theorem BitVec.msb_true_toNat_eq_neg_toInt {bv : BitVec 64} {n : Nat}
  (hmsb : bv.msb = true) (h : bv.toInt = Int.negSucc n) :
  (-bv).toNat = n.succ
:= by
    have h₀ : (-bv).toNat = 2^64 - bv.toNat := by
      have h₀ := BitVec.toNat_neg bv
      have h₁ := BitVec.toNat_ge_of_msb_true hmsb; omega
    have h₁ := BitVec.toInt_eq_toNat_cond bv
    simp only [← BitVec.msb_eq_false_iff_two_mul_lt, hmsb, Bool.true_eq_false, ↓reduceIte] at h₁
    rw [h, ← Int.neg_inj, Int.neg_sub, Int.neg_negSucc] at h₁
    have h₂ : Int.ofNat (bv.toNat) ≤ Int.ofNat (2^64) := by
      apply Int.le_of_sub_nonneg
      apply Int.le_trans
      exact Int.ofNat_zero_le n.succ
      simp only [h₁, Int.ofNat_eq_coe, Int.le_refl]
    simp only [Int.ofNat_eq_coe, Int.ofNat_le] at h₂
    simp only [← Int.ofNat_sub h₂, Int.ofNat_inj] at h₁
    simp only [h₀, ← h₁, ← Int.ofNat_ediv]

theorem toInt_sdiv_eq_tdiv_toInt {bv₁ bv₂ : BitVec 64}
  (h₀ : 0 < bv₂.toInt) :
  BitVec.toInt (bv₁.sdiv bv₂) = bv₁.toInt.tdiv bv₂.toInt
:= by
  cases hmsb₁ : bv₁.msb
  case false =>
    have hi₁ : 0 ≤ bv₁.toInt := by
      simp only [BitVec.msb_eq_toInt, decide_eq_false_iff_not, Int.not_lt] at hmsb₁
      exact hmsb₁
    have ⟨n₁, hn₁⟩ := Int.eq_ofNat_of_zero_le hi₁
    cases hmsb₂ : bv₂.msb
    case false =>
      have hi₂ : 0 ≤ bv₂.toInt := by
        simp only [BitVec.msb_eq_toInt, decide_eq_false_iff_not, Int.not_lt] at hmsb₂
        exact hmsb₂
      simp only [BitVec.sdiv, hmsb₁, hmsb₂]
      have ⟨n₂, hn₂⟩ := Int.eq_ofNat_of_zero_le hi₂
      simp only [BitVec.udiv_eq, BitVec.toInt_udiv_of_msb hmsb₁, hn₁, hn₂]
      simp only [BitVec.toInt_eq_toNat_of_msb hmsb₁] at hn₁
      simp only [BitVec.toInt_eq_toNat_of_msb hmsb₂] at hn₂
      simp only [hn₁, hn₂, Int.tdiv, Int.ofNat_eq_coe, Int.ofNat_ediv]
    case true =>
      have hi₂ : bv₂.toInt < 0 := by
        simp only [BitVec.msb_eq_toInt, decide_eq_true_iff] at hmsb₂
        exact hmsb₂
      omega
  case true =>
    have hi₁ : bv₁.toInt < 0 := by
      simp only [BitVec.msb_eq_toInt, decide_eq_true_iff] at hmsb₁
      exact hmsb₁
    have ⟨n₁, hn₁⟩ := Int.eq_negSucc_of_lt_zero hi₁
    have h₁ := BitVec.msb_true_toNat_eq_neg_toInt hmsb₁ hn₁
    cases hmsb₂ : bv₂.msb
    case false =>
      have hi₂ : 0 ≤ bv₂.toInt := by
        simp only [BitVec.msb_eq_toInt, decide_eq_false_iff_not, Int.not_lt] at hmsb₂
        exact hmsb₂
      have ⟨n₂, hn₂⟩ := Int.eq_ofNat_of_zero_le hi₂
      simp only [BitVec.sdiv, hmsb₁, hmsb₂]
      simp only [Int.tdiv, hn₁, hn₂]
      simp only [BitVec.toInt_eq_toNat_of_msb hmsb₂, Int.ofNat_inj] at hn₂
      have h₅ : (-bv₁).toNat / bv₂.toNat < 2^64 := by
        have h₅ : n₁.succ < 2^64 := by
          have h₅ := BitVec.toInt_intMin_le bv₁
          simp only [toInt_intMin, Nat.add_one_sub_one, Nat.reducePow, Nat.reduceMod, hn₁, Int.negSucc_eq] at h₅
          replace h₅ := Int.neg_le_neg h₅
          simp only [Int.neg_neg] at h₅; omega
        simp only [h₁, hn₂]
        cases n₂
        case zero =>
          simp only [Nat.div_zero, Nat.reducePow, Nat.zero_lt_succ]
        case succ =>
          apply Nat.div_lt_of_lt_mul; omega
      cases h₂ : bv₂ == 1#64
      case false =>
        have h₃ := BitVec.msb_udiv bv₁.neg bv₂
        simp only [h₂, Bool.and_false] at h₃; clear h₂
        cases BitVec.msb_false_implies_neg_msb_eq h₃
        case inl h₄ =>
          simp only [BitVec.udiv_eq, h₄, BitVec.toInt_zero]
          symm; simp only [Int.neg_eq_zero]
          simp only [BitVec.neg_eq, BitVec.neg_eq_zero_iff] at h₄
          simp only [BitVec.toNat_eq, BitVec.udiv_def, BitVec.toNat_ofNat, Nat.zero_mod] at h₄
          simp only [Nat.mod_eq_of_lt h₅] at h₄
          simp only [← Int.ofNat_zero, ← h₄, Int.ofNat_eq_coe, Int.ofNat_inj, h₁, hn₂]
        case inr h₄ =>
          replace ⟨h₄, h₆⟩ := h₄
          replace h₆ := Int.ne_of_lt h₆
          simp only [ne_eq, BitVec.toInt_inj, BitVec.neg_eq] at h₆
          rw [← BitVec.neg_inj, BitVec.neg_neg, BitVec.neg_intMin, ← ne_eq] at h₆
          symm at h₆
          simp only [BitVec.udiv_eq, BitVec.neg_eq, BitVec.toInt_neg_of_ne_intMin h₆, Int.neg_inj]
          simp only [BitVec.neg_eq] at h₃
          simp only [BitVec.toInt_eq_toNat_of_msb h₃]
          simp only [Int.ofNat_eq_coe, Int.ofNat_inj, BitVec.udiv_def, BitVec.toNat_ofNat]
          simp only [Nat.mod_eq_of_lt h₅]
          simp only [h₁, hn₂]
      case true =>
        simp only [beq_iff_eq] at h₂; subst h₂
        simp only [BitVec.neg_eq, BitVec.udiv_eq, BitVec.udiv_one, BitVec.neg_neg, hn₁, ← hn₂]
        simp only [BitVec.toNat_ofNat, Nat.one_mod_two_pow (by exact Nat.zero_lt_succ 64)]
        simp only [Int.negSucc_eq, Nat.succ_eq_add_one, Nat.div_one, Int.ofNat_eq_coe,
          Int.natCast_add, Int.cast_ofNat_Int]
    case true =>
      have hi₂ : bv₂.toInt < 0 := by
        simp only [BitVec.msb_eq_toInt, decide_eq_true_iff] at hmsb₂
        exact hmsb₂
      omega

theorem sdiv_pos_bounded {bv₁ bv₂ : BitVec 64}
  (h₀ : 0 < bv₂.toInt) :
  Int64.MIN.tdiv bv₂.toInt ≤ (bv₁.sdiv bv₂).toInt ∧ (bv₁.sdiv bv₂).toInt ≤ Int64.MAX.tdiv bv₂.toInt
:= by
  have h₁ := @toInt_sdiv_eq_tdiv_toInt bv₁ bv₂ h₀
  simp only [h₁]; clear h₁
  have h₁ := BitVec.toInt_ge_INT64_MIN bv₁
  have h₂ := BitVec.toInt_le_INT64_MAX bv₁
  generalize bv₁.toInt = i₁ at h₁ h₂
  generalize bv₂.toInt = i₂ at h₀
  clear bv₁ bv₂
  have ⟨n₂, hn₂⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt h₀)
  have ⟨nlow, hnlow⟩ := @Int.eq_negSucc_of_lt_zero Int64.MIN (by simp only [Int64.MIN, Int.reduceLT])
  have ⟨nhigh, hnhigh⟩ := @Int.eq_ofNat_of_zero_le Int64.MAX (by simp only [Int64.MAX, Int.reduceLE])
  simp only [hn₂, hnlow, hnhigh] at *; clear hn₂ hnlow hnhigh i₂
  cases h₃ : decide (0 ≤ i₁)
  case' false =>
    simp only [decide_eq_false_iff_not, Int.not_le] at h₃
    have ⟨n₁, hn₁⟩ := Int.eq_negSucc_of_lt_zero h₃; subst hn₁
    simp only [Int.tdiv, Nat.succ_eq_add_one, Int.ofNat_eq_coe, Int.ofNat_ediv]
    simp only [Int.negSucc_eq] at h₁ h₂ h₃
    apply And.intro
    case left =>
      apply Int.neg_le_neg
      apply Int.ediv_le_ediv h₀
      exact Int.neg_le_neg h₁
    case' right =>
      simp only [← Int.ofNat_ediv]
      apply @Int.le_trans _ 0
      apply Int.neg_le_of_neg_le
      simp only [Int.neg_zero]
      apply Int.ofNat_zero_le
      apply Int.ofNat_zero_le
  case true =>
    simp only [decide_eq_true_eq] at h₃
    have ⟨n₁, hn₁⟩ := Int.eq_ofNat_of_zero_le h₃; subst hn₁
    simp only [Int.tdiv, Nat.succ_eq_add_one, Int.ofNat_eq_coe, Int.neg_natCast_le_natCast,
      Int.ofNat_le, true_and, ge_iff_le]
    simp only [Int.ofNat_le] at h₂
    simp only [Int.ofNat_pos] at h₀
    clear h₁ h₃ nlow
    simp only [Nat.le_div_iff_mul_le h₀]
    apply Nat.le_trans _ h₂
    apply Nat.div_mul_le_self

theorem mul_toInt_sdiv_eq_toInt_mul_sdiv {bv₁ bv₂ : BitVec 64}
  (h : 0 < bv₂.toInt) :
  bv₂.toInt * (bv₁.sdiv bv₂).toInt = (bv₂ * (bv₁.sdiv bv₂)).toInt
:= by
  have ⟨hmin, hmax⟩ := @sdiv_pos_bounded bv₁ _ h
  replace hmin := Int.mul_le_mul_of_nonneg_left hmin (Int.le_of_lt h)
  replace hmax := Int.mul_le_mul_of_nonneg_left hmax (Int.le_of_lt h)
  replace hmin := Int.le_trans (le_mul_left_tdiv_right_neg (by simp only [Int64.MIN, Int.reduceNeg, Int.reduceLE]) (Int.le_of_lt h)) hmin
  replace hmax := Int.le_trans hmax (mul_left_tdiv_right_pos_le (by simp only [Int64.MAX, Int.reduceLE]) (Int.le_of_lt h))
  symm; exact mul_toInt_eq_toInt_mul (And.intro hmin hmax)

theorem smtSDiv_eq_sdiv {n : Nat} {bv₁ bv₂ : BitVec n}
  (h : bv₂ ≠ 0) :
  bv₁.smtSDiv bv₂ = bv₁.sdiv bv₂
:= by
  simp only [ofNat_eq_ofNat, ne_eq] at h
  simp only [smtSDiv_eq, sdiv_eq, smtUDiv_eq, HDiv.hDiv, Div.div]
  simp only [h, ↓reduceIte, udiv_eq, neg_eq_zero_iff]

theorem bvule_iff_le {n : Nat} {bv₁ bv₂ : BitVec n} :
  bv₁.ule bv₂ = decide (bv₁ ≤ bv₂)
:= by
  simp only [BitVec.ule, decide_eq_true_eq]
  bv_omega

end BitVec

theorem Int.bmod_bounded_eq_self {n : Nat} {i : Int}
  (hlow : -2^n ≤ i)
  (hhigh : i ≤ 2^n - 1) :
  i.bmod (2^(n + 1)) = i
:= by
  cases h₀ : (0 ≤ i) == true
  case false =>
    simp only [beq_true, decide_eq_false_iff_not] at h₀
    replace ⟨n₀, h₀⟩ := Int.eq_negSucc_of_lt_zero (Int.lt_of_not_ge h₀); subst h₀
    simp only [Int.bmod, Int.emod_negSucc, Int.natAbs_ofNat]
    simp only [Int.negSucc_eq] at hlow
    replace hlow := Int.le_of_neg_le_neg hlow
    have hlow' : Int.ofNat (n₀ + 1) ≤ Int.ofNat (2^n) := by
      simp only [ofNat_eq_coe]
      apply Int.le_trans hlow
      simp only [Int.natCast_pow, cast_ofNat_Int, Int.le_refl]
    have h₀ : n₀.succ < 2^(n+1) := by
      simp only [ofNat_eq_coe, Int.ofNat_le] at hlow'
      omega
    simp only [Nat.mod_eq_of_lt (Nat.lt_of_succ_lt h₀)]
    simp only [Int.subNatNat_of_le (Nat.le_of_lt h₀)]
    have h₁ : ((Int.ofNat (2^(n + 1))) + 1) / 2 = Int.ofNat (2 ^ n) := by
      simp only [ofNat_eq_coe]; omega
    simp only [Int.ofNat_eq_coe] at h₁
    simp only [h₁]; clear h₁
    simp only [Int.ofNat_eq_coe, Int.ofNat_le] at hlow'
    omega
  case true =>
    simp only [beq_true, decide_eq_true_eq] at h₀
    simp only [Int.bmod, Int.emod_def]
    have h₁ : i < Int.ofNat (2^(n+1)) := by
      simp only [ofNat_eq_coe, Int.natCast_pow, cast_ofNat_Int]; omega
    have h₂ : i / Int.ofNat (2^(n+1)) = 0 := by exact Int.ediv_eq_zero_of_lt h₀ h₁
    simp only [← Int.ofNat_eq_coe, h₂, Int.mul_zero, Int.sub_zero]
    have h₄ : (2 ^ n) - 1 < (Int.ofNat (2 ^ (n + 1)) + 1) / 2 := by
      simp only [ofNat_eq_coe, Int.natCast_pow, cast_ofNat_Int]; omega
    simp only [Int.lt_of_le_of_lt hhigh h₄, ↓reduceIte]
