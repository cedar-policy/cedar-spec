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
public import CedarRustModel.Ext.Convert
import all Cedar.Spec.Ext.IPAddr
import Mathlib.Tactic.IntervalCases

/-! The IP-address predicates of the model (`ip_is_v4`, `ip_is_v6`,
`ip_is_loopback`, `ip_is_multicast`, `ip_in_range`) are Lean's, on
well-formed networks. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model
open Cedar.Spec.Ext Cedar.Spec.Ext.IPAddr

public section

/-! ## Masks -/

/-- The network mask of a `w`-bit address with prefix length `p` -/
def netmaskBV (w p : Nat) : BitVec w := if p = 0 then 0 else BitVec.allOnes w <<< (w - p)

/-- The host mask of a `w`-bit address with prefix length `p` -/
def hostmaskBV (w p : Nat) : BitVec w := if p = w then 0 else BitVec.allOnes w >>> p

@[step] theorem v4_netmask_spec (p : U8) :
    ext.v4_netmask p ⦃ r => r.bv = netmaskBV 32 (min p.val 32) ⦄ := by
  unfold ext.v4_netmask netmaskBV
  by_cases h0 : p = 0#u8
  · have : p.val = 0 := by scalar_tac
    simp [h0, this, WP.spec_ok]
  · by_cases h1 : p > 32#u8
    · have h2 : min p.val 32 = 32 := by scalar_tac
      simp only [h0, h1, ite_false, ite_true, h2, WP.spec_ok]; simp
    · have h2 : min p.val 32 = p.val := by scalar_tac
      have h3 : p.val ≠ 0 := by scalar_tac
      simp only [h0, h1, ite_false, h2, h3]
      step*

@[step] theorem v4_hostmask_spec (p : U8) :
    ext.v4_hostmask p ⦃ r => r.bv = hostmaskBV 32 (min p.val 32) ⦄ := by
  unfold ext.v4_hostmask hostmaskBV
  by_cases h0 : p >= 32#u8
  · have : min p.val 32 = 32 := by scalar_tac
    simp [h0, this, WP.spec_ok]
  · have h2 : min p.val 32 = p.val := by scalar_tac
    have h3 : p.val ≠ 32 := by scalar_tac
    simp only [h0, ite_false, h2, h3]
    step*

@[step] theorem v6_netmask_spec (p : U8) :
    ext.v6_netmask p ⦃ r => r.bv = netmaskBV 128 (min p.val 128) ⦄ := by
  unfold ext.v6_netmask netmaskBV
  by_cases h0 : p = 0#u8
  · have : p.val = 0 := by scalar_tac
    simp [h0, this, WP.spec_ok]
  · by_cases h1 : p > 128#u8
    · have h2 : min p.val 128 = 128 := by scalar_tac
      simp only [h0, h1, ite_false, ite_true, h2, WP.spec_ok]; simp
    · have h2 : min p.val 128 = p.val := by scalar_tac
      have h3 : p.val ≠ 0 := by scalar_tac
      simp only [h0, h1, ite_false, h2, h3]
      step*

@[step] theorem v6_hostmask_spec (p : U8) :
    ext.v6_hostmask p ⦃ r => r.bv = hostmaskBV 128 (min p.val 128) ⦄ := by
  unfold ext.v6_hostmask hostmaskBV
  by_cases h0 : p >= 128#u8
  · have : min p.val 128 = 128 := by scalar_tac
    simp [h0, this, WP.spec_ok]
  · have h2 : min p.val 128 = p.val := by scalar_tac
    have h3 : p.val ≠ 128 := by scalar_tac
    simp only [h0, ite_false, h2, h3]
    step*

/-! ## Arithmetic of masks -/

theorem lo_bound {w n : Nat} (hn : n ≤ w) (a : Nat) (ha : a < 2 ^ w) : a / 2 ^ n * 2 ^ n + 2 ^ n ≤ 2 ^ w := by
  have hp : 2 ^ w = 2 ^ (w - n) * 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : a / 2 ^ n < 2 ^ (w - n) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [← hp]; exact ha
  have : (a / 2 ^ n + 1) * 2 ^ n ≤ 2 ^ (w - n) * 2 ^ n := Nat.mul_le_mul_right _ h1
  rw [hp]; nlinarith

theorem pow_sub_one_div {w n : Nat} (hn : n ≤ w) : (2 ^ w - 1) / 2 ^ (w - n) = 2 ^ n - 1 := by
  have hp : 2 ^ w = 2 ^ n * 2 ^ (w - n) := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : 1 ≤ 2 ^ (w - n) := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h3 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, ← hp, Nat.one_mul]; omega
  · rw [Nat.sub_add_cancel h2, ← hp]; omega

theorem lo_toNat {w : Nat} (x : BitVec w) (n : Nat) :
    (x >>> n <<< n).toNat = x.toNat / 2 ^ n * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ _) x.isLt)

theorem hi_toNat {w : Nat} (hw : 0 < w) (x : BitVec w) (n : Nat) (hn : n ≤ w) :
    (x >>> n <<< n + 1#w <<< n - 1#w).toNat = x.toNat / 2 ^ n * 2 ^ n + 2 ^ n - 1 := by
  have hb := lo_bound hn x.toNat x.isLt
  have hM : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hw)
  have h1 : (1#w).toNat = 1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM]
  rw [BitVec.toNat_sub, BitVec.toNat_add, lo_toNat, h1, BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq, Nat.one_mul]
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  generalize x.toNat / 2 ^ n * 2 ^ n = L at hb ⊢
  by_cases hnw : n < w
  · have : 2 ^ n < 2 ^ w := Nat.pow_lt_pow_right (by omega) hnw
    rw [Nat.mod_eq_of_lt this]
    rcases Nat.lt_or_ge (L + 2 ^ n) (2 ^ w) with h | h
    · rw [Nat.mod_eq_of_lt h]
      rw [show 2 ^ w - 1 + (L + 2 ^ n) = (L + 2 ^ n - 1) + 2 ^ w by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · have he : L + 2 ^ n = 2 ^ w := by omega
      rw [he, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  · have he : n = w := by omega
    subst he
    rw [Nat.mod_self]
    have hL : L = 0 ∨ L + 2 ^ n ≤ 2 ^ n := by omega
    have : L = 0 := by omega
    subst this
    simp

theorem and_mask_toNat {w : Nat} (x : BitVec w) (n : Nat) :
    (x &&& BitVec.allOnes w <<< n).toNat = x.toNat / 2 ^ n * 2 ^ n := by
  rw [← BitVec.shiftLeft_ushiftRight, lo_toNat]

theorem or_mask_toNat {w : Nat} (x : BitVec w) (n : Nat) (hn : n ≤ w) :
    (x ||| BitVec.allOnes w >>> (w - n)).toNat = x.toNat / 2 ^ n * 2 ^ n + 2 ^ n - 1 := by
  have e : x ||| BitVec.allOnes w >>> (w - n) = (x &&& BitVec.allOnes w <<< n) ||| BitVec.allOnes w >>> (w - n) := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight,
      BitVec.getElem_allOnes]
    by_cases h : i < n <;> simp [h] <;> omega
  have z : (x &&& BitVec.allOnes w <<< n) &&& BitVec.allOnes w >>> (w - n) = 0#w := by
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight,
      BitVec.getElem_allOnes, BitVec.getElem_zero]
    by_cases h : i < n <;> simp [h] <;> omega
  rw [e, ← BitVec.add_eq_or_of_and_eq_zero _ _ z, BitVec.toNat_add, and_mask_toNat,
    BitVec.toNat_ushiftRight, BitVec.toNat_allOnes, Nat.shiftRight_eq_div_pow, pow_sub_one_div hn]
  have hb := lo_bound hn x.toNat x.isLt
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem and_nm_toNat {w : Nat} (x : BitVec w) (p : Nat) (hp : p ≤ w) :
    (x &&& netmaskBV w p).toNat = x.toNat / 2 ^ (w - p) * 2 ^ (w - p) := by
  unfold netmaskBV
  split
  · rename_i h; subst h
    simp only [BitVec.and_zero, BitVec.toNat_zero, Nat.sub_zero]
    rw [Nat.div_eq_of_lt x.isLt]; simp
  · exact and_mask_toNat x (w - p)

theorem or_hm_toNat {w : Nat} (x : BitVec w) (p : Nat) (hp : p ≤ w) :
    (x ||| hostmaskBV w p).toNat = x.toNat / 2 ^ (w - p) * 2 ^ (w - p) + 2 ^ (w - p) - 1 := by
  unfold hostmaskBV
  split
  · rename_i h; subst h; simp
  · have := or_mask_toNat x (w - p) (by omega)
    rwa [show w - (w - p) = p by omega] at this

/-! ## CIDR ranges -/

theorem range_of {w : Nat} (hw : 0 < w) (x W : BitVec w) (n : Nat) (hW : W.toNat = n) (hn : n ≤ w) :
    (x >>> W <<< W).toNat = x.toNat / 2 ^ n * 2 ^ n ∧
    (x >>> W <<< W + 1#w <<< W - 1#w).toNat = x.toNat / 2 ^ n * 2 ^ n + 2 ^ n - 1 := by
  simp only [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', hW]
  exact ⟨lo_toNat x n, hi_toNat hw x n hn⟩

theorem range_v4 (x : BitVec 32) (p : Nat) (hp : p ≤ 32) :
    (CIDR.mk (w := V4_WIDTH) x (prefixOfNat V4_WIDTH p)).range.1.toNat = x.toNat / 2 ^ (32 - p) * 2 ^ (32 - p) ∧
    (CIDR.mk (w := V4_WIDTH) x (prefixOfNat V4_WIDTH p)).range.2.toNat =
      x.toNat / 2 ^ (32 - p) * 2 ^ (32 - p) + 2 ^ (32 - p) - 1 := by
  unfold CIDR.range CIDR.subnetWidth prefixOfNat
  simp only [ADDR_SIZE, V4_WIDTH, Nat.reducePow]
  by_cases h : p < 32
  · simp only [h, ite_true]
    exact range_of (by omega) x _ (32 - p) (by rw [BitVec.toNat_sub]; simp; omega) (by omega)
  · have : p = 32 := by omega
    subst this
    simp only [Nat.lt_irrefl, ite_false]
    exact range_of (by omega) x _ 0 (by simp) (by omega)

theorem range_v6 (x : BitVec 128) (p : Nat) (hp : p ≤ 128) :
    (CIDR.mk (w := V6_WIDTH) x (prefixOfNat V6_WIDTH p)).range.1.toNat = x.toNat / 2 ^ (128 - p) * 2 ^ (128 - p) ∧
    (CIDR.mk (w := V6_WIDTH) x (prefixOfNat V6_WIDTH p)).range.2.toNat =
      x.toNat / 2 ^ (128 - p) * 2 ^ (128 - p) + 2 ^ (128 - p) - 1 := by
  unfold CIDR.range CIDR.subnetWidth prefixOfNat
  simp only [ADDR_SIZE, V6_WIDTH, Nat.reducePow]
  by_cases h : p < 128
  · simp only [h, ite_true]
    exact range_of (by omega) x _ (128 - p) (by rw [BitVec.toNat_sub]; simp; omega) (by omega)
  · have : p = 128 := by omega
    subst this
    simp only [Nat.lt_irrefl, ite_false]
    exact range_of (by omega) x _ 0 (by simp) (by omega)

theorem pre_clip (w p : Nat) (hw : 2 ^ w < 2 ^ (2 ^ w)) :
    prefixOfNat w p = prefixOfNat w (min p (2 ^ w)) := by
  rw [XV.prefix_eq w _ _ hw]; omega

theorem range_v4' (x : BitVec 32) (p : Nat) :
    (CIDR.mk (w := V4_WIDTH) x (prefixOfNat V4_WIDTH p)).range.1.toNat =
      x.toNat / 2 ^ (32 - min p 32) * 2 ^ (32 - min p 32) ∧
    (CIDR.mk (w := V4_WIDTH) x (prefixOfNat V4_WIDTH p)).range.2.toNat =
      x.toNat / 2 ^ (32 - min p 32) * 2 ^ (32 - min p 32) + 2 ^ (32 - min p 32) - 1 := by
  rw [pre_clip 5 p (by decide)]
  exact range_v4 x _ (by omega)

theorem range_v6' (x : BitVec 128) (p : Nat) :
    (CIDR.mk (w := V6_WIDTH) x (prefixOfNat V6_WIDTH p)).range.1.toNat =
      x.toNat / 2 ^ (128 - min p 128) * 2 ^ (128 - min p 128) ∧
    (CIDR.mk (w := V6_WIDTH) x (prefixOfNat V6_WIDTH p)).range.2.toNat =
      x.toNat / 2 ^ (128 - min p 128) * 2 ^ (128 - min p 128) + 2 ^ (128 - min p 128) - 1 := by
  rw [pre_clip 7 p (by decide)]
  exact range_v6 x _ (by omega)

/-! ## Predicates -/

theorem bv32_ofNat (x : U32) : BitVec.ofNat 32 x.val = x.bv := by
  rw [← UScalar.bv_toNat, BitVec.ofNat_toNat]; exact BitVec.setWidth_eq x.bv
theorem bv128_ofNat (x : U128) : BitVec.ofNat 128 x.val = x.bv := by
  rw [← UScalar.bv_toNat, BitVec.ofNat_toNat]; exact BitVec.setWidth_eq x.bv

theorem le_u32 (a b : U32) : (a ≤ b) ↔ a.bv.toNat ≤ b.bv.toNat := by
  rw [UScalar.bv_toNat, UScalar.bv_toNat]; exact Iff.rfl
theorem lt_u32 (a b : U32) : (a < b) ↔ a.bv.toNat < b.bv.toNat := by
  rw [UScalar.bv_toNat, UScalar.bv_toNat]; exact Iff.rfl
theorem le_u128 (a b : U128) : (a ≤ b) ↔ a.bv.toNat ≤ b.bv.toNat := by
  rw [UScalar.bv_toNat, UScalar.bv_toNat]; exact Iff.rfl
theorem lt_u128 (a b : U128) : (a < b) ↔ a.bv.toNat < b.bv.toNat := by
  rw [UScalar.bv_toNat, UScalar.bv_toNat]; exact Iff.rfl

@[step] theorem ip_in_range_spec (a b : ext.IPNet) :
    ext.ip_in_range a b ⦃ r => r = (IPNet.toSpec a).inRange (IPNet.toSpec b) ⦄ := by
  unfold ext.ip_in_range
  cases a with
  | V4 x p =>
    cases b with
    | V4 y q =>
      obtain ⟨r1, r2⟩ := range_v4' x.bv p.val
      obtain ⟨r3, r4⟩ := range_v4' y.bv q.val
      have m1 := and_nm_toNat x.bv (min p.val 32) (by omega)
      have m2 := and_nm_toNat y.bv (min q.val 32) (by omega)
      have m3 := or_hm_toNat x.bv (min p.val 32) (by omega)
      have m4 := or_hm_toNat y.bv (min q.val 32) (by omega)
      step*
      all_goals (simp only [IPNet.toSpec, IPAddr.IPNet.inRange, CIDR.inRange, bv32_ofNat, GE.ge,
        BitVec.le_def, r1, r2, r3, r4])
      all_goals (simp only [le_u32, lt_u32] at *)
      all_goals simp_all
    | V6 y q => simp [IPNet.toSpec, IPAddr.IPNet.inRange, WP.spec_ok]
  | V6 x p =>
    cases b with
    | V4 y q => simp [IPNet.toSpec, IPAddr.IPNet.inRange, WP.spec_ok]
    | V6 y q =>
      obtain ⟨r1, r2⟩ := range_v6' x.bv p.val
      obtain ⟨r3, r4⟩ := range_v6' y.bv q.val
      have m1 := and_nm_toNat x.bv (min p.val 128) (by omega)
      have m2 := and_nm_toNat y.bv (min q.val 128) (by omega)
      have m3 := or_hm_toNat x.bv (min p.val 128) (by omega)
      have m4 := or_hm_toNat y.bv (min q.val 128) (by omega)
      step*
      all_goals (simp only [IPNet.toSpec, IPAddr.IPNet.inRange, CIDR.inRange, bv128_ofNat, GE.ge,
        BitVec.le_def, r1, r2, r3, r4])
      all_goals (simp only [le_u128, lt_u128] at *)
      all_goals simp_all

theorem loop4_nat (X n : Nat) (hX : X < 2 ^ 32) (hn : n ≤ 32) :
    (X / 2 ^ n * 2 ^ n + 2 ^ n - 1 ≤ 2147483647 ∧ 2130706432 ≤ X / 2 ^ n * 2 ^ n) ↔
      (X / 2 ^ 24 = 127 ∧ n ≤ 24) := by
  interval_cases n <;> omega

theorem mc4_nat (X n : Nat) (hX : X < 2 ^ 32) (hn : n ≤ 32) :
    (X / 2 ^ n * 2 ^ n + 2 ^ n - 1 ≤ 4026531839 ∧ 3758096384 ≤ X / 2 ^ n * 2 ^ n) ↔
      (X / 2 ^ 28 = 14 ∧ n ≤ 28) := by
  interval_cases n <;> omega

theorem loop6_nat (X n : Nat) (hX : X < 2 ^ 128) (hn : n ≤ 128) :
    (X / 2 ^ n * 2 ^ n + 2 ^ n - 1 ≤ 1 ∧ 1 ≤ X / 2 ^ n * 2 ^ n) ↔ (X = 1 ∧ n = 0) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp; omega
  · have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    constructor
    · intro ⟨h1, h2⟩; omega
    · intro ⟨_, h2⟩; omega

theorem mc6_nat (X n : Nat) (hX : X < 2 ^ 128) (hn : n ≤ 128) :
    (X / 2 ^ n * 2 ^ n + 2 ^ n - 1 ≤ 340282366920938463463374607431768211455 ∧
      338953138925153547590470800371487866880 ≤ X / 2 ^ n * 2 ^ n) ↔
      (X / 2 ^ 120 = 255 ∧ n ≤ 120) := by
  interval_cases n <;> omega

theorem bool_glue {c b : Bool} {P Q R S : Prop} [Decidable P] [Decidable Q] [Decidable R] [Decidable S]
    (key : (R ∧ S) ↔ (P ∧ Q)) (hc : c = decide P) (hb : b = decide Q) :
    (if c = true then b else false) = (decide R && decide S) := by
  subst hc hb
  by_cases hP : P <;> by_cases hQ : Q <;> simp_all

theorem loop_v4_eq : LOOP_BACK_CIDR_V4 = CIDR.mk (w := V4_WIDTH) 2130706432#32 (prefixOfNat V4_WIDTH 8) := by
  decide
theorem mc_v4_eq : MULTICAST_CIDR_V4 = CIDR.mk (w := V4_WIDTH) 3758096384#32 (prefixOfNat V4_WIDTH 4) := by
  decide
theorem loop_v6_eq : LOOP_BACK_CIDR_V6 = CIDR.mk (w := V6_WIDTH) 1#128 (prefixOfNat V6_WIDTH 128) := by
  decide
theorem mc_v6_eq : MULTICAST_CIDR_V6 =
    CIDR.mk (w := V6_WIDTH) 338953138925153547590470800371487866880#128 (prefixOfNat V6_WIDTH 8) := by
  decide

@[step] theorem ip_is_v4_spec (a : ext.IPNet) : ext.ip_is_v4 a ⦃ r => r = (IPNet.toSpec a).isV4 ⦄ := by
  cases a <;> simp [ext.ip_is_v4, IPNet.toSpec, IPAddr.IPNet.isV4, WP.spec_ok]

@[step] theorem ip_is_v6_spec (a : ext.IPNet) : ext.ip_is_v6 a ⦃ r => r = (IPNet.toSpec a).isV6 ⦄ := by
  cases a <;> simp [ext.ip_is_v6, IPNet.toSpec, IPAddr.IPNet.isV6, WP.spec_ok]

theorem shr_val (x : U32) (k : I32) (hk : 0 ≤ k.val ∧ k.val < 32) :
    ∃ r, x >>> k = ok r ∧ r.val = x.bv.toNat / 2 ^ k.toNat := by
  obtain ⟨r, h1, h2, _⟩ := spec_ok_exists (U32.ShiftRight_IScalar_spec x k hk.1 hk.2)
  exact ⟨r, h1, by rw [h2, UScalar.bv_toNat, Nat.shiftRight_eq_div_pow]⟩

theorem shr_val128 (x : U128) (k : I32) (hk : 0 ≤ k.val ∧ k.val < 128) :
    ∃ r, x >>> k = ok r ∧ r.val = x.bv.toNat / 2 ^ k.toNat := by
  obtain ⟨r, h1, h2, _⟩ := spec_ok_exists (U128.ShiftRight_IScalar_spec x k hk.1 hk.2)
  exact ⟨r, h1, by rw [h2, UScalar.bv_toNat, Nat.shiftRight_eq_div_pow]⟩

theorem ite_ok {α} (c : Prop) [Decidable c] (a b : α) :
    (if c then ok a else ok b : Result α) = ok (if decide c = true then a else b) := by
  by_cases h : c <;> simp [h]

@[step] theorem ip_is_loopback_spec (a : ext.IPNet) :
    ext.ip_is_loopback a ⦃ r => r = (IPNet.toSpec a).isLoopback ⦄ := by
  unfold ext.ip_is_loopback
  cases a with
  | V4 x p =>
    have hpq : (8#u8 ≤ p) ↔ 32 - min p.val 32 ≤ 24 := by constructor <;> intro <;> scalar_tac
    obtain ⟨r1, r2⟩ := range_v4' x.bv p.val
    obtain ⟨r3, r4⟩ := range_v4 2130706432#32 8 (by omega)
    have r3' : (2130706432#32).toNat / 2 ^ (32 - 8) * 2 ^ (32 - 8) = 2130706432 := by decide
    have r4' : (2130706432#32).toNat / 2 ^ (32 - 8) * 2 ^ (32 - 8) + 2 ^ (32 - 8) - 1 = 2147483647 := by decide
    simp only [IPNet.toSpec, IPAddr.IPNet.isLoopback, loop_v4_eq, CIDR.inRange, bv32_ofNat, GE.ge,
      BitVec.le_def, r1, r2, r3, r4, r3', r4']
    obtain ⟨r, hr1, hr2⟩ := shr_val x 24#i32 (by scalar_tac)
    rw [hr1]; simp only [bind_ok]
    have e24 : I32.toNat 24#i32 = 24 := rfl
    rw [e24] at hr2
    rw [ite_ok, WP.spec_ok]
    apply bool_glue (loop4_nat x.bv.toNat (32 - min p.val 32) x.bv.isLt (by omega))
    · simp only [decide_eq_decide]
      constructor
      · intro h; have : r.val = (127 : Nat) := by rw [h]; rfl
        omega
      · intro h; apply UScalar.eq_of_val_eq; rw [hr2, h]; rfl
    · simp only [decide_eq_decide]; exact hpq
  | V6 x p =>
    have hpq : (128#u8 ≤ p) ↔ 128 - min p.val 128 = 0 := by constructor <;> intro <;> scalar_tac
    obtain ⟨r1, r2⟩ := range_v6' x.bv p.val
    obtain ⟨r3, r4⟩ := range_v6 1#128 128 (by omega)
    have r3' : (1#128).toNat / 2 ^ (128 - 128) * 2 ^ (128 - 128) = 1 := by decide
    have r4' : (1#128).toNat / 2 ^ (128 - 128) * 2 ^ (128 - 128) + 2 ^ (128 - 128) - 1 = 1 := by decide
    simp only [IPNet.toSpec, IPAddr.IPNet.isLoopback, loop_v6_eq, CIDR.inRange, bv128_ofNat, GE.ge,
      BitVec.le_def, r1, r2, r3, r4, r3', r4']
    rw [ite_ok, WP.spec_ok]
    apply bool_glue (loop6_nat x.bv.toNat (128 - min p.val 128) x.bv.isLt (by omega))
    · simp only [decide_eq_decide]
      constructor
      · intro h; rw [h]; rfl
      · intro h; apply UScalar.eq_of_val_eq; rw [← UScalar.bv_toNat, h]; rfl
    · simp only [decide_eq_decide]; exact hpq

@[step] theorem ip_is_multicast_spec (a : ext.IPNet) :
    ext.ip_is_multicast a ⦃ r => r = (IPNet.toSpec a).isMulticast ⦄ := by
  unfold ext.ip_is_multicast
  cases a with
  | V4 x p =>
    have hpq : (4#u8 ≤ p) ↔ 32 - min p.val 32 ≤ 28 := by constructor <;> intro <;> scalar_tac
    obtain ⟨r1, r2⟩ := range_v4' x.bv p.val
    obtain ⟨r3, r4⟩ := range_v4 3758096384#32 4 (by omega)
    have r3' : (3758096384#32).toNat / 2 ^ (32 - 4) * 2 ^ (32 - 4) = 3758096384 := by decide
    have r4' : (3758096384#32).toNat / 2 ^ (32 - 4) * 2 ^ (32 - 4) + 2 ^ (32 - 4) - 1 = 4026531839 := by decide
    simp only [IPNet.toSpec, IPAddr.IPNet.isMulticast, mc_v4_eq, CIDR.inRange, bv32_ofNat, GE.ge,
      BitVec.le_def, r1, r2, r3, r4, r3', r4']
    obtain ⟨r, hr1, hr2⟩ := shr_val x 28#i32 (by scalar_tac)
    rw [hr1]; simp only [bind_ok]
    have e28 : I32.toNat 28#i32 = 28 := rfl
    rw [e28] at hr2
    rw [ite_ok, WP.spec_ok]
    apply bool_glue (mc4_nat x.bv.toNat (32 - min p.val 32) x.bv.isLt (by omega))
    · simp only [decide_eq_decide]
      constructor
      · intro h; have : r.val = (14 : Nat) := by rw [h]; rfl
        omega
      · intro h; apply UScalar.eq_of_val_eq; rw [hr2, h]; rfl
    · simp only [decide_eq_decide]; exact hpq
  | V6 x p =>
    have hpq : (8#u8 ≤ p) ↔ 128 - min p.val 128 ≤ 120 := by constructor <;> intro <;> scalar_tac
    obtain ⟨r1, r2⟩ := range_v6' x.bv p.val
    obtain ⟨r3, r4⟩ := range_v6 338953138925153547590470800371487866880#128 8 (by omega)
    have r3' : (338953138925153547590470800371487866880#128).toNat / 2 ^ (128 - 8) * 2 ^ (128 - 8) =
        338953138925153547590470800371487866880 := by decide
    have r4' : (338953138925153547590470800371487866880#128).toNat / 2 ^ (128 - 8) * 2 ^ (128 - 8) +
        2 ^ (128 - 8) - 1 = 340282366920938463463374607431768211455 := by decide
    simp only [IPNet.toSpec, IPAddr.IPNet.isMulticast, mc_v6_eq, CIDR.inRange, bv128_ofNat, GE.ge,
      BitVec.le_def, r1, r2, r3, r4, r3', r4']
    obtain ⟨r, hr1, hr2⟩ := shr_val128 x 120#i32 (by scalar_tac)
    rw [hr1]; simp only [bind_ok]
    have e120 : I32.toNat 120#i32 = 120 := rfl
    rw [e120] at hr2
    rw [ite_ok, WP.spec_ok]
    apply bool_glue (mc6_nat x.bv.toNat (128 - min p.val 128) x.bv.isLt (by omega))
    · simp only [decide_eq_decide]
      constructor
      · intro h; have : r.val = (255 : Nat) := by rw [h]; rfl
        omega
      · intro h; apply UScalar.eq_of_val_eq; rw [hr2, h]; rfl
    · simp only [decide_eq_decide]; exact hpq

end

end CedarRustModel
