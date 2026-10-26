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

public import CedarRustModel.Convert
import all Cedar.Spec.Ext.IPAddr
import all Cedar.Spec.Ext.Datetime
import all Cedar.Spec.Ext

/-! Cloning, equality and order of the model's extension values (`ext.rs`): they
are Lean's on the translated values, for all values. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model
open Cedar.Spec

public section

namespace XV

theorem toInt_ofInt_val (i : I64) : (Int64.ofInt i.val).toInt = i.val := by
  have h := i.hBounds
  rw [Int64.toInt_ofInt]
  simp at h ⊢

theorem ofInt_val_inj (x y : I64) : Int64.ofInt x.val = Int64.ofInt y.val ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg Int64.toInt h
    rw [toInt_ofInt_val, toInt_ofInt_val] at h'
    exact IScalar.eq_of_val_eq h'
  · intro h; rw [h]

theorem bv_ofNat32 (x : U32) : BitVec.ofNat 32 x.val = x.bv := by
  rw [← UScalar.bv_toNat, BitVec.ofNat_toNat]; exact BitVec.setWidth_eq x.bv

theorem bv_ofNat128 (x : U128) : BitVec.ofNat 128 x.val = x.bv := by
  rw [← UScalar.bv_toNat, BitVec.ofNat_toNat]; exact BitVec.setWidth_eq x.bv

theorem bv32_inj (x y : U32) : BitVec.ofNat 32 x.val = BitVec.ofNat 32 y.val ↔ x = y := by
  rw [bv_ofNat32, bv_ofNat32]
  constructor
  · intro h; apply UScalar.eq_of_val_eq
    rw [← UScalar.bv_toNat, ← UScalar.bv_toNat]; exact congrArg BitVec.toNat h
  · intro h; rw [h]

theorem bv128_inj (x y : U128) : BitVec.ofNat 128 x.val = BitVec.ofNat 128 y.val ↔ x = y := by
  rw [bv_ofNat128, bv_ofNat128]
  constructor
  · intro h; apply UScalar.eq_of_val_eq
    rw [← UScalar.bv_toNat, ← UScalar.bv_toNat]; exact congrArg BitVec.toNat h
  · intro h; rw [h]

theorem bveq32 (x y : U32) : x.bv = y.bv ↔ x = y := by rw [← bv_ofNat32, ← bv_ofNat32, bv32_inj]
theorem bveq128 (x y : U128) : x.bv = y.bv ↔ x = y := by rw [← bv_ofNat128, ← bv_ofNat128, bv128_inj]

theorem bv32_lt (x y : U32) : (BitVec.ofNat 32 x.val < BitVec.ofNat 32 y.val) ↔ x < y := by
  rw [bv_ofNat32, bv_ofNat32, BitVec.lt_def, UScalar.bv_toNat, UScalar.bv_toNat]; exact Iff.rfl

theorem bv128_lt (x y : U128) : (BitVec.ofNat 128 x.val < BitVec.ofNat 128 y.val) ↔ x < y := by
  rw [bv_ofNat128, bv_ofNat128, BitVec.lt_def, UScalar.bv_toNat, UScalar.bv_toNat]; exact Iff.rfl

/-- The length of a translated prefix: the prefix, clipped to the width -/
theorem prefix_toNat (w p : Nat) (hw : 2 ^ w < 2 ^ (2 ^ w)) :
    (prefixOfNat w p).toNat = min p (2 ^ w) := by
  unfold prefixOfNat
  split
  · rename_i h; simp only [Cedar.Spec.Ext.IPAddr.ADDR_SIZE] at h
    simp only [Cedar.Spec.Ext.IPAddr.IPNetPrefix.toNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rename_i h; simp only [Cedar.Spec.Ext.IPAddr.ADDR_SIZE] at h
    simp only [Cedar.Spec.Ext.IPAddr.IPNetPrefix.toNat, Cedar.Spec.Ext.IPAddr.ADDR_SIZE]; omega

theorem prefix_eq (w p q : Nat) (hw : 2 ^ w < 2 ^ (2 ^ w)) :
    prefixOfNat w p = prefixOfNat w q ↔ min p (2 ^ w) = min q (2 ^ w) := by
  constructor
  · intro h
    have := congrArg Cedar.Spec.Ext.IPAddr.IPNetPrefix.toNat h
    rwa [prefix_toNat w p hw, prefix_toNat w q hw] at this
  · intro h
    unfold prefixOfNat
    simp only [Cedar.Spec.Ext.IPAddr.ADDR_SIZE]
    by_cases hp : p < 2 ^ w <;> by_cases hq : q < 2 ^ w <;> simp only [hp, hq, ite_true, ite_false]
    · have : p = q := by omega
      rw [this]
    · omega
    · omega

theorem prefix_lt (w p q : Nat) (hw : 2 ^ w < 2 ^ (2 ^ w)) :
    (prefixOfNat w p < prefixOfNat w q) ↔ min p (2 ^ w) < min q (2 ^ w) := by
  show Cedar.Spec.Ext.IPAddr.IPNetPrefix.lt _ _ = true ↔ _
  simp [Cedar.Spec.Ext.IPAddr.IPNetPrefix.lt, prefix_toNat w p hw, prefix_toNat w q hw]

theorem cidr_lt_iff {w : Nat} (c1 c2 : Cedar.Spec.Ext.IPAddr.CIDR w) :
    (c1 < c2) ↔ (c1.addr < c2.addr ∨ (c1.addr = c2.addr ∧ c1.pre < c2.pre)) := by
  show Cedar.Spec.Ext.IPAddr.CIDR.lt c1 c2 = true ↔ _
  simp [Cedar.Spec.Ext.IPAddr.CIDR.lt]

theorem clip_v4_ok (p : U8) : ∃ c, ext.clip_v4 p = ok c ∧ c.val = min p.val 32 := by
  unfold ext.clip_v4
  by_cases h : p > 32#u8
  · exact ⟨32#u8, by simp [h], by scalar_tac⟩
  · exact ⟨p, by simp [h], by scalar_tac⟩

theorem clip_v6_ok (p : U8) : ∃ c, ext.clip_v6 p = ok c ∧ c.val = min p.val 128 := by
  unfold ext.clip_v6
  by_cases h : p > 128#u8
  · exact ⟨128#u8, by simp [h], by scalar_tac⟩
  · exact ⟨p, by simp [h], by scalar_tac⟩

theorem dt_lt_iff (a b : Cedar.Spec.Ext.Datetime) : (a < b) ↔ a.val < b.val := by
  show Cedar.Spec.Ext.Datetime.lt a b = true ↔ _; simp [Cedar.Spec.Ext.Datetime.lt]
theorem dt_le_iff (a b : Cedar.Spec.Ext.Datetime) : (a ≤ b) ↔ a.val ≤ b.val := by
  show Cedar.Spec.Ext.Datetime.le a b = true ↔ _; simp [Cedar.Spec.Ext.Datetime.le]
theorem dur_lt_iff (a b : Duration) : (a < b) ↔ a.val < b.val := by
  show Cedar.Spec.Ext.Datetime.Duration.lt a b = true ↔ _; simp [Cedar.Spec.Ext.Datetime.Duration.lt]
theorem dur_le_iff (a b : Duration) : (a ≤ b) ↔ a.val ≤ b.val := by
  show Cedar.Spec.Ext.Datetime.Duration.le a b = true ↔ _; simp [Cedar.Spec.Ext.Datetime.Duration.le]

theorem val_lt (x y : I64) : (x < y) ↔ Int64.ofInt x.val < Int64.ofInt y.val := by
  rw [Int64.lt_iff_toInt_lt, toInt_ofInt_val, toInt_ofInt_val]; exact Iff.rfl
theorem val_le (x y : I64) : (x ≤ y) ↔ Int64.ofInt x.val ≤ Int64.ofInt y.val := by
  rw [Int64.le_iff_toInt_le, toInt_ofInt_val, toInt_ofInt_val]; exact Iff.rfl

theorem val_lt' (x y : I64) : (x.val < y.val) ↔ Int64.ofInt x.val < Int64.ofInt y.val := by
  rw [Int64.lt_iff_toInt_lt, toInt_ofInt_val, toInt_ofInt_val]
theorem val_le' (x y : I64) : (x.val ≤ y.val) ↔ Int64.ofInt x.val ≤ Int64.ofInt y.val := by
  rw [Int64.le_iff_toInt_le, toInt_ofInt_val, toInt_ofInt_val]

theorem ipnet_lt_prop (x y : Cedar.Spec.Ext.IPAddr.IPNet) :
    (x < y) = (Cedar.Spec.Ext.IPAddr.IPNet.lt x y = true) := rfl

end XV

theorem clone_ext_ok (e : ext.Ext) : ext.clone_ext e = ok e := by
  rcases e with _ | (_ | _) | _ | _ <;> simp [ext.clone_ext, ext.clone_ipnet]

theorem toSpec_v4_eq (x y : U32) (p q : U8) :
    IPNet.toSpec (.V4 x p) = IPNet.toSpec (.V4 y q) ↔ x = y ∧ min p.val 32 = min q.val 32 := by
  simp only [IPNet.toSpec, Cedar.Spec.Ext.IPAddr.IPNet.V4.injEq, Cedar.Spec.Ext.IPAddr.CIDR.mk.injEq]
  rw [XV.bv32_inj, XV.prefix_eq 5 _ _ (by decide)]; rfl

theorem toSpec_v6_eq (x y : U128) (p q : U8) :
    IPNet.toSpec (.V6 x p) = IPNet.toSpec (.V6 y q) ↔ x = y ∧ min p.val 128 = min q.val 128 := by
  simp only [IPNet.toSpec, Cedar.Spec.Ext.IPAddr.IPNet.V6.injEq, Cedar.Spec.Ext.IPAddr.CIDR.mk.injEq]
  rw [XV.bv128_inj, XV.prefix_eq 7 _ _ (by decide)]; rfl

theorem ipnet_eq_ok (a b : ext.IPNet) :
    ext.ipnet_eq a b = ok (decide (IPNet.toSpec a = IPNet.toSpec b)) := by
  unfold ext.ipnet_eq
  cases a with
  | V4 x p =>
    cases b with
    | V6 y q => simp [IPNet.toSpec]
    | V4 y q =>
      obtain ⟨c, hc, hcv⟩ := XV.clip_v4_ok p
      obtain ⟨d, hd, hdv⟩ := XV.clip_v4_ok q
      simp only [toSpec_v4_eq]
      by_cases h : x = y
      · simp only [h, ite_true, hc, hd, bind_ok, true_and]
        congr 1
        rw [decide_eq_decide]
        constructor
        · intro e; rw [← hcv, ← hdv, e]
        · intro e; apply UScalar.eq_of_val_eq; omega
      · simp [h]
  | V6 x p =>
    cases b with
    | V4 y q => simp [IPNet.toSpec]
    | V6 y q =>
      obtain ⟨c, hc, hcv⟩ := XV.clip_v6_ok p
      obtain ⟨d, hd, hdv⟩ := XV.clip_v6_ok q
      simp only [toSpec_v6_eq]
      by_cases h : x = y
      · simp only [h, ite_true, hc, hd, bind_ok, true_and]
        congr 1
        rw [decide_eq_decide]
        constructor
        · intro e; rw [← hcv, ← hdv, e]
        · intro e; apply UScalar.eq_of_val_eq; omega
      · simp [h]

theorem ext_eq_ok (a b : ext.Ext) :
    ext.ext_eq a b = ok (decide (Ext.toSpec a = Ext.toSpec b)) := by
  unfold ext.ext_eq
  cases a <;> cases b <;> simp only [Ext.toSpec, reduceCtorEq, decide_false]
  all_goals (try simp only [Cedar.Spec.Ext.decimal.injEq, Cedar.Spec.Ext.datetime.injEq,
    Cedar.Spec.Ext.duration.injEq, Cedar.Spec.Ext.ipaddr.injEq, Cedar.Spec.Ext.Datetime.mk.injEq,
    Cedar.Spec.Ext.Datetime.Duration.mk.injEq, XV.ofInt_val_inj])
  all_goals (try exact ipnet_eq_ok _ _)
  all_goals rfl

theorem toSpec_v4_lt (x y : U32) (p q : U8) :
    Cedar.Spec.Ext.IPAddr.IPNet.lt (IPNet.toSpec (.V4 x p)) (IPNet.toSpec (.V4 y q)) =
      decide (x < y ∨ (x = y ∧ min p.val 32 < min q.val 32)) := by
  simp only [IPNet.toSpec, Cedar.Spec.Ext.IPAddr.IPNet.lt]
  rw [decide_eq_decide, XV.cidr_lt_iff]
  simp only
  rw [XV.bv32_lt, XV.bv32_inj, XV.prefix_lt 5 _ _ (by decide)]; rfl

theorem toSpec_v6_lt (x y : U128) (p q : U8) :
    Cedar.Spec.Ext.IPAddr.IPNet.lt (IPNet.toSpec (.V6 x p)) (IPNet.toSpec (.V6 y q)) =
      decide (x < y ∨ (x = y ∧ min p.val 128 < min q.val 128)) := by
  simp only [IPNet.toSpec, Cedar.Spec.Ext.IPAddr.IPNet.lt]
  rw [decide_eq_decide, XV.cidr_lt_iff]
  simp only
  rw [XV.bv128_lt, XV.bv128_inj, XV.prefix_lt 7 _ _ (by decide)]; rfl

theorem ipnet_lt_ok (a b : ext.IPNet) :
    ext.ipnet_lt a b = ok (Cedar.Spec.Ext.IPAddr.IPNet.lt (IPNet.toSpec a) (IPNet.toSpec b)) := by
  unfold ext.ipnet_lt
  cases a with
  | V4 x p =>
    cases b with
    | V6 y q => simp [IPNet.toSpec, Cedar.Spec.Ext.IPAddr.IPNet.lt]
    | V4 y q =>
      obtain ⟨c, hc, hcv⟩ := XV.clip_v4_ok p
      obtain ⟨d, hd, hdv⟩ := XV.clip_v4_ok q
      rw [toSpec_v4_lt]
      by_cases h1 : x < y
      · simp [h1]
      · by_cases h2 : x = y
        · subst h2
          have e : (c < d) ↔ (min p.val 32 < min q.val 32) := by
            rw [show (c < d) ↔ c.val < d.val from Iff.rfl, hcv, hdv]
          simp only [h1, ite_false, hc, hd, bind_ok, false_or, true_and, e, ↓reduceIte]
        · simp [h1, h2]
  | V6 x p =>
    cases b with
    | V4 y q => simp [IPNet.toSpec, Cedar.Spec.Ext.IPAddr.IPNet.lt]
    | V6 y q =>
      obtain ⟨c, hc, hcv⟩ := XV.clip_v6_ok p
      obtain ⟨d, hd, hdv⟩ := XV.clip_v6_ok q
      rw [toSpec_v6_lt]
      by_cases h1 : x < y
      · simp [h1]
      · by_cases h2 : x = y
        · subst h2
          have e : (c < d) ↔ (min p.val 128 < min q.val 128) := by
            rw [show (c < d) ↔ c.val < d.val from Iff.rfl, hcv, hdv]
          simp only [h1, ite_false, hc, hd, bind_ok, false_or, true_and, e, ↓reduceIte]
        · simp [h1, h2]

theorem ext_lt_ok (a b : ext.Ext) :
    ext.ext_lt a b = ok (Cedar.Spec.Ext.lt (Ext.toSpec a) (Ext.toSpec b)) := by
  unfold ext.ext_lt
  cases a <;> cases b <;> simp only [Ext.toSpec, Cedar.Spec.Ext.lt]
  all_goals (try (simp only [XV.ipnet_lt_prop, Bool.decide_eq_true]; exact ipnet_lt_ok _ _))
  all_goals (simp [XV.dt_lt_iff, XV.dur_lt_iff, XV.val_lt, XV.val_lt'])

theorem clone_extfun_ok (f : ext.ExtFun) : ext.clone_extfun f = ok f := by
  cases f <;> simp [ext.clone_extfun]

end -- public section

end CedarRustModel
