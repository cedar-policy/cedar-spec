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

import Cedar.Thm.SymCC.Compiler.Args
import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Compiler.WF

/-!
This file proves the compilation lemmas for `.call` expressions.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

----- PE lemmas for ExtFuns -----

private theorem pe_decimal_lessThan {d₁ d₂ : Ext.Decimal} :
  Decimal.lessThan (Term.prim (TermPrim.ext (Ext.decimal d₁))) (Term.prim (TermPrim.ext (Ext.decimal d₂))) =
  Term.prim (TermPrim.bool (decide (d₁ < d₂)))
:= by
  simp only [Decimal.lessThan, pe_ext_decimal_val, pe_bvslt, LT.lt, Int64.lt, Bool.decide_eq_true]

private theorem pe_decimal_lessThanOrEqual {d₁ d₂ : Ext.Decimal} :
  Decimal.lessThanOrEqual (Term.prim (TermPrim.ext (Ext.decimal d₁))) (Term.prim (TermPrim.ext (Ext.decimal d₂))) =
  Term.prim (TermPrim.bool (decide (d₁ ≤ d₂)))
:= by
  simp only [Decimal.lessThanOrEqual, pe_ext_decimal_val, pe_bvsle, LE.le, Int64.le,
    Bool.decide_eq_true]

private theorem pe_decimal_greaterThan {d₁ d₂ : Ext.Decimal} :
  Decimal.greaterThan (Term.prim (TermPrim.ext (Ext.decimal d₁))) (Term.prim (TermPrim.ext (Ext.decimal d₂))) =
  Term.prim (TermPrim.bool (decide (d₁ > d₂)))
:= by simp only [Decimal.greaterThan, pe_decimal_lessThan, gt_iff_lt]

private theorem pe_decimal_greaterThanOrEqual {d₁ d₂ : Ext.Decimal} :
  Decimal.greaterThanOrEqual (Term.prim (TermPrim.ext (Ext.decimal d₁))) (Term.prim (TermPrim.ext (Ext.decimal d₂))) =
  Term.prim (TermPrim.bool (decide (d₁ ≥ d₂)))
:= by simp only [Decimal.greaterThanOrEqual, pe_decimal_lessThanOrEqual, ge_iff_le]

private theorem pe_ipaddr_isIpv4 {ip : Ext.IPAddr.IPNet} :
  IPAddr.isIpv4 (Term.prim (TermPrim.ext (Ext.ipaddr ip))) = ip.isV4
:= by
  simp only [IPAddr.isIpv4, Ext.IPAddr.IPNet.isV4]
  cases ip <;>
  simp only [pe_ext_ipaddr_isV4_V4, pe_ext_ipaddr_isV4_V6]

private theorem pe_ipaddr_isIpv6 {ip : Ext.IPAddr.IPNet} :
  IPAddr.isIpv6 (Term.prim (TermPrim.ext (Ext.ipaddr ip))) = ip.isV6
:= by
  simp only [IPAddr.isIpv6, Ext.IPAddr.IPNet.isV6]
  cases ip <;>
  simp only [pe_ext_ipaddr_isV4_V4, pe_ext_ipaddr_isV4_V6, pe_not_true, pe_not_false]

private theorem pe_ipaddr_isIpv4_V4 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} :
  IPAddr.isIpv4 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V4 cidr)))) = true
:= by
  simp only [IPAddr.isIpv4, pe_ext_ipaddr_isV4_V4]

private theorem pe_ipaddr_isIpv4_V6 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH} :
  IPAddr.isIpv4 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V6 cidr)))) = false
:= by
  simp only [IPAddr.isIpv4, pe_ext_ipaddr_isV4_V6]

private theorem pe_ipaddr_isIpv6_V4 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} :
  IPAddr.isIpv6 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V4 cidr)))) = false
:= by
  simp only [IPAddr.isIpv6, pe_ext_ipaddr_isV4_V4, pe_not_true]

private theorem pe_ipaddr_isIpv6_V6 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH} :
  IPAddr.isIpv6 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V6 cidr)))) = true
:= by
  simp only [IPAddr.isIpv6, pe_ext_ipaddr_isV4_V6, pe_not_false]

private theorem pe_ipaddr_subnetWidth {w : Nat} {cidr : Ext.IPAddr.CIDR w} :
  IPAddr.subnetWidth w (cidrPrefixTerm cidr) = Ext.IPAddr.CIDR.subnetWidth cidr
:= by
  simp only [IPAddr.subnetWidth, cidrPrefixTerm, Ext.IPAddr.CIDR.subnetWidth]
  split <;> rename_i heq <;> simp only [heq]
  · simp only [pe_isNone_none, pe_ite_true]
  · simp only [pe_isNone_some, Ext.IPAddr.ADDR_SIZE, pe_option_get_some, pe_ite_false]
    have h := @Nat.lt_two_pow_self w
    have h : w ≤ 2 ^ w := by omega
    simp only [pe_zero_extend h, pe_bvsub, BitVec.sub_eq, BitVec.natCast_eq_ofNat]

private theorem pe_ipaddr_range {w : Nat} {cidr : Ext.IPAddr.CIDR w} :
  IPAddr.range w (Term.prim (TermPrim.bitvec cidr.addr)) (cidrPrefixTerm cidr) =
  (Ext.IPAddr.CIDR.range cidr).map Term.bitvec Term.bitvec
:= by
  simp only [IPAddr.range, pe_ipaddr_subnetWidth, pe_bvlshr, pe_bvshl, pe_bvadd, BitVec.add_eq,
    pe_bvsub, BitVec.sub_eq, Prod.map, Term.bitvec, Ext.IPAddr.CIDR.range]

private theorem pe_ipaddr_rangeV4 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} :
  IPAddr.rangeV4 (.prim (.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V4 cidr)))) =
  (Ext.IPAddr.CIDR.range cidr).map Term.bitvec Term.bitvec
:= by
  simp only [IPAddr.rangeV4, pe_ext_ipaddr_addrV4_V4, pe_ext_ipaddr_prefixV4_V4, pe_ipaddr_range]

private theorem pe_ipaddr_rangeV6 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH} :
  IPAddr.rangeV6 (.prim (.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V6 cidr)))) =
  (Ext.IPAddr.CIDR.range cidr).map Term.bitvec Term.bitvec
:= by
  simp only [IPAddr.rangeV6, pe_ext_ipaddr_addrV6_V6, pe_ext_ipaddr_prefixV6_V6, pe_ipaddr_range]

private theorem pe_ipaddr_inRange {w : Nat} {c₁ c₂ : Ext.IPAddr.CIDR w} {rangeV : Term → (Term × Term)} {f : Ext.IPAddr.CIDR w → Ext.IPAddr.IPNet}
  (hpe : ∀ {c}, rangeV (.prim (.ext (Ext.ipaddr (f c)))) = (Ext.IPAddr.CIDR.range c).map Term.bitvec Term.bitvec) :
  IPAddr.inRange rangeV (Term.prim (TermPrim.ext (Ext.ipaddr (f c₁)))) (Term.prim (TermPrim.ext (Ext.ipaddr (f c₂)))) =
  Term.prim (TermPrim.bool (Ext.IPAddr.CIDR.inRange c₁ c₂))
:= by
  simp only [IPAddr.inRange,
    hpe, Prod.map, pe_bvule,
    Ext.IPAddr.CIDR.inRange,
    ge_iff_le, BitVec.bvule_iff_le]
  cases (decide ((Ext.IPAddr.CIDR.range c₁).snd ≤ (Ext.IPAddr.CIDR.range c₂).snd))
  · simp only [pe_and_false_left, Bool.false_and]
  · simp only [pe_and_true_left, Bool.true_and]

private theorem pe_ipaddr_isInRange {ip₁ ip₂ : Ext.IPAddr.IPNet} :
  IPAddr.isInRange (.prim (.ext (Ext.ipaddr ip₁))) (.prim (.ext (Ext.ipaddr ip₂))) =
  ip₁.inRange ip₂
:= by
  simp [IPAddr.isInRange, Ext.IPAddr.IPNet.inRange, IPAddr.inRangeV]
  cases ip₁ <;> cases ip₂ <;>
  simp only [
    pe_ipaddr_isIpv4_V4, pe_ipaddr_isIpv4_V6,
    pe_ipaddr_isIpv6_V4, pe_ipaddr_isIpv6_V6,
    pe_and_false_left, pe_and_false_right, pe_and_true_left,
    pe_or_false_left, pe_or_false_right]
  case V4 => exact pe_ipaddr_inRange pe_ipaddr_rangeV4
  case V6 => exact pe_ipaddr_inRange pe_ipaddr_rangeV6

private theorem pe_ipaddr_isInRangeLit {ip : Ext.IPAddr.IPNet}
  {c₄ : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} {c₆ : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH} :
  IPAddr.inRangeLit (Term.prim (TermPrim.ext (Ext.ipaddr ip))) c₄ c₆ =
  Term.prim (TermPrim.bool (match ip with
    | .V4 cidr => cidr.inRange c₄
    | .V6 cidr => cidr.inRange c₆))
:= by
  simp only [IPAddr.inRangeLit]
  cases ip <;>
  simp only [
    pe_ipaddr_isIpv4_V4, pe_ipaddr_isIpv4_V6,
    pe_ite_true, pe_ite_false]
  case V4 => exact pe_ipaddr_inRange pe_ipaddr_rangeV4
  case V6 => exact pe_ipaddr_inRange pe_ipaddr_rangeV6

private theorem pe_ipaddr_isLoopback {ip : Ext.IPAddr.IPNet} :
  IPAddr.isLoopback (.prim (.ext (Ext.ipaddr ip))) = ip.isLoopback
:= by
  simp only [IPAddr.isLoopback, Ext.IPAddr.IPNet.isLoopback, pe_ipaddr_isInRangeLit]
  cases ip <;> simp only

private theorem pe_ipaddr_isMulticast {ip : Ext.IPAddr.IPNet} :
  IPAddr.isMulticast (.prim (.ext (Ext.ipaddr ip))) = ip.isMulticast
:= by
  simp only [IPAddr.isMulticast, Ext.IPAddr.IPNet.isMulticast, pe_ipaddr_isInRangeLit]
  cases ip <;> simp only

private theorem pe_datetime_offset {dt : Ext.Datetime} {dur : Ext.Datetime.Duration}:
  Datetime.offset (.prim (.ext (Ext.datetime dt))) (.prim (.ext (Ext.duration dur))) =
  match dt.offset dur with
  | none => .none (.prim (.ext .datetime))
  | some dt' => .some (.prim (.ext (Ext.datetime dt')))
:= by
  simp only [Datetime.offset, pe_ext_datetime_val, pe_ext_duration_val, pe_bvadd, pe_bvsaddo,
    Ext.Datetime.offset]
  cases h: dt.val.add? dur.val <;> unfold Int64.add? at h <;> simp
  case none =>
    rw [BitVec.Int64_ofInt?_eq_none_iff_overflows] at h
    simp [BitVec.Int64_toBitVec_toInt_eq_toInt, h, pe_ifFalse_true,
      (wf_ifFalse wf_bool (wf_ext_datetime_ofBitVec wf_bv typeOf_bv).left typeOf_bool).right]
    apply (wf_ext_datetime_ofBitVec wf_bv typeOf_bv).right; exact Map.empty
  case some v =>
    have h' : ∃ v, Int64.ofInt? (dt.val.toInt + dur.val.toInt) = some v := by exact Exists.intro v h
    rw [← Option.isSome_iff_exists, Option.isSome_iff_ne_none, ne_eq, BitVec.Int64_ofInt?_eq_none_iff_overflows] at h'
    simp only [Bool.not_eq_true] at h'
    simp [BitVec.Int64_toBitVec_toInt_eq_toInt, h', pe_ifFalse_false,
      (wf_ifFalse wf_bool (wf_ext_datetime_ofBitVec wf_bv typeOf_bv).left typeOf_bool).right]
    simp only [Int64.ofInt?, Option.dite_none_right_eq_some, Option.some.injEq, Int64.ofIntChecked] at h
    cases h; rename_i h heq
    subst heq
    simp only [Int64.ofInt, BitVec.ofInt_add, Int64.toInt, ext.datetime.ofBitVec, BitVec.toInt_ofInt_64]

private theorem pe_datetime_durationSince {dt₁ dt₂ : Ext.Datetime}:
  Datetime.durationSince (.prim (.ext (Ext.datetime dt₁))) (.prim (.ext (Ext.datetime dt₂))) =
  match dt₁.durationSince dt₂ with
  | none => .none (.prim (.ext .duration))
  | some dur => .some (.prim (.ext (Ext.duration dur)))
:= by
  simp only [Datetime.durationSince, pe_ext_datetime_val, pe_bvsub, pe_bvssubo, Ext.Datetime.durationSince]
  cases h: dt₁.val.sub? dt₂.val <;> unfold Int64.sub? at h <;> simp
  case none =>
    rw [BitVec.Int64_ofInt?_eq_none_iff_overflows] at h
    simp [BitVec.Int64_toBitVec_toInt_eq_toInt, h, pe_ifFalse_true,
      (wf_ifFalse wf_bool (wf_ext_duration_ofBitVec wf_bv typeOf_bv).left typeOf_bool).right]
    apply (wf_ext_duration_ofBitVec wf_bv typeOf_bv).right; exact Map.empty
  case some v =>
    have h' : ∃ v, Int64.ofInt? (dt₁.val.toInt - dt₂.val.toInt) = some v := by exact Exists.intro v h
    rw [← Option.isSome_iff_exists, Option.isSome_iff_ne_none, ne_eq, BitVec.Int64_ofInt?_eq_none_iff_overflows] at h'
    simp only [Bool.not_eq_true] at h'
    simp [BitVec.Int64_toBitVec_toInt_eq_toInt, h', pe_ifFalse_false,
      (wf_ifFalse wf_bool (wf_ext_datetime_ofBitVec wf_bv typeOf_bv).left typeOf_bool).right]
    simp only [Int64.ofInt?, Option.dite_none_right_eq_some, Option.some.injEq, Int64.ofIntChecked] at h
    cases h; rename_i h heq
    subst heq
    simp only [ext.duration.ofBitVec, Int64.ofInt, BitVec.toInt_sub, Nat.reducePow, Int64.toInt,
      Term.prim.injEq, TermPrim.ext.injEq, Ext.duration.injEq, Ext.Datetime.Duration.mk.injEq]
    have hbmod := @Int.bmod_bounded_eq_self 63 _ h.left h.right
    simp only [Int64.toInt] at hbmod
    rw [hbmod]

private theorem pe_datetime_toDate_sDiv_ms_sub_1 (dt : Ext.Datetime) :
  (dt.val.toUInt64.toBitVec.sdiv 86400000#64).toInt - Int.ofNat 1 =
  ((dt.val.toUInt64.toBitVec.sdiv 86400000#64).sub 1#64).toInt
:= by
  simp only [Int.ofNat_eq_coe, BitVec.sub_eq, BitVec.toInt_sub,
    BitVec.reduceToInt, Nat.reducePow]
  symm
  apply @Int.bmod_bounded_eq_self 63
  case hlow =>
    generalize dt.val.toUInt64.toBitVec = bv at *
    apply Int.le_sub_one_of_lt
    apply @BitVec.sdiv_pos_gt_INT64_MIN
    simp only [BitVec.reduceToInt, Int.reduceLT]
  case hhigh =>
    generalize dt.val.toUInt64.toBitVec = bv at *
    apply @Int.le_trans _ (bv.sdiv 86400000#64).toInt
    case h₁ => bv_omega
    case h₂ =>
      apply Int.le_of_lt
      apply BitVec.sdiv_pos_lt_INT64_MAX
      simp only [BitVec.reduceToInt, Int.reduceLT]

private theorem pe_datetime_toDate {dt : Ext.Datetime}:
  Datetime.toDate (.prim (.ext (Ext.datetime dt))) =
  match dt.toDate with
  | none => .none (.prim (.ext .datetime))
  | some dt' => .some (.prim (.ext (Ext.datetime dt')))
:= by
  simp only [Datetime.toDate, someOf, pe_ext_datetime_val, pe_bvsdiv, pe_bvsub, pe_bvmul, pe_bvsmulo,
    pe_bvsrem, pe_bvsle, pe_ext_datetime_ofBitVec,
    Ext.Datetime.toDate, Ext.Datetime.MILLISECONDS_PER_DAY, Int64.ofIntChecked,
    Int64.ofInt, pe_eq_lit term_prim_is_lit term_prim_is_lit, Int64.mod, Int64.div ]
  simp only [
    show Int64.toBitVec 0 = 0 by rfl,
    show Int64.toBitVec 1 = 1 by rfl,
    show Int64.toBitVec 86400000 = 86400000 by rfl ]
  cases h₀ : BitVec.sle 0 dt.val.toBitVec
  case false =>
    simp only [h₀, pe_ite_false]
    have h₁ : ¬dt.val ≥ 0 := by
      simp only [ge_iff_le, LE.le, Int64.le, BitVec.ofNat_eq_ofNat, Bool.not_eq_true]
      exact h₀
    simp only [h₁, ↓reduceIte]
    cases h₂ : Term.prim (TermPrim.bitvec (dt.val.toBitVec.srem 86400000)) == Term.prim (TermPrim.bitvec 0)
    case false =>
      simp only [pe_ite_false, beq_eq_false_iff_ne, ne_eq, Term.prim.injEq,
        TermPrim.bitvec.injEq, heq_eq_eq, true_and, Int64.toBitVec] at h₂
      simp only [BitVec.ofInt_ofNat, BitVec.ofInt_toInt]
      simp only [Int64.toBitVec, BEq.beq, decide_eq_true_eq, OfNat.ofNat, Int64.ofNat]
      replace h₂ : ¬dt.val.toUInt64.toBitVec.srem 86400000#64 = 0#64 := by exact h₂
      rw [BitVec.eq_iff_UInt64_toInt64_eq_64, UInt64.toInt64, UInt64.toInt64] at h₂
      simp only [h₂, ↓reduceIte, pe_ite_false, Ext.Datetime.datetime?]
      simp only [Int64.toInt, Int64.toBitVec]
      have h₃ := pe_datetime_toDate_sDiv_ms_sub_1 dt
      cases h₄ : BitVec.overflows 64 (((dt.val.toUInt64.toBitVec.smtSDiv 86400000#64).sub 1#64).toInt * (86400000#64).toInt)
      case false =>
        clear h₀ h₁ h₂
        simp only [pe_ifFalse_false]
        simp only [Bool.eq_false_iff, ne_eq, ← BitVec.Int64_ofInt?_eq_none_iff_overflows, Int64.ofInt?] at h₄
        simp only [dite_eq_right_iff, reduceCtorEq, imp_false, not_and, not_imp, Decidable.not_not] at h₄
        replace ⟨h₄, h₅⟩ := h₄
        simp only [@BitVec.smtSDiv_eq_sdiv _ _ 86400000#64 (by simp only [BitVec.ofNat_eq_ofNat, ne_eq, BitVec.reduceEq, not_false_eq_true])] at *
        simp only [h₃, Int64.ofInt?, h₄, h₅]
        simp only [and_self, ↓reduceDIte, BitVec.toInt_sub,
          BitVec.reduceToInt, Nat.reducePow, Option.pure_def, Option.bind_some_fun, Term.some.injEq,
          Term.prim.injEq, TermPrim.ext.injEq, Ext.datetime.injEq, Ext.Datetime.mk.injEq]
        simp only [Int64.ofIntChecked, Int64.ofInt]
        apply congr_arg ; apply congr_arg
        have h₆ : (86400000 : Int) = (86400000#64).toInt := by
          simp only [BitVec.toInt, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
            Nat.reduceMul, Nat.reduceLT, ↓reduceIte, Int.cast_ofNat_Int]
        simp only [h₆, ← BitVec.mul_toInt_eq_toInt_mul (And.intro h₄ h₅), BitVec.ofInt_toInt]
        simp only [BitVec.sub_eq, BitVec.mul_eq]
      case true =>
        simp only [← BitVec.Int64_ofInt?_eq_none_iff_overflows] at h₄
        simp only [@BitVec.smtSDiv_eq_sdiv _ _ 86400000#64 (by simp only [BitVec.ofNat_eq_ofNat, ne_eq, BitVec.reduceEq, not_false_eq_true])] at *
        simp only [pe_ifFalse_true, Term.typeOf, TermPrim.typeOf, h₃, h₄]
        simp only [Option.pure_def, Option.bind_none_fun]
    case true =>
      simp only [pe_ite_true, Int64.toBitVec]
      simp only [BitVec.ofNat_eq_ofNat, beq_iff_eq, Term.prim.injEq, TermPrim.bitvec.injEq, heq_eq_eq, true_and] at h₂
      simp only [Int64.toInt, Int64.toBitVec] at *
      simp only [show  BitVec.ofInt 64 86400000 = 86400000#64 by rfl, h₂]
      have h₃ : 0 = UInt64.toInt64 { toBitVec := 0#64 } := by
        simp only [UInt64.toInt64, UInt64.ofBitVec_ofNat, OfNat.ofNat, Int64.ofNat, UInt64.ofBitVec_ofNat, UInt64.reduceOfNat]
      simp only [UInt64.ofBitVec_ofNat, h₃, UInt64.toInt64, beq_self_eq_true, ↓reduceIte]
  case true =>
    have h₁ : dt.val ≥ 0 := by
      simp only [ge_iff_le, LE.le, Int64.le, BitVec.ofNat_eq_ofNat, Bool.not_eq_true]
      exact h₀
    simp only [h₁, ↓reduceIte, pe_ite_true]; clear h₀ h₁
    simp only [Int64.toInt, Int64.toBitVec]
    simp only [show 86400000 = 86400000#64 by rfl]
    simp only [@BitVec.smtSDiv_eq_sdiv _ _ 86400000#64 (by simp only [BitVec.ofNat_eq_ofNat, ne_eq, BitVec.reduceEq, not_false_eq_true])]
    have h₀ : (BitVec.ofInt 64 86400000).toInt = (86400000#64).toInt := by
      simp only [BitVec.toInt, BitVec.ofInt_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
        Nat.reduceMul, Nat.reduceLT, ↓reduceIte]
    have h₁ : (BitVec.ofInt 64 86400000) = 86400000#64 := by simp only [BitVec.ofInt_ofNat]
    simp only [h₀, h₁] ; clear h₀ h₁
    rw [@BitVec.mul_toInt_sdiv_eq_toInt_mul_sdiv _ 86400000#64 (by simp only [BitVec.reduceToInt, Int.reduceLT])]
    simp only [Ext.Datetime.datetime?, Int64.ofInt?, BitVec.toInt_ge_INT64_MIN, BitVec.toInt_le_INT64_MAX]
    simp only [BitVec.mul_eq, BitVec.toInt_mul, BitVec.reduceToInt, Nat.reducePow, and_self,
      ↓reduceDIte, Int64.ofIntChecked, Option.pure_def, Option.bind_some_fun, Term.some.injEq,
      Term.prim.injEq, TermPrim.ext.injEq, Ext.datetime.injEq, Ext.Datetime.mk.injEq]
    simp only [Int64.ofInt]

private theorem pe_datetime_toTime {dt : Ext.Datetime}:
  Datetime.toTime (.prim (.ext (Ext.datetime dt))) = .prim (.ext (Ext.duration dt.toTime))
:= by
  simp only [Datetime.toTime, pe_ext_datetime_val, pe_bvsrem, pe_bvadd, pe_bvsle,
    pe_eq_lit term_prim_is_lit term_prim_is_lit, Ext.Datetime.toTime]
  simp only [Int64.ofIntChecked, Int64.ofInt, Int64.mod, Ext.Datetime.MILLISECONDS_PER_DAY]
  simp only [
    show Int64.toBitVec 0 = 0#64 by rfl,
    show Int64.toBitVec 86400000 = 86400000#64 by rfl ]
  have h₀ : (UInt64.toInt64 {toBitVec := (BitVec.ofInt 64 86400000)}).toBitVec = 86400000#64 := by
    simp only [BitVec.ofInt_ofNat, UInt64.ofBitVec_ofNat, UInt64.toBitVec_toInt64,
      UInt64.toBitVec_ofNat]
  simp only [UInt64.toInt64] at h₀
  simp only [h₀] ; clear h₀
  cases h₀ : BitVec.sle 0#64 dt.val.toBitVec
  case false =>
    have h₁ : ¬dt.val ≥ 0 := by
      simp only [ge_iff_le, LE.le, Int64.le, BitVec.ofNat_eq_ofNat, Bool.not_eq_true]
      exact h₀
    simp only [pe_ite_false, h₁, ↓reduceIte]; clear h₀ h₁
    have h₁ : UInt64.toInt64 { toBitVec := 0#64 } = 0 := by
        simp only [UInt64.toInt64, UInt64.ofBitVec_ofNat, OfNat.ofNat, Int64.ofNat, UInt64.ofBitVec_ofNat, UInt64.reduceOfNat]
    simp only [UInt64.toInt64] at h₁
    cases h₀ : Term.prim (TermPrim.bitvec (dt.val.toBitVec.srem 86400000#64)) == Term.prim (TermPrim.bitvec 0#64)
    case false =>
      simp only [pe_ite_false]
      simp only [beq_eq_false_iff_ne, ne_eq, Term.prim.injEq, TermPrim.bitvec.injEq, heq_eq_eq, true_and] at h₀
      rw [BitVec.eq_iff_UInt64_toInt64_eq_64, UInt64.toInt64, UInt64.toInt64] at h₀
      simp only [h₁] at h₀
      simp only [beq_iff_eq, h₀, ↓reduceIte, pe_ext_duration_ofBitVec, Term.prim.injEq, TermPrim.ext.injEq, Ext.duration.injEq,
        Ext.Datetime.Duration.mk.injEq]
      simp only [Int64.eq_iff_toBitVec_eq, BitVec.toInt_ofInt64_toBitVec]
      rfl
    case true =>
      simp only [beq_iff_eq, Term.prim.injEq, TermPrim.bitvec.injEq, heq_eq_eq, true_and] at h₀
      rw [BitVec.eq_iff_UInt64_toInt64_eq_64, UInt64.toInt64, UInt64.toInt64] at h₀
      simp only [h₁] at h₀
      simp only [BitVec.add_eq, pe_ite_true, pe_ext_duration_ofBitVec, BitVec.toInt_zero, h₀,
        beq_self_eq_true, ↓reduceIte, Term.prim.injEq, TermPrim.ext.injEq, Ext.duration.injEq,
        Ext.Datetime.Duration.mk.injEq]
      rfl
  case true =>
    have h₁ : dt.val ≥ 0 := by
      simp only [ge_iff_le, LE.le, Int64.le, BitVec.ofNat_eq_ofNat, Bool.not_eq_true]
      exact h₀
    simp only [h₁, ↓reduceIte, pe_ite_true, pe_ext_duration_ofBitVec, Int64.ofInt, BitVec.ofInt_toInt]

private theorem pe_duration_toMilliseconds {dur : Ext.Datetime.Duration} :
  Duration.toMilliseconds (.prim (.ext (Ext.duration dur))) = dur.toMilliseconds
:= by simp only [Duration.toMilliseconds, pe_ext_duration_val] ; rfl

private theorem pe_duration_toSeconds {dur : Ext.Datetime.Duration} :
  Duration.toSeconds (.prim (.ext (Ext.duration dur))) = dur.toSeconds
:= by simp only [Duration.toSeconds, pe_ext_duration_val, pe_bvsdiv] ; rfl

theorem pe_duration_toMinutes {dur : Ext.Datetime.Duration} :
  Duration.toMinutes (.prim (.ext (Ext.duration dur))) = dur.toMinutes
:= by simp only [Duration.toMinutes, pe_ext_duration_val, pe_bvsdiv] ; rfl

private theorem pe_duration_toHours {dur : Ext.Datetime.Duration} :
  Duration.toHours (.prim (.ext (Ext.duration dur))) = dur.toHours
:= by simp only [Duration.toHours, pe_ext_duration_val, pe_bvsdiv] ; rfl

private theorem pe_duration_toDays {dur : Ext.Datetime.Duration} :
  Duration.toDays (.prim (.ext (Ext.duration dur))) = dur.toDays
:= by simp only [Duration.toDays, pe_ext_duration_val, pe_bvsdiv] ; rfl

----- Interpret lemmas for ExtFuns -----

private theorem interpret_decimal_lessThan {I : Interpretation} {t₁ t₂ : Term} :
  (Decimal.lessThan t₁ t₂).interpret I = Decimal.lessThan (t₁.interpret I) (t₂.interpret I)
:= by
  simp only [Decimal.lessThan, interpret_bvslt, interpret_ext_decimal_val]

private theorem interpret_decimal_lessThanOrEqual {I : Interpretation} {t₁ t₂ : Term} :
  (Decimal.lessThanOrEqual t₁ t₂).interpret I = Decimal.lessThanOrEqual (t₁.interpret I) (t₂.interpret I)
:= by
  simp only [Decimal.lessThanOrEqual, interpret_bvsle, interpret_ext_decimal_val]

private theorem interpret_decimal_greaterThan {I : Interpretation} {t₁ t₂ : Term} :
  (Decimal.greaterThan t₁ t₂).interpret I = Decimal.greaterThan (t₁.interpret I) (t₂.interpret I)
:= by
  simp only [Decimal.greaterThan, interpret_decimal_lessThan]

private theorem interpret_decimal_greaterThanOrEqual {I : Interpretation} {t₁ t₂ : Term} :
  (Decimal.greaterThanOrEqual t₁ t₂).interpret I = Decimal.greaterThanOrEqual (t₁.interpret I) (t₂.interpret I)
:= by
  simp only [Decimal.greaterThanOrEqual, interpret_decimal_lessThanOrEqual]

private theorem interpret_ipaddr_isIpv4 {I : Interpretation} {t : Term} :
  (IPAddr.isIpv4 t).interpret I = IPAddr.isIpv4 (t.interpret I)
:= by
  simp only [IPAddr.isIpv4, interpret_ext_ipaddr_isV4]

private theorem interpret_ipaddr_isIpv6 {εs : SymEntities} {I : Interpretation} {t : Term}
  (hI : I.WellFormed εs)
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  (IPAddr.isIpv6 t).interpret I = IPAddr.isIpv6 (t.interpret I)
:= by
  simp only [IPAddr.isIpv6, interpret_not hI (wf_ext_ipaddr_isV4 h₁.left h₁.right).left,
    interpret_ext_ipaddr_isV4]

private theorem interpret_ipaddr_subnetWidth {εs : SymEntities} {I : Interpretation} {w : Nat} {ipPre : Term}
  (hI : I.WellFormed εs)
  (h₁ : ipPre.WellFormed εs ∧ ipPre.typeOf = .option (.bitvec w)) :
  (IPAddr.subnetWidth w ipPre).interpret I = IPAddr.subnetWidth w (ipPre.interpret I)
:= by
  simp only [IPAddr.subnetWidth]
  generalize hw : (Ext.IPAddr.ADDR_SIZE w) = n
  simp only [Ext.IPAddr.ADDR_SIZE] at hw
  have h₂ := wf_isNone h₁.left
  have h₃ := wf_option_get h₁.left h₁.right
  have h₄ := @wf_zero_extend εs (option.get ipPre) (n - w) w h₃.left h₃.right
  have h₅ : n - w + w = n := by
    subst hw
    have := @Nat.lt_two_pow_self w
    omega
  simp only [h₅] at h₄
  have h₆ := @wf_bvsub εs
    (Term.prim (TermPrim.bitvec (BitVec.ofNat n n)))
    (zero_extend (n - w) (option.get ipPre))
    n wf_bv h₄.left (by simp only [typeOf_bv]) h₄.right
  rw [interpret_ite hI h₂.left wf_bv h₆.left h₂.right (by simp only [typeOf_bv, h₆.right]),
    interpret_isNone hI h₁.left,
    interpret_term_prim, interpret_bvsub, interpret_term_prim,
    interpret_zero_extend hI h₃.left]
  have hlit := interpret_term_wfl hI h₁.left
  rw [h₁.right] at hlit
  replace hlit := wfl_of_type_option_is_option hlit.left hlit.right
  rcases hlit with hlit | ⟨_, hlit⟩ <;>
  simp only [hlit, pe_isNone_none, pe_ite_true]
  simp only [pe_isNone_some, pe_ite_false, pe_option_get_some,
    interpret_option_get I h₁.left h₁.right, hlit, pe_option_get'_some]

private theorem interpret_ipaddr_range {εs : SymEntities} {I : Interpretation} {w : Nat} {ipAddr ipPre : Term}
  (hI : I.WellFormed εs)
  (h₁ : ipPre.WellFormed εs ∧ ipPre.typeOf = .option (.bitvec w)) :
  (IPAddr.range w ipAddr ipPre).map (Term.interpret I) (Term.interpret I) =
  IPAddr.range w (ipAddr.interpret I) (ipPre.interpret I)
:= by
  simp only [
    IPAddr.range, Prod.map, interpret_bvshl, interpret_bvlshr,
    interpret_bvsub, interpret_bvadd, interpret_term_prim,
    interpret_ipaddr_subnetWidth hI h₁]

private theorem interpret_ipaddr_rangeV4 {εs : SymEntities} {I : Interpretation} {t : Term}
  (hI : I.WellFormed εs)
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr)
  (h₂ : (IPAddr.isIpv4 (t.interpret I)) = true) :
  (IPAddr.rangeV4 t).map (Term.interpret I) (Term.interpret I) = IPAddr.rangeV4 (t.interpret I)
:= by
  have hwp := wf_ext_ipaddr_prefixV4 h₁.left h₁.right
  simp only [IPAddr.rangeV4, interpret_ipaddr_range hI hwp,
    interpret_ext_ipaddr_addrV4, interpret_ext_ipaddr_prefixV4]
  have hlit := interpret_term_wfl hI h₁.left
  rw [h₁.right] at hlit
  replace ⟨ip, hlit⟩ := wfl_of_type_ext_ipaddr_is_ext_ipaddr hlit.left hlit.right
  simp only [hlit] at *
  cases ip
  · simp only [pe_ext_ipaddr_addrV4'_V4, pe_ext_ipaddr_prefixV4'_V4]
  · simp only [pe_ipaddr_isIpv4_V6, Term.prim.injEq, TermPrim.bool.injEq, reduceCtorEq] at h₂

private theorem interpret_ipaddr_rangeV6 {εs : SymEntities} {I : Interpretation} {t : Term}
  (hI : I.WellFormed εs)
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr)
  (h₂ : (IPAddr.isIpv6 (t.interpret I)) = true) :
  (IPAddr.rangeV6 t).map (Term.interpret I) (Term.interpret I) = IPAddr.rangeV6 (t.interpret I)
:= by
  have hwp := wf_ext_ipaddr_prefixV6 h₁.left h₁.right
  simp only [IPAddr.rangeV6, interpret_ipaddr_range hI hwp,
    interpret_ext_ipaddr_addrV6, interpret_ext_ipaddr_prefixV6]
  have hlit := interpret_term_wfl hI h₁.left
  rw [h₁.right] at hlit
  replace ⟨ip, hlit⟩ := wfl_of_type_ext_ipaddr_is_ext_ipaddr hlit.left hlit.right
  simp only [hlit] at *
  cases ip
  · simp only [pe_ipaddr_isIpv6_V4, Term.prim.injEq, TermPrim.bool.injEq, reduceCtorEq] at h₂
  · simp only [pe_ext_ipaddr_addrV6'_V6, pe_ext_ipaddr_prefixV6'_V6]

private theorem interpret_ipaddr_inRange {εs : SymEntities} {I : Interpretation} {w : Nat} {rangeV : Term → Term × Term} {t₁ t₂ : Term}
  (hI : I.WellFormed εs)
  (h₁ : WFIPRange εs (rangeV t₁) w)
  (h₂ : WFIPRange εs (rangeV t₂) w)
  (h₃ : (rangeV t₁).map (Term.interpret I) (Term.interpret I) = rangeV (t₁.interpret I))
  (h₄ : (rangeV t₂).map (Term.interpret I) (Term.interpret I) = rangeV (t₂.interpret I)) :
  (IPAddr.inRange rangeV t₁ t₂).interpret I =
  IPAddr.inRange rangeV (t₁.interpret I) (t₂.interpret I)
:= by
  simp only [IPAddr.inRange]
  simp only [WFIPRange, WFArg] at h₁ h₂
  simp only [Prod.map] at h₃ h₄
  have h₅ := wf_bvule h₁.right.left h₂.right.left h₁.right.right h₂.right.right
  have h₆ := wf_bvule h₂.left.left h₁.left.left h₂.left.right h₁.left.right
  simp only [interpret_and hI h₅.left h₆.left h₅.right h₆.right, interpret_bvule, ← h₃, ←h₄]

private theorem interpret_ipaddr_inRangeV {εs : SymEntities} {I : Interpretation} {w : Nat} {isIp : Term → Term} {rangeV : Term → Term × Term} {t₁ t₂ : Term}
  (hI : I.WellFormed εs)
  (hr₁ : WFIPRange εs (rangeV t₁) w)
  (hr₂ : WFIPRange εs (rangeV t₂) w)
  (hw₁ : (isIp t₁).WellFormed εs ∧ (isIp t₁).typeOf = .bool)
  (hw₂ : (isIp t₂).WellFormed εs ∧ (isIp t₂).typeOf = .bool)
  (hi₁ : (isIp t₁).interpret I = isIp (t₁.interpret I))
  (hi₂ : (isIp t₂).interpret I = isIp (t₂.interpret I))
  (hi₃ : isIp (t₁.interpret I) = true → (rangeV t₁).map (Term.interpret I) (Term.interpret I) = rangeV (t₁.interpret I))
  (hi₄ : isIp (t₂.interpret I) = true → (rangeV t₂).map (Term.interpret I) (Term.interpret I) = rangeV (t₂.interpret I)) :
  (IPAddr.inRangeV isIp rangeV t₁ t₂).interpret I =
  IPAddr.inRangeV isIp rangeV (t₁.interpret I) (t₂.interpret I)
:= by
  have hw₃ := wf_and hw₁.left hw₂.left hw₁.right hw₂.right
  have hw₄ := wf_ipaddr_inRange hr₁ hr₂
  simp only [IPAddr.inRangeV]
  rw [
    interpret_and hI hw₃.left hw₄.left hw₃.right hw₄.right,
    interpret_and hI hw₁.left hw₂.left hw₁.right hw₂.right,
    hi₁, hi₂]
  have hlit₁ := interpret_term_wfl hI hw₁.left
  have hlit₂ := interpret_term_wfl hI hw₂.left
  rw [hw₁.right] at hlit₁
  rw [hw₂.right] at hlit₂
  replace ⟨b₁, hlit₁⟩ := wfl_of_type_bool_is_bool hlit₁.left hlit₁.right
  replace ⟨b₂, hlit₂⟩ := wfl_of_type_bool_is_bool hlit₂.left hlit₂.right
  simp only [hi₁, hi₂] at hlit₁ hlit₂
  cases b₁ <;> cases b₂ <;>
  simp only [hlit₁, hlit₂, pe_and_false_right, pe_and_false_left, pe_and_true_left]
  exact interpret_ipaddr_inRange hI hr₁ hr₂ (hi₃ hlit₁) (hi₄ hlit₂)

private theorem interpret_ipaddr_isInRange {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term}
  (hI: I.WellFormed εs)
  (h₁ : t₁.WellFormed εs ∧ t₁.typeOf = .ext .ipAddr)
  (h₂ : t₂.WellFormed εs ∧ t₂.typeOf = .ext .ipAddr) :
  (IPAddr.isInRange t₁ t₂).interpret I = IPAddr.isInRange (t₁.interpret I) (t₂.interpret I)
:= by
  have h₃ := wf_ipaddr_inRangeV (wf_ipaddr_rangeV4 h₁) (wf_ipaddr_rangeV4 h₂) (wf_ipaddr_isIpv4 h₁) (wf_ipaddr_isIpv4 h₂)
  have h₄ := wf_ipaddr_inRangeV (wf_ipaddr_rangeV6 h₁) (wf_ipaddr_rangeV6 h₂) (wf_ipaddr_isIpv6 h₁) (wf_ipaddr_isIpv6 h₂)
  simp only [
    IPAddr.isInRange,
    interpret_or hI h₃.left h₄.left h₃.right h₄.right,
    interpret_ipaddr_inRangeV hI
      (wf_ipaddr_rangeV4 h₁) (wf_ipaddr_rangeV4 h₂)
      (wf_ipaddr_isIpv4 h₁) (wf_ipaddr_isIpv4 h₂)
      interpret_ipaddr_isIpv4 interpret_ipaddr_isIpv4
      (interpret_ipaddr_rangeV4 hI h₁) (interpret_ipaddr_rangeV4 hI h₂),
    interpret_ipaddr_inRangeV hI
      (wf_ipaddr_rangeV6 h₁) (wf_ipaddr_rangeV6 h₂)
      (wf_ipaddr_isIpv6 h₁) (wf_ipaddr_isIpv6 h₂)
      (interpret_ipaddr_isIpv6 hI h₁) (interpret_ipaddr_isIpv6 hI h₂)
      (interpret_ipaddr_rangeV6 hI h₁) (interpret_ipaddr_rangeV6 hI h₂)]

private theorem interpret_ipaddr_inRangeLit {εs : SymEntities} {I : Interpretation} {t : Term}
  {cidr₄ : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} {cidr₆ : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH}
  (hI : I.WellFormed εs)
  (h₁ : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  (IPAddr.inRangeLit t cidr₄ cidr₆).interpret I = IPAddr.inRangeLit (t.interpret I) cidr₄ cidr₆
:= by
  have h₂ := (wf_ipaddr_isIpv4 h₁)
  have h₃ := wf_ipaddr_inRange (wf_ipaddr_rangeV4 h₁) (wf_ipaddr_rangeV4 (wf_ipaddr_ipTerm εs (Ext.IPAddr.IPNet.V4 cidr₄)))
  have h₄ := wf_ipaddr_inRange (wf_ipaddr_rangeV6 h₁) (wf_ipaddr_rangeV6 (wf_ipaddr_ipTerm εs (Ext.IPAddr.IPNet.V6 cidr₆)))
  simp only [IPAddr.inRangeLit,
    interpret_ite hI h₂.left h₃.left h₄.left h₂.right (by simp only [h₃, h₄]),
    interpret_ipaddr_isIpv4]
  have hlit := interpret_term_wfl hI h₁.left
  rw [h₁.right] at hlit
  replace ⟨ip, hlit⟩ := wfl_of_type_ext_ipaddr_is_ext_ipaddr hlit.left hlit.right
  cases ip
  case V4 =>
    simp only [hlit, pe_ipaddr_isIpv4_V4, pe_ite_true, IPAddr.ipTerm]
    rw [← hlit]
    rw (config := {occs := .pos [2]}) [← @interpret_term_prim I]
    apply interpret_ipaddr_inRange hI
      (wf_ipaddr_rangeV4 h₁)
      (wf_ipaddr_rangeV4 (wf_ipaddr_ipTerm εs (Ext.IPAddr.IPNet.V4 cidr₄)))
    · apply interpret_ipaddr_rangeV4 hI h₁
      simp only [hlit, pe_ipaddr_isIpv4_V4]
    · apply interpret_ipaddr_rangeV4 hI (wf_ipaddr_ipTerm εs (Ext.IPAddr.IPNet.V4 cidr₄))
      simp only [IPAddr.ipTerm, interpret_term_prim, pe_ipaddr_isIpv4_V4]
  case V6 =>
    simp only [hlit, pe_ipaddr_isIpv4_V6, pe_ite_false, IPAddr.ipTerm]
    rw [← hlit]
    rw (config := {occs := .pos [2]}) [← @interpret_term_prim I]
    apply interpret_ipaddr_inRange hI
      (wf_ipaddr_rangeV6 h₁)
      (wf_ipaddr_rangeV6 (wf_ipaddr_ipTerm εs (Ext.IPAddr.IPNet.V6 cidr₆)))
    · apply interpret_ipaddr_rangeV6 hI h₁
      simp only [hlit, pe_ipaddr_isIpv6_V6]
    · apply interpret_ipaddr_rangeV6 hI (wf_ipaddr_ipTerm εs (Ext.IPAddr.IPNet.V6 cidr₆))
      simp only [IPAddr.ipTerm, interpret_term_prim, pe_ipaddr_isIpv6_V6]

private theorem interpret_ipaddr_isLoopback {εs : SymEntities} {I : Interpretation} {t : Term}
  (hI : I.WellFormed εs)
  (hw : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  (IPAddr.isLoopback t).interpret I = IPAddr.isLoopback (t.interpret I)
:= by
  simp only [IPAddr.isLoopback, interpret_ipaddr_inRangeLit hI hw]

private theorem interpret_ipaddr_isMulticast {εs : SymEntities} {I : Interpretation} {t : Term}
  (hI : I.WellFormed εs)
  (hw : t.WellFormed εs ∧ t.typeOf = .ext .ipAddr) :
  (IPAddr.isMulticast t).interpret I = IPAddr.isMulticast (t.interpret I)
:= by
  simp only [IPAddr.isMulticast, interpret_ipaddr_inRangeLit hI hw]

private theorem interpret_datetime_offset {I : Interpretation} {t₁ t₂ : Term}
  (hI : I.WellFormed εs)
  (hw₁ : t₁.WellFormed εs ∧ t₁.typeOf = .ext .datetime)
  (hw₂ : t₂.WellFormed εs ∧ t₂.typeOf = .ext .duration) :
  (Datetime.offset t₁ t₂).interpret I = Datetime.offset (t₁.interpret I) (t₂.interpret I)
:= by
  replace hw₁ := wf_ext_datetime_val hw₁.left hw₁.right
  replace hw₂ := wf_ext_duration_val hw₂.left hw₂.right
  have ⟨hwfg, htyg⟩ := wf_bvsaddo hw₁.left hw₂.left hw₁.right hw₂.right
  have ⟨hwft, htyt⟩ := wf_bvadd hw₁.left hw₂.left hw₁.right hw₂.right
  replace ⟨hwft, htyt⟩ := wf_ext_datetime_ofBitVec hwft htyt
  simp only [Datetime.offset, interpret_ifFalse hI hwfg htyg hwft,
    interpret_ext_datetime_ofBitVec, interpret_bvadd, interpret_bvsaddo,
    interpret_ext_datetime_val, interpret_ext_duration_val]

private theorem interpret_datetime_durationSince {I : Interpretation} {t₁ t₂ : Term}
  (hI : I.WellFormed εs)
  (hw₁ : t₁.WellFormed εs ∧ t₁.typeOf = .ext .datetime)
  (hw₂ : t₂.WellFormed εs ∧ t₂.typeOf = .ext .datetime) :
  (Datetime.durationSince t₁ t₂).interpret I = Datetime.durationSince (t₁.interpret I) (t₂.interpret I)
:= by
  replace hw₁ := wf_ext_datetime_val hw₁.left hw₁.right
  replace hw₂ := wf_ext_datetime_val hw₂.left hw₂.right
  have ⟨hwfg, htyg⟩ := wf_bvssubo hw₁.left hw₂.left hw₁.right hw₂.right
  have ⟨hwft, htyt⟩ := wf_bvsub hw₁.left hw₂.left hw₁.right hw₂.right
  replace ⟨hwft, htyt⟩ := wf_ext_duration_ofBitVec hwft htyt
  simp only [Datetime.durationSince, interpret_ifFalse hI hwfg htyg hwft,
    interpret_ext_duration_ofBitVec, interpret_bvsub, interpret_bvssubo,
    interpret_ext_datetime_val]

private theorem interpret_datetime_toDate {εs : SymEntities} {I : Interpretation} {t : Term}
  (hI : I.WellFormed εs)
  (hw : t.WellFormed εs ∧ t.typeOf = .ext .datetime) :
  (Datetime.toDate t).interpret I = Datetime.toDate (t.interpret I)
:= by
  have ⟨hwf₀, hty₀⟩ := wf_ext_datetime_val hw.left hw.right
  have hwf_bv_zero := @wf_bv εs _ (Int64.toBitVec 0)
  have hwf_bv_ms_per_day := @wf_bv εs _ (Int64.toBitVec 86400000)
  have ⟨hwf₁, hty₁⟩   := wf_bvsle hwf_bv_zero hwf₀ typeOf_bv hty₀
  have ⟨hwf₂, hty₂⟩   := wf_bvsdiv hwf₀ hwf_bv_ms_per_day hty₀ typeOf_bv
  have ⟨hwf₃, hty₃⟩   := wf_bvmul hwf_bv_ms_per_day hwf₂ typeOf_bv hty₂
  have ⟨hwf₄, hty₄⟩   := wf_ext_datetime_ofBitVec hwf₃ hty₃
  have ⟨hwf₅, hty₅⟩   := wf_term_some hwf₄ hty₄
  have ⟨hwf₆, hty₆⟩   := wf_bvsrem hwf₀ hwf_bv_ms_per_day hty₀ typeOf_bv
  have ⟨hwf₇, hty₇⟩   := wf_eq hwf₆ hwf_bv_zero (by simp only [hty₆, typeOf_bv])
  have ⟨hwf₈, hty₈⟩   := wf_term_some hw.left hw.right
  have ⟨hwf₉, hty₉⟩   := wf_bvsub hwf₂ (@wf_bv εs _ (Int64.toBitVec 1)) hty₂ typeOf_bv
  have ⟨hwf₁₀, hty₁₀⟩ := wf_bvsmulo hwf₉ hwf_bv_ms_per_day hty₉ typeOf_bv
  have ⟨hwf₁₁, hty₁₁⟩ := wf_bvmul hwf₉ hwf_bv_ms_per_day hty₉ typeOf_bv
  have ⟨hwf₁₂, hty₁₂⟩ := wf_ext_datetime_ofBitVec hwf₁₁ hty₁₁
  have ⟨hwf₁₃, hty₁₃⟩ := wf_ifFalse hwf₁₀ hwf₁₂ hty₁₀
  have ⟨hwf₁₄, hty₁₄⟩ := wf_ite hwf₇ hwf₈ hwf₁₃ hty₇ (by simp only [hty₈, hty₁₃, hty₁₂])
  simp only [Datetime.toDate, someOf,
    interpret_ite hI hwf₁ hwf₅ hwf₁₄ hty₁ (by simp only [hty₅, hty₁₄, hty₈]),
    interpret_ite hI hwf₇ hwf₈ hwf₁₃ hty₇ (by simp only [hty₈, hty₁₃, hty₁₂]),
    interpret_eq hI hwf₆ hwf_bv_zero, interpret_term_some,
    interpret_ifFalse hI hwf₁₀ hty₁₀ hwf₁₂, interpret_ext_datetime_ofBitVec,
    interpret_bvsle, interpret_bvsmulo, interpret_bvmul, interpret_bvsrem,
    interpret_bvsub, interpret_bvsdiv, interpret_term_prim, interpret_ext_datetime_val
  ]

private theorem interpret_datetime_toTime {εs : SymEntities} {I : Interpretation} {t : Term}
  (hI : I.WellFormed εs)
  (hw : t.WellFormed εs ∧ t.typeOf = .ext .datetime) :
  (Datetime.toTime t).interpret I = Datetime.toTime (t.interpret I)
:= by
  have ⟨hwf₀, hty₀⟩ := wf_ext_datetime_val hw.left hw.right
  have hwf_bv_zero := @wf_bv εs _ (Int64.toBitVec 0)
  have hwf_bv_ms_per_day := @wf_bv εs _ (Int64.toBitVec 86400000)
  have ⟨hwf₁, hty₁⟩ := wf_bvsle hwf_bv_zero hwf₀ typeOf_bv hty₀
  have ⟨hwf₂, hty₂⟩ := wf_bvsrem hwf₀ hwf_bv_ms_per_day hty₀ typeOf_bv
  have ⟨hwf₃, hty₃⟩ := wf_eq hwf₂ hwf_bv_zero (by simp only [hty₂, typeOf_bv])
  have ⟨hwf₄, hty₄⟩ := wf_bvadd hwf₂ hwf_bv_ms_per_day hty₂ typeOf_bv
  have ⟨hwf₅, hty₅⟩ := wf_ite hwf₃ hwf_bv_zero hwf₄ hty₃ (by simp only [typeOf_bv, hty₄])
  simp only [Datetime.toTime, interpret_ext_duration_ofBitVec,
    interpret_ite hI hwf₁ hwf₂ hwf₅ hty₁ (by simp only [hty₂, hty₅, typeOf_bv]),
    interpret_ite hI hwf₃ hwf_bv_zero hwf₄ hty₃ (by simp only [typeOf_bv, hty₄]),
    interpret_eq hI hwf₂ hwf_bv_zero, interpret_bvsle, interpret_bvadd,
    interpret_bvsrem, interpret_term_prim, interpret_ext_datetime_val
  ]

private theorem interpret_duration_toMilliseconds {I : Interpretation} {t : Term} :
  (Duration.toMilliseconds t).interpret I = Duration.toMilliseconds (t.interpret I)
:= by
  simp only [Duration.toMilliseconds, interpret_ext_duration_val]

private theorem interpret_duration_toSeconds {I : Interpretation} {t : Term} :
  (Duration.toSeconds t).interpret I = Duration.toSeconds (t.interpret I)
:= by
  simp only [Duration.toSeconds, interpret_bvsdiv, interpret_duration_toMilliseconds, interpret_term_prim]

private theorem interpret_duration_toMinutes {I : Interpretation} {t : Term} :
  (Duration.toMinutes t).interpret I = Duration.toMinutes (t.interpret I)
:= by
  simp only [Duration.toMinutes, interpret_bvsdiv, interpret_duration_toSeconds, interpret_term_prim]

private theorem interpret_duration_toHours {I : Interpretation} {t : Term} :
  (Duration.toHours t).interpret I = Duration.toHours (t.interpret I)
:= by
  simp only [Duration.toHours, interpret_bvsdiv, interpret_duration_toMinutes, interpret_term_prim]

private theorem interpret_duration_toDays {I : Interpretation} {t : Term} :
  (Duration.toDays t).interpret I = Duration.toDays (t.interpret I)
:= by
  simp only [Duration.toDays, interpret_bvsdiv, interpret_duration_toHours, interpret_term_prim]

----- compile_interpret tactics and lemmas for ExtFuns -----

local macro "simp_compileCall₀_interpret" hok:ident compile_call_thm:ident : tactic => do
 `(tactic| (
    replace ⟨_, _, hts, hv, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    simp only [compileCall, List.map_cons, interpret_term_some, interpret_term_prim, List.map_nil,
    compileCall₀, hv, someOf, Coe.coe]
  ))

local macro "simp_compileCall₁_interpret"
  I:ident hI:ident hwφ:ident hok:ident
  xfn:ident compile_call_thm:ident
  wf_thm:ident interpret_thm:ident : tactic => do
 `(tactic| (
    replace ⟨t₁, hts, hty, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace $hwφ := wf_arg' $hwφ
    have hwφ' := interpret_term_wfl $hI $hwφ
    rw [hty] at hwφ'
    have h₃ := $wf_thm (wf_option_get $hwφ hty)
    have h₄ := Term.WellFormed.some_wf h₃.left
    simp only [compileCall, compileCall₁, compileCallWithError₁, hwφ'.right, someOf,
      List.map_cons, List.map_nil, ↓reduceIte, Except.ok.injEq]
    first
    | simp only [interpret_ifSome $hI $hwφ h₄, interpret_term_some]
    | simp only [interpret_ifSome $hI $hwφ h₃.left]
    first
      | simp only [$interpret_thm:ident]
      | simp only [$interpret_thm:ident $hI (wf_option_get $hwφ hty)]
    simp only [interpret_option_get $I $hwφ hty]
    first
    | apply pe_ifSome_get_eq_get' $I (λ t' => Term.some ($xfn t'))
        hwφ'.left hwφ'.right typeOf_term_some
    | apply pe_ifSome_get_eq_get' $I (λ t' => $xfn t') hwφ'.left hwφ'.right
        ($wf_thm (wf_option_get (interpret_term_wf $hI $hwφ).left
          (by simp only [(interpret_term_wf $hI $hwφ).right, hty]))).right
    simp only [typeOf_term_some,
      $wf_thm:ident (wf_option_get' $hI hwφ'.left.left hwφ'.right),
      $wf_thm:ident (wf_option_get hwφ'.left.left hwφ'.right)]
  ))

local macro "simp_compileCall₂_interpret"
  I:ident hI:ident hwφ:ident hok:ident
  xfn:ident compile_call_thm:ident
  wf_thm:ident interpret_thm:ident  : tactic => do
 `(tactic| (
    replace ⟨t₁, t₂, hts, hty₁, hty₂, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace $hwφ := wf_args' $hwφ
    have hwφ₁' := interpret_term_wfl $hI ($hwφ).left
    have hwφ₂' := interpret_term_wfl $hI ($hwφ).right
    simp only [hty₁, hty₂] at hwφ₁' hwφ₂'
    simp only [compileCall, compileCall₂, compileCallWithError₂, hwφ₁', hwφ₂', someOf, decide_true,
      List.map_cons, List.map_nil, Bool.and_self, ↓reduceIte, Except.ok.injEq]
    have h₃ := $wf_thm (wf_option_get ($hwφ).left hty₁) (wf_option_get ($hwφ).right hty₂)
    have h₄ := Term.WellFormed.some_wf h₃.left
    have h₅ := wf_ifSome_option ($hwφ).right h₄ typeOf_term_some
    first
    | rw [h₃.right] at h₅
      simp only [
        interpret_ifSome $hI ($hwφ).left h₅.left,
        interpret_ifSome $hI ($hwφ).right h₄,
        interpret_term_some]
    | have h₆ := wf_ifSome_option ($hwφ).right h₃.left h₃.right
      simp only [
        interpret_ifSome $hI ($hwφ).left h₆.left,
        interpret_ifSome $hI ($hwφ).right h₃.left,
      ]
    first
      | simp only [$interpret_thm:ident]
      | simp only [$interpret_thm:ident $hI (wf_option_get ($hwφ).left hty₁) (wf_option_get ($hwφ).right hty₂)]
    simp only [
      interpret_option_get $I ($hwφ).left hty₁,
      interpret_option_get $I ($hwφ).right hty₂]
    first
    | apply pe_ifSome_get_eq_get'₂ $I (λ t₁' t₂' => Term.some ($xfn t₁' t₂')) hwφ₁' hwφ₂'
    | apply pe_ifSome_get_eq_get'₂ $I (λ t₁' t₂' => $xfn t₁' t₂') hwφ₁' hwφ₂'
    · replace h₃ := $wf_thm (wf_option_get hwφ₁'.left.left hwφ₁'.right) (wf_option_get hwφ₂'.left.left hwφ₂'.right)
      simp only [typeOf_term_some, h₃.right, TermType.option.injEq] ; rfl
    · replace h₃ := $wf_thm (wf_option_get' $hI hwφ₁'.left.left hwφ₁'.right) (wf_option_get' $hI hwφ₂'.left.left hwφ₂'.right)
      simp only [typeOf_term_some, h₃.right, TermType.option.injEq]
  ))

private theorem compileCall_interpret_decimal  {I : Interpretation} {ts : List Term} {t : Term}
  (hok : compileCall ExtFun.decimal ts = Except.ok t) :
  compileCall ExtFun.decimal (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by simp_compileCall₀_interpret hok compileCall_decimal_ok_implies

private theorem compileCall_interpret_decimal_lessThan {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.lessThan ts = Except.ok t) :
  compileCall ExtFun.lessThan (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₂_interpret I hI hwφ hok
    Decimal.lessThan compileCall_decimal_lessThan_ok_implies
    wf_decimal_lessThan interpret_decimal_lessThan

private theorem compileCall_interpret_decimal_lessThanOrEqual {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.lessThanOrEqual ts = Except.ok t) :
  compileCall ExtFun.lessThanOrEqual (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₂_interpret I hI hwφ hok
    Decimal.lessThanOrEqual compileCall_decimal_lessThanOrEqual_ok_implies
    wf_decimal_lessThanOrEqual interpret_decimal_lessThanOrEqual

private theorem compileCall_interpret_decimal_greaterThan {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.greaterThan ts = Except.ok t) :
  compileCall ExtFun.greaterThan (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₂_interpret I hI hwφ hok
    Decimal.greaterThan compileCall_decimal_greaterThan_ok_implies
    wf_decimal_greaterThan interpret_decimal_greaterThan

private theorem compileCall_interpret_decimal_greaterThanOrEqual {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.greaterThanOrEqual ts = Except.ok t) :
  compileCall ExtFun.greaterThanOrEqual (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₂_interpret I hI hwφ hok
    Decimal.greaterThanOrEqual compileCall_decimal_greaterThanOrEqual_ok_implies
    wf_decimal_greaterThanOrEqual interpret_decimal_greaterThanOrEqual

private theorem compileCall_interpret_ip  {I : Interpretation} {ts : List Term} {t : Term}
  (hok : compileCall ExtFun.ip ts = Except.ok t) :
  compileCall ExtFun.ip (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by simp_compileCall₀_interpret hok compileCall_ipAddr_ok_implies

private theorem compileCall_interpret_ipaddr_isIpv4 {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.isIpv4 ts = Except.ok t) :
  compileCall ExtFun.isIpv4 (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₁_interpret I hI hwφ hok
    IPAddr.isIpv4 compileCall_ipAddr_isIpv4_ok_implies
    wf_ipaddr_isIpv4 interpret_ipaddr_isIpv4

private theorem compileCall_interpret_ipaddr_isIpv6 {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.isIpv6 ts = Except.ok t) :
  compileCall ExtFun.isIpv6 (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₁_interpret I hI hwφ hok
    IPAddr.isIpv6 compileCall_ipAddr_isIpv6_ok_implies
    wf_ipaddr_isIpv6 interpret_ipaddr_isIpv6

private theorem compileCall_interpret_ipaddr_isLoopback {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.isLoopback ts = Except.ok t) :
  compileCall ExtFun.isLoopback (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₁_interpret I hI hwφ hok
    IPAddr.isLoopback compileCall_ipAddr_isLoopback_ok_implies
    wf_ipaddr_isLoopback interpret_ipaddr_isLoopback

private theorem compileCall_interpret_ipaddr_isMulticast {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.isMulticast ts = Except.ok t) :
  compileCall ExtFun.isMulticast (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₁_interpret I hI hwφ hok
    IPAddr.isMulticast compileCall_ipAddr_isMulticast_ok_implies
    wf_ipaddr_isMulticast interpret_ipaddr_isMulticast

private theorem compileCall_interpret_ipaddr_isInRange {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.isInRange ts = Except.ok t) :
  compileCall ExtFun.isInRange (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₂_interpret I hI hwφ hok
    IPAddr.isInRange compileCall_ipAddr_isInRange_ok_implies
    wf_ipaddr_isInRange interpret_ipaddr_isInRange

private theorem compileCall_interpret_datetime {I : Interpretation} {ts : List Term} {t : Term}
  (hok : compileCall ExtFun.datetime ts = Except.ok t) :
  compileCall ExtFun.datetime (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by simp_compileCall₀_interpret hok compileCall_datetime_ok_implies

private theorem compileCall_interpret_duration {I : Interpretation} {ts : List Term} {t : Term}
  (hok : compileCall ExtFun.duration ts = Except.ok t) :
  compileCall ExtFun.duration (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by simp_compileCall₀_interpret hok compileCall_duration_ok_implies

private theorem compileCall_interpret_datetime_offset {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.offset ts = Except.ok t) :
  compileCall ExtFun.offset (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by simp_compileCall₂_interpret I hI hwφ hok
  Datetime.offset compileCall_datetime_offset_ok_implies
  wf_datetime_offset interpret_datetime_offset

private theorem compileCall_interpret_datetime_durationSince {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.durationSince ts = Except.ok t) :
  compileCall ExtFun.durationSince (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by simp_compileCall₂_interpret I hI hwφ hok
  Datetime.durationSince compileCall_datetime_durationSince_ok_implies
  wf_datetime_durationSince interpret_datetime_durationSince

private theorem compileCall_interpret_datetime_toDate {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.toDate ts = Except.ok t) :
  compileCall ExtFun.toDate (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by simp_compileCall₁_interpret I hI hwφ hok
  Datetime.toDate compileCall_datetime_toDate_ok_implies
  wf_datetime_toDate interpret_datetime_toDate

private theorem compileCall_interpret_datetime_toTime {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.toTime ts = Except.ok t) :
  compileCall ExtFun.toTime (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by simp_compileCall₁_interpret I hI hwφ hok
  Datetime.toTime compileCall_datetime_toTime_ok_implies
  wf_datetime_toTime interpret_datetime_toTime

private theorem compileCall_interpret_duration_toMilliseconds {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.toMilliseconds ts = Except.ok t) :
  compileCall ExtFun.toMilliseconds (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₁_interpret I hI hwφ hok
    Duration.toMilliseconds compileCall_duration_toMilliseconds_ok_implies
    wf_duration_toMilliseconds interpret_duration_toMilliseconds

private theorem compileCall_interpret_duration_toSeconds {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.toSeconds ts = Except.ok t) :
  compileCall ExtFun.toSeconds (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₁_interpret I hI hwφ hok
    Duration.toSeconds compileCall_duration_toSeconds_ok_implies
    wf_duration_toSeconds interpret_duration_toSeconds

private theorem compileCall_interpret_duration_toMinutes {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.toMinutes ts = Except.ok t) :
  compileCall ExtFun.toMinutes (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₁_interpret I hI hwφ hok
    Duration.toMinutes compileCall_duration_toMinutes_ok_implies
    wf_duration_toMinutes interpret_duration_toMinutes

private theorem compileCall_interpret_duration_toHours {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.toHours ts = Except.ok t) :
  compileCall ExtFun.toHours (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₁_interpret I hI hwφ hok
    Duration.toHours compileCall_duration_toHours_ok_implies
    wf_duration_toHours interpret_duration_toHours

private theorem compileCall_interpret_duration_toDays {εs : SymEntities} {I : Interpretation} {ts : List Term} {t : Term}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall ExtFun.toDays ts = Except.ok t) :
  compileCall ExtFun.toDays (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  simp_compileCall₁_interpret I hI hwφ hok
    Duration.toDays compileCall_duration_toDays_ok_implies
    wf_duration_toDays interpret_duration_toDays

theorem compileCall_interpret {xfn : ExtFun} {ts : List Term} {t : Term} {I : Interpretation}
  (hI  : I.WellFormed εs)
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εs t)
  (hok : compileCall xfn ts = Except.ok t) :
  compileCall xfn (List.map (Term.interpret I) ts) = Except.ok (Term.interpret I t)
:= by
  cases xfn
  case decimal            => exact compileCall_interpret_decimal hok
  case lessThan           => exact compileCall_interpret_decimal_lessThan hI hwφ hok
  case lessThanOrEqual    => exact compileCall_interpret_decimal_lessThanOrEqual hI hwφ hok
  case greaterThan        => exact compileCall_interpret_decimal_greaterThan hI hwφ hok
  case greaterThanOrEqual => exact compileCall_interpret_decimal_greaterThanOrEqual hI hwφ hok
  case ip                 => exact compileCall_interpret_ip hok
  case isIpv4             => exact compileCall_interpret_ipaddr_isIpv4 hI hwφ hok
  case isIpv6             => exact compileCall_interpret_ipaddr_isIpv6 hI hwφ hok
  case isLoopback         => exact compileCall_interpret_ipaddr_isLoopback hI hwφ hok
  case isMulticast        => exact compileCall_interpret_ipaddr_isMulticast hI hwφ hok
  case isInRange          => exact compileCall_interpret_ipaddr_isInRange hI hwφ hok
  case datetime           => exact compileCall_interpret_datetime hok
  case duration           => exact compileCall_interpret_duration hok
  case offset             => exact compileCall_interpret_datetime_offset hI hwφ hok
  case durationSince      => exact compileCall_interpret_datetime_durationSince hI hwφ hok
  case toDate             => exact compileCall_interpret_datetime_toDate hI hwφ hok
  case toTime             => exact compileCall_interpret_datetime_toTime hI hwφ hok
  case toMilliseconds     => exact compileCall_interpret_duration_toMilliseconds hI hwφ hok
  case toSeconds          => exact compileCall_interpret_duration_toSeconds hI hwφ hok
  case toMinutes          => exact compileCall_interpret_duration_toMinutes hI hwφ hok
  case toHours            => exact compileCall_interpret_duration_toHours hI hwφ hok
  case toDays             => exact compileCall_interpret_duration_toDays hI hwφ hok

theorem compile_interpret_call {f : ExtFun} {xs : List Expr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (hI  : I.WellFormed εnv.entities)
  (hwε : εnv.WellFormedFor (.call f xs))
  (hok : compile (.call f xs) εnv = .ok t)
  (ih  : ∀ x ∈ xs, CompileInterpret x) :
  compile (.call f xs) (εnv.interpret I) = .ok (t.interpret I)
:= by
  replace ⟨ts, hok₂, hok⟩ := compile_call_ok_implies hok
  replace hwε := wf_εnv_for_call_implies hwε
  have hwφ := compile_wfs hwε hok₂
  replace ih := compile_interpret_ihs hI hwε ih hok₂
  simp only [compile, List.mapM₁_eq_mapM (λ x => compile x (SymEnv.interpret I εnv))]
  simp_do_let (List.mapM (fun x => compile x (SymEnv.interpret I εnv)) xs)
  case error h =>
    exact compile_interpret_args_not_error ih h
  case ok ts' hok' =>
    rw [List.mapM_ok_iff_forall₂] at hok'
    replace ih := compile_interpret_terms ih hok'
    clear hok'
    simp only [List.forall₂_iff_map_eq, List.map_id'] at ih
    subst ih
    exact compileCall_interpret hI hwφ hok

----- compile_evaluate tactics and lemmas for ExtFuns -----

local macro "simp_compileCall₀_evaluate" env:ident ih:ident hok:ident compile_call_thm:ident : tactic => do
  `(tactic| (
    replace ⟨_, _, hts, hv, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace ⟨x, $ih, hxs⟩ := List.forall₂_singleton_right_iff.mp $ih
    subst hxs
    simp only [List.mem_singleton, forall_eq, List.mapM_cons, List.mapM_nil, pure_bind,
      bind_assoc] at *
    simp_do_let (evaluate x ($env).request ($env).entities) <;>
    rename_i h <;>
    simp only [Same.same, SameResults, h] at $ih:ident
    replace $ih := same_string_term_implies $ih
    subst $ih
    simp only [call, res, hv, Coe.coe, Same.same, SameResults]
    exact same_ext
  ))

local macro "simp_compileCall₁_evaluate" env:ident hwφ:ident ih:ident hok:ident compile_call_thm:ident wfl_thm:ident pe_thm:ident : tactic => do
  `(tactic| (
    replace ⟨t, hts, hty, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace $hwφ := wf_arg' $hwφ
    replace ⟨x, $ih, hxs⟩ := List.forall₂_singleton_right_iff.mp $ih
    subst hxs
    simp only [List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc]
    cases h₁ : evaluate x ($env).request ($env).entities with simp only [Except.bind_err, Except.bind_ok]
    | error =>
      simp only [h₁] at $ih:ident
      exact same_error_implies_ifSome_error $ih typeOf_term_some
    | ok =>
      simp only [h₁] at $ih:ident
      replace ⟨_, ht, $ih⟩ := same_ok_implies $ih
      subst ht
      simp only [pe_ifSome_some typeOf_term_some, pe_option_get_some]
      simp only [typeOf_term_some, TermType.option.injEq] at hty
      have ⟨_, ht⟩ := $wfl_thm (And.intro (wf_term_some_implies $hwφ) (same_value_implies_lit $ih)) hty
      subst ht
      replace $ih := same_ext_term_implies $ih
      subst $ih
      simp only [call, $pe_thm:ident, same_ok_bool]
      try simp only [same_ok_some_iff, same_int64]
    ))

local macro "simp_compileCall₁_evaluate_ext" env:ident hwφ:ident ih:ident hok:ident compile_call_thm:ident wf_thm:ident wfl_arg_thm:ident pe_thm:ident ext_fun:ident : tactic => do
  `(tactic| (
    replace ⟨t, hts, hty, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace $hwφ := wf_arg' $hwφ
    replace ⟨x, $ih, hxs⟩ := List.forall₂_singleton_right_iff.mp $ih
    subst hxs
    simp only [List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc]
    cases h₁ : evaluate x ($env).request ($env).entities with simp only [Except.bind_err, Except.bind_ok]
    | error =>
      simp only [h₁] at $ih:ident
      first
      | exact same_error_implies_ifSome_error $ih typeOf_term_some
      | exact same_error_implies_ifSome_error $ih ($wf_thm (wf_option_get $hwφ hty)).right
    | ok =>
      simp only [h₁] at $ih:ident
      replace ⟨_, ht, $ih⟩ := same_ok_implies $ih
      subst ht
      first
      | simp only [pe_ifSome_some typeOf_term_some]
      | simp only [pe_ifSome_some ($wf_thm (wf_option_get $hwφ hty)).right]
      simp only [pe_option_get_some]
      simp only [typeOf_term_some, TermType.option.injEq] at hty
      have ⟨_, ht⟩ := $wfl_arg_thm (And.intro (wf_term_some_implies $hwφ) (same_value_implies_lit $ih)) hty
      subst ht
      replace $ih := same_ext_term_implies $ih
      subst $ih
      simp only [call, $pe_thm:ident]
      first
      | simp only [same_ok_some_iff, Coe.coe, same_ext]
      | rename_i pt _
        cases h: $ext_fun pt <;> simp only [res]
        case none =>
          apply same_error_implied_by; exact ne_of_beq_false rfl
        case some =>
          simp only [same_ok_some_iff, Coe.coe, same_ext]
  ))


local macro "simp_compileCall₂_evaluate" env:ident hwφ:ident ih:ident hok:ident compile_call_thm:ident wfl_thm:ident pe_thm:ident : tactic => do
  `(tactic| (
    replace ⟨t₁, t₂, hts, hty₁, hty₂, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace $hwφ := wf_args' $hwφ
    replace ⟨x₁, x₂, h₁, h₂, $ih⟩ := List.forall₂_pair_right_iff.mp $ih
    subst $ih
    simp only [List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc] at *
    cases h₃ : (evaluate x₁ ($env).request ($env).entities) with simp only [Except.bind_err, Except.bind_ok]
    | error =>
      simp only [h₃] at h₁
      exact same_error_implies_ifSome_error h₁ (typeOf_ifSome_option typeOf_term_some)
    | ok =>
      simp only [h₃] at h₁
      replace ⟨_, ht₁, h₁⟩ := same_ok_implies h₁
      subst ht₁
      simp only [pe_ifSome_some (typeOf_ifSome_option typeOf_term_some)]
      cases h₄ : (evaluate x₂ ($env).request ($env).entities) with simp only [Except.bind_err, Except.bind_ok]
      | error =>
        simp only [h₄] at h₂
        exact same_error_implies_ifSome_error h₂ typeOf_term_some
      | ok =>
        simp only [h₄] at h₂
        replace ⟨_, ht₂, h₂⟩ := same_ok_implies h₂
        subst ht₂
        simp only [typeOf_term_some, TermType.option.injEq] at hty₁ hty₂
        have ⟨_, ht₁⟩ := $wfl_thm (And.intro (wf_term_some_implies ($hwφ).left) (same_value_implies_lit h₁)) hty₁
        have ⟨_, ht₂⟩ := $wfl_thm (And.intro (wf_term_some_implies ($hwφ).right) (same_value_implies_lit h₂)) hty₂
        subst ht₁ ht₂
        replace h₁ := same_ext_term_implies h₁
        replace h₂ := same_ext_term_implies h₂
        subst h₁ h₂
        simp only [pe_option_get_some, pe_ifSome_some typeOf_term_some, call, $pe_thm:ident, same_ok_bool]
  ))

local macro "simp_compileCall₂_evaluate_ext" env:ident hwφ:ident ih:ident hok:ident compile_call_thm:ident wf_thm:ident wfl_arg₁_thm:ident wfl_arg₂_thm:ident pe_thm:ident ext_fun:ident : tactic => do
  `(tactic| (
    replace ⟨t₁, t₂, hts, hty₁, hty₂, $hok⟩ := $compile_call_thm $hok
    subst $hok hts
    replace $hwφ := wf_args' $hwφ
    replace ⟨x₁, x₂, h₁, h₂, $ih⟩ := List.forall₂_pair_right_iff.mp $ih
    subst $ih
    simp only [List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc] at *
    have hty := ($wf_thm (wf_option_get ($hwφ).left hty₁) (wf_option_get ($hwφ).right hty₂)).right
    cases h₃ : (evaluate x₁ ($env).request ($env).entities) with simp only [Except.bind_err, Except.bind_ok]
    | error =>
      simp only [h₃] at h₁
      exact same_error_implies_ifSome_error h₁ (typeOf_ifSome_option hty)
    | ok =>
      simp only [h₃] at h₁
      replace ⟨_, ht₁, h₁⟩ := same_ok_implies h₁
      subst ht₁
      simp only [pe_ifSome_some (typeOf_ifSome_option hty)]
      cases h₄ : (evaluate x₂ ($env).request ($env).entities) with simp only [Except.bind_err, Except.bind_ok]
      | error =>
        simp only [h₄] at h₂
        exact same_error_implies_ifSome_error h₂ hty
      | ok =>
        simp only [h₄] at h₂
        replace ⟨_, ht₂, h₂⟩ := same_ok_implies h₂
        subst ht₂
        simp only [typeOf_term_some, TermType.option.injEq] at hty₁ hty₂
        have ⟨_, ht₁⟩ := $wfl_arg₁_thm (And.intro (wf_term_some_implies ($hwφ).left) (same_value_implies_lit h₁)) hty₁
        have ⟨_, ht₂⟩ := $wfl_arg₂_thm (And.intro (wf_term_some_implies ($hwφ).right) (same_value_implies_lit h₂)) hty₂
        subst ht₁ ht₂
        replace h₁ := same_ext_term_implies h₁
        replace h₂ := same_ext_term_implies h₂
        subst h₁ h₂
        simp only [pe_option_get_some]
        rename_i pt₁ pt₂ _
        simp only [pe_ifSome_some ($wf_thm (And.intro (wf_term_some_implies ($hwφ).left) hty₁) (And.intro (wf_term_some_implies ($hwφ).right) hty₂)).right,
          call]
        simp only [$pe_thm:ident]
        cases $ext_fun pt₁ pt₂ <;> simp only [res]
        case none =>
          apply same_error_implied_by; exact ne_of_beq_false rfl
        case some =>
          simp only [same_ok_some_iff, Coe.coe, same_ext]
  ))


private theorem compile_evaluate_call_decimal {xs : List Expr} {ts : List Term} {env : Env} {t : Term}
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.decimal ts = Except.ok t) :
  (do call ExtFun.decimal (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₀_evaluate env ih hok compileCall_decimal_ok_implies

private theorem compile_evaluate_call_ip {xs : List Expr} {ts : List Term} {env : Env} {t : Term}
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.ip ts = Except.ok t) :
  (do call ExtFun.ip (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₀_evaluate env ih hok compileCall_ipAddr_ok_implies

private theorem compile_evaluate_call_decimal_lessThan {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.lessThan ts = Except.ok t) :
  (do call ExtFun.lessThan (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate env hwφ ih hok compileCall_decimal_lessThan_ok_implies
    wfl_of_type_ext_decimal_is_ext_decimal pe_decimal_lessThan

private theorem compile_evaluate_call_decimal_lessThanOrEqual {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.lessThanOrEqual ts = Except.ok t) :
  (do call ExtFun.lessThanOrEqual (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate env hwφ ih hok compileCall_decimal_lessThanOrEqual_ok_implies
    wfl_of_type_ext_decimal_is_ext_decimal pe_decimal_lessThanOrEqual

private theorem compile_evaluate_call_decimal_greaterThan {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.greaterThan ts = Except.ok t) :
  (do call ExtFun.greaterThan (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate env hwφ ih hok compileCall_decimal_greaterThan_ok_implies
    wfl_of_type_ext_decimal_is_ext_decimal pe_decimal_greaterThan

private theorem compile_evaluate_call_decimal_greaterThanOrEqual {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.greaterThanOrEqual ts = Except.ok t) :
  (do call ExtFun.greaterThanOrEqual (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate env hwφ ih hok compileCall_decimal_greaterThanOrEqual_ok_implies
    wfl_of_type_ext_decimal_is_ext_decimal pe_decimal_greaterThanOrEqual

private theorem compile_evaluate_call_ipaddr_isIpv4 {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.isIpv4 ts = Except.ok t) :
  (do call ExtFun.isIpv4 (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate env hwφ ih hok
    compileCall_ipAddr_isIpv4_ok_implies wfl_of_type_ext_ipaddr_is_ext_ipaddr
    pe_ipaddr_isIpv4

private theorem compile_evaluate_call_ipaddr_isIpv6 {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.isIpv6 ts = Except.ok t) :
  (do call ExtFun.isIpv6 (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate env hwφ ih hok
    compileCall_ipAddr_isIpv6_ok_implies wfl_of_type_ext_ipaddr_is_ext_ipaddr
    pe_ipaddr_isIpv6

private theorem compile_evaluate_call_ipaddr_isInRange {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.isInRange ts = Except.ok t) :
  (do call ExtFun.isInRange (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate env hwφ ih hok compileCall_ipAddr_isInRange_ok_implies
    wfl_of_type_ext_ipaddr_is_ext_ipaddr pe_ipaddr_isInRange

private theorem compile_evaluate_call_ipaddr_isLoopback {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.isLoopback ts = Except.ok t) :
  (do call ExtFun.isLoopback (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate env hwφ ih hok compileCall_ipAddr_isLoopback_ok_implies
    wfl_of_type_ext_ipaddr_is_ext_ipaddr pe_ipaddr_isLoopback

private theorem compile_evaluate_call_ipaddr_isMulticast {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.isMulticast  ts = Except.ok t) :
  (do call ExtFun.isMulticast  (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate env hwφ ih hok compileCall_ipAddr_isMulticast_ok_implies
    wfl_of_type_ext_ipaddr_is_ext_ipaddr pe_ipaddr_isMulticast

private theorem compile_evaluate_call_datetime {xs : List Expr} {ts : List Term} {env : Env} {t : Term}
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.datetime ts = Except.ok t) :
  (do call ExtFun.datetime (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₀_evaluate env ih hok compileCall_datetime_ok_implies

private theorem compile_evaluate_call_duration {xs : List Expr} {ts : List Term} {env : Env} {t : Term}
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.duration ts = Except.ok t) :
  (do call ExtFun.duration (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₀_evaluate env ih hok compileCall_duration_ok_implies

private theorem compile_evaluate_call_datetime_offset {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.offset ts = Except.ok t) :
  (do call ExtFun.offset (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate_ext  env hwφ ih hok compileCall_datetime_offset_ok_implies
    wf_datetime_offset wfl_of_type_ext_datetime_is_ext_datetime wfl_of_type_ext_duration_is_ext_duration
    pe_datetime_offset Ext.Datetime.offset

private theorem compile_evaluate_call_datetime_durationSince {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.durationSince ts = Except.ok t) :
  (do call ExtFun.durationSince (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₂_evaluate_ext  env hwφ ih hok compileCall_datetime_durationSince_ok_implies
    wf_datetime_durationSince wfl_of_type_ext_datetime_is_ext_datetime wfl_of_type_ext_datetime_is_ext_datetime
    pe_datetime_durationSince Ext.Datetime.durationSince

private theorem compile_evaluate_call_datetime_toDate {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toDate ts = Except.ok t) :
  (do call ExtFun.toDate (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_ext env hwφ ih hok compileCall_datetime_toDate_ok_implies
    wf_datetime_toDate wfl_of_type_ext_datetime_is_ext_datetime pe_datetime_toDate Ext.Datetime.toDate

private theorem compile_evaluate_call_datetime_toTime {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toTime ts = Except.ok t) :
  (do call ExtFun.toTime (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate_ext env hwφ ih hok compileCall_datetime_toTime_ok_implies
    wf_datetime_toTime wfl_of_type_ext_datetime_is_ext_datetime pe_datetime_toTime Ext.Datetime.toTime

private theorem compile_evaluate_call_duration_toMilliseconds {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toMilliseconds ts = Except.ok t) :
  (do call ExtFun.toMilliseconds (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate env hwφ ih hok compileCall_duration_toMilliseconds_ok_implies
    wfl_of_type_ext_duration_is_ext_duration pe_duration_toMilliseconds

private theorem compile_evaluate_call_duration_toSeconds {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toSeconds ts = Except.ok t) :
  (do call ExtFun.toSeconds (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate env hwφ ih hok compileCall_duration_toSeconds_ok_implies
    wfl_of_type_ext_duration_is_ext_duration pe_duration_toSeconds

private theorem compile_evaluate_call_duration_toMinutes {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toMinutes ts = Except.ok t) :
  (do call ExtFun.toMinutes (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate env hwφ ih hok compileCall_duration_toMinutes_ok_implies
    wfl_of_type_ext_duration_is_ext_duration pe_duration_toMinutes

private theorem compile_evaluate_call_duration_toHours {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toHours ts = Except.ok t) :
  (do call ExtFun.toHours (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate env hwφ ih hok compileCall_duration_toHours_ok_implies
    wfl_of_type_ext_duration_is_ext_duration pe_duration_toHours

private theorem compile_evaluate_call_duration_toDays {xs : List Expr} {ts : List Term} {env : Env} {εnv : SymEnv} {t : Term}
  (hwφ : ∀ (t : Term), t ∈ ts → Term.WellFormed εnv.entities t)
  (ih  : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (hok : compileCall ExtFun.toDays ts = Except.ok t) :
  (do call ExtFun.toDays (← xs.mapM (evaluate · env.request env.entities))) ∼ t
:= by
  simp_compileCall₁_evaluate env hwφ ih hok compileCall_duration_toDays_ok_implies
    wfl_of_type_ext_duration_is_ext_duration pe_duration_toDays

theorem compile_evaluate_call {f : ExtFun} {xs : List Expr} {env : Env} {εnv : SymEnv} {t : Term}
  (heq : env ∼ εnv)
  (hwe : env.WellFormedFor (.call f xs))
  (hwε : εnv.WellFormedFor (.call f xs))
  (hok : compile (.call f xs) εnv = .ok t)
  (ih  : ∀ x ∈ xs, CompileEvaluate x) :
  evaluate (.call f xs) env.request env.entities ∼ t
:= by
  replace ⟨ts, hok₂, hok⟩ := compile_call_ok_implies hok
  replace hwε := wf_εnv_for_call_implies hwε
  have hwφ := compile_wfs hwε hok₂
  replace ih := compile_evaluate_ihs heq (wf_env_for_call_implies hwe) hwε ih hok₂
  simp only [evaluate, List.mapM₁_eq_mapM (evaluate · env.request env.entities)]
  cases f
  case decimal =>
    exact compile_evaluate_call_decimal ih hok
  case lessThan =>
    exact compile_evaluate_call_decimal_lessThan hwφ ih hok
  case lessThanOrEqual =>
    exact compile_evaluate_call_decimal_lessThanOrEqual hwφ ih hok
  case greaterThan =>
    exact compile_evaluate_call_decimal_greaterThan hwφ ih hok
  case greaterThanOrEqual =>
    exact compile_evaluate_call_decimal_greaterThanOrEqual hwφ ih hok
  case ip =>
    exact compile_evaluate_call_ip ih hok
  case isIpv4 =>
    exact compile_evaluate_call_ipaddr_isIpv4 hwφ ih hok
  case isIpv6 =>
    exact compile_evaluate_call_ipaddr_isIpv6 hwφ ih hok
  case isLoopback =>
    exact compile_evaluate_call_ipaddr_isLoopback hwφ ih hok
  case isMulticast =>
    exact compile_evaluate_call_ipaddr_isMulticast hwφ ih hok
  case isInRange =>
    exact compile_evaluate_call_ipaddr_isInRange hwφ ih hok
  case datetime =>
    exact compile_evaluate_call_datetime ih hok
  case duration =>
    exact compile_evaluate_call_duration ih hok
  case offset =>
    exact compile_evaluate_call_datetime_offset hwφ ih hok
  case durationSince =>
    exact compile_evaluate_call_datetime_durationSince hwφ ih hok
  case toDate =>
    exact compile_evaluate_call_datetime_toDate hwφ ih hok
  case toTime =>
    exact compile_evaluate_call_datetime_toTime hwφ ih hok
  case toMilliseconds =>
    exact compile_evaluate_call_duration_toMilliseconds hwφ ih hok
  case toSeconds =>
    exact compile_evaluate_call_duration_toSeconds hwφ ih hok
  case toMinutes =>
    exact compile_evaluate_call_duration_toMinutes hwφ ih hok
  case toHours =>
    exact compile_evaluate_call_duration_toHours hwφ ih hok
  case toDays =>
    exact compile_evaluate_call_duration_toDays hwφ ih hok

end Cedar.Thm
