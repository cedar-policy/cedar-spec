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

public import CedarRustModel.Ext.Decimal
public import CedarRustModel.Ext.IPAddrBridge
public import CedarRustModel.Ext.DatetimeBridge
public import CedarRustModel.Ext.DurationBridge
public import CedarRustModel.Ext.IPOps
import all Cedar.Spec.ExtFun
import all Cedar.Spec.Ext.Datetime
import all Cedar.Data.Int64
import all Cedar.Spec.Ext.IPAddr
import all Cedar.Spec.Ext

/-!
# Correctness of the extension model

The model's extension functions (`ext::call`, `src/ext.rs`) compute Lean's
`Cedar.Spec.call`, values and errors alike.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model
open Cedar.Spec Cedar.Spec.Ext

/-! ## Values -/

theorem opt_i64 {r : Option I64} {o : Option Int64} (h : r.map (·.val) = o.map Int64.toInt) :
    r.map (fun x => Int64.ofInt x.val) = o := by
  cases r <;> cases o <;> simp_all

theorem opt_dt {r : Option I64} {o : Option Datetime} (h : r.map (·.val) = o.map (fun d => d.val.toInt)) :
    r.map (fun x => (⟨Int64.ofInt x.val⟩ : Datetime)) = o := by
  cases r <;> cases o <;> simp_all

theorem opt_dur {r : Option I64} {o : Option Duration}
    (h : r.map (·.val) = o.map (fun d => d.val.toInt)) :
    r.map (fun x => (⟨Int64.ofInt x.val⟩ : Duration)) = o := by
  cases r <;> cases o <;> simp_all

theorem toInt_ofInt_val (x : I64) : (Int64.ofInt x.val).toInt = x.val :=
  XL.ofInt_toInt' _ (by scalar_tac)

/-! ## Parsers -/

public theorem parse_decimal_correct (s : value.List Char) :
    ext.parse_decimal s ⦃ r => r.map (fun d => Int64.ofInt d.val) = Decimal.parse (Str.toSpec s) ⦄ :=
  WP.spec_mono (parse_decimal_spec s) fun _ h => opt_i64 (by rw [← h, XL.parseDecimal_eq]; rfl)

public theorem parse_ip_correct (s : value.List Char) :
    ext.parse_ip s ⦃ r => r.map IPNet.toSpec = IPAddr.ip (Str.toSpec s) ⦄ :=
  WP.spec_mono (parse_ip_spec s) fun _ h => by rw [← h, XL.parseIP_eq]; rfl

public theorem parse_datetime_correct (s : value.List Char) :
    ext.parse_datetime s ⦃ r => r.map (fun d => (⟨Int64.ofInt d.val⟩ : Datetime)) =
      Datetime.parse (Str.toSpec s) ⦄ :=
  WP.spec_mono (parse_datetime_spec s) fun _ h => opt_dt (by rw [← h, XL.parseDatetime_eq]; rfl)

public theorem parse_duration_correct (s : value.List Char) :
    ext.parse_duration s ⦃ r => r.map (fun d => (⟨Int64.ofInt d.val⟩ : Duration)) =
      Datetime.Duration.parse (Str.toSpec s) ⦄ :=
  WP.spec_mono (parse_duration_spec s) fun _ h => opt_dur (by rw [← h, XL.parseDuration_eq]; rfl)

theorem parsePrefix_le {l : List Char} {max maxLen n : Nat} (h : XL.parsePrefix l max maxLen = some n) :
    n ≤ max := by
  unfold XL.parsePrefix at h
  split_ifs at h <;> (try split at h) <;> simp_all <;> omega

/-- The networks parsed by the model are well formed. -/
public theorem parse_ip_wf (s : value.List Char) :
    ext.parse_ip s ⦃ r => ∀ a, r = some a → Ext.WF (.IPAddr a) ⦄ := by
  unfold ext.parse_ip
  step*
  all_goals (try obtain ⟨_, _⟩ := p)
  all_goals (try step*)
  all_goals (intro a ha; subst_vars; simp_all [Ext.WF])
  all_goals (subst_vars; simp only [Ext.WF])
  all_goals (try scalar_tac)
  all_goals (exact parsePrefix_le ‹_›)


/-! ## Operations -/

theorem i64_lt (x y : I64) : (x < y) ↔ Int64.ofInt x.val < Int64.ofInt y.val := by
  rw [Int64.lt_iff_toInt_lt, toInt_ofInt_val, toInt_ofInt_val]; exact Iff.rfl
theorem i64_le (x y : I64) : (x ≤ y) ↔ Int64.ofInt x.val ≤ Int64.ofInt y.val := by
  rw [Int64.le_iff_toInt_le, toInt_ofInt_val, toInt_ofInt_val]; exact Iff.rfl

theorem val_lt (x y : I64) : (x.val < y.val) ↔ Int64.ofInt x.val < Int64.ofInt y.val := by
  rw [Int64.lt_iff_toInt_lt, toInt_ofInt_val, toInt_ofInt_val]
theorem val_le (x y : I64) : (x.val ≤ y.val) ↔ Int64.ofInt x.val ≤ Int64.ofInt y.val := by
  rw [Int64.le_iff_toInt_le, toInt_ofInt_val, toInt_ofInt_val]

theorem ofInt?_eq (v : Int) : Int64.ofInt? v = (XL.chk v).map Int64.ofInt := by
  rw [XL.chk_eq]
  by_cases h : -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807
  · rw [if_pos h, Int64.ofInt?_some_iff.mp (by simp only [Int64.MIN, Int64.MAX]; omega)]; rfl
  · rw [if_neg h]
    cases ho : Int64.ofInt? v with
    | none => rfl
    | some i =>
      have := Int64.ofInt?_some_toInt ho
      have := XL.toInt_range i
      omega

theorem add?_eq (a b : I64) :
    (I64.checked_add a b).map (fun x => Int64.ofInt x.val) = Int64.add? (Int64.ofInt a.val) (Int64.ofInt b.val) := by
  apply opt_i64
  rw [I64.checked_add_val, Int64.add?, ofInt?_eq, toInt_ofInt_val, toInt_ofInt_val]
  unfold XL.chk
  split <;> simp_all
  have h := XL.ofInt_toInt' _ ((XL.inI64_iff _).1 ‹_›)
  simp only [Int64.toInt_ofInt] at h; exact h.symm

theorem sub?_eq (a b : I64) :
    (I64.checked_sub a b).map (fun x => Int64.ofInt x.val) = Int64.sub? (Int64.ofInt a.val) (Int64.ofInt b.val) := by
  apply opt_i64
  rw [I64.checked_sub_val, Int64.sub?, ofInt?_eq, toInt_ofInt_val, toInt_ofInt_val]
  unfold XL.chk
  split <;> simp_all
  have h := XL.ofInt_toInt' _ ((XL.inI64_iff _).1 ‹_›)
  simp only [Int64.toInt_ofInt] at h; exact h.symm

theorem sub_map (a b : I64) :
    (I64.checked_sub a b).map (fun x => Int64.ofInt x.val) = (XL.chk (a.val - b.val)).map Int64.ofInt := by
  have := I64.checked_sub_val a b
  cases h : I64.checked_sub a b <;> simp_all [XL.chk] <;> split_ifs at this <;> simp_all

theorem ms_day_toInt (M : Int64) (h : Int64.ofIntChecked Datetime.MILLISECONDS_PER_DAY (by decide) = M) :
    M.toInt = 86400000 := by
  rw [← h]; simp [Int64.ofIntChecked, Datetime.MILLISECONDS_PER_DAY]

theorem div_toInt (a M : Int64) (hM : M.toInt = 86400000) : (a.div M).toInt = a.toInt.tdiv 86400000 := by
  have : M ≠ -1 := by intro h; rw [h] at hM; simp at hM
  rw [show a.div M = a / M from rfl, Int64.toInt_div_of_ne_right _ _ this, hM]

theorem mod_toInt (a M : Int64) (hM : M.toInt = 86400000) : (a.mod M).toInt = a.toInt.tmod 86400000 := by
  rw [show a.mod M = a % M from rfl, Int64.toInt_mod, hM]

theorem beq_zero (a : Int64) : (a == 0) = decide (a.toInt = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← Int64.toInt_inj]; simp

theorem ge_zero (x : I64) : (Int64.ofInt x.val ≥ 0) ↔ 0 ≤ x.val := by
  rw [GE.ge, Int64.le_iff_toInt_le, toInt_ofInt_val]; simp

theorem chk_map_dt (v : Int) :
    (do let a ← (XL.chk v).map Int64.ofInt; pure (⟨a⟩ : Datetime)) = (XL.chk v).map (fun v => (⟨Int64.ofInt v⟩ : Datetime)) := by
  cases XL.chk v <;> rfl

theorem dt_to_date_correct (dt : I64) :
    ext.dt_to_date dt ⦃ r => r.map (fun x => (⟨Int64.ofInt x.val⟩ : Datetime)) =
      Datetime.toDate ⟨Int64.ofInt dt.val⟩ ⦄ := by
  unfold ext.dt_to_date
  have hms : 0 < (ext.MS_PER_DAY).val := by rw [ms_per_day_val]; omega
  step
  have hb := tdiv_bounds_gen dt.val 86400000 (by omega)
  have htm := Int.tmod_def dt.val 86400000
  unfold Datetime.toDate
  simp only [Datetime.datetime?, ofInt?_eq]
  generalize hMd : Int64.ofIntChecked Datetime.MILLISECONDS_PER_DAY _ = M
  have hMv := ms_day_toInt M hMd
  simp only [div_toInt _ M hMv, mod_toInt _ M hMv, beq_zero, toInt_ofInt_val, hMv, ge_zero,
    decide_eq_true_eq]
  rw [ms_per_day_val] at r_post
  have hcomp : ∀ o : Option I64, o.map (fun x => (⟨Int64.ofInt x.val⟩ : Datetime)) =
      (o.map (fun x => Int64.ofInt x.val)).map Datetime.mk := by intro o; cases o <;> rfl
  by_cases hneg : r < 0#i64
  · have hr : r.val < 0 := by scalar_tac
    simp only [hneg, ite_true]
    step*
    rw [ms_per_day_val] at r1_post
    rw [hcomp, sub_map]
    have hd : ¬ 0 ≤ dt.val := by
      intro h; have := Int.tmod_nonneg 86400000 h; omega
    have ht : ¬ dt.val.tmod 86400000 = 0 := by omega
    rw [if_neg hd, if_neg ht, show dt.val - r1.val = (dt.val.tdiv 86400000 - 1) * 86400000 by omega]
    cases XL.chk _ <;> rfl
  · have hr : 0 ≤ r.val := by scalar_tac
    simp only [hneg, ite_false, bind_ok, WP.spec_ok]
    rw [hcomp, sub_map]
    by_cases hd : 0 ≤ dt.val
    · rw [if_pos hd, show dt.val - r.val = 86400000 * dt.val.tdiv 86400000 by omega]
      cases XL.chk _ <;> rfl
    · have h0 : dt.val.tmod 86400000 = 0 := by omega
      rw [if_neg hd, if_pos h0, show dt.val - r.val = dt.val by omega, XL.chk_eq, if_pos (by scalar_tac)]
      rfl

theorem dt_to_time_correct (dt : I64) :
    ext.dt_to_time dt ⦃ r => (⟨Int64.ofInt r.val⟩ : Duration) = Datetime.toTime ⟨Int64.ofInt dt.val⟩ ⦄ := by
  unfold ext.dt_to_time
  have hms : 0 < (ext.MS_PER_DAY).val := by rw [ms_per_day_val]; omega
  have hb := tdiv_bounds_gen dt.val 86400000 (by omega)
  have htm := Int.tmod_def dt.val 86400000
  unfold Datetime.toTime
  generalize hMd : Int64.ofIntChecked Datetime.MILLISECONDS_PER_DAY _ = M
  have hMv := ms_day_toInt M hMd
  have hm := mod_toInt (Int64.ofInt dt.val) M hMv
  rw [toInt_ofInt_val] at hm
  by_cases hneg : dt < 0#i64
  · have hd : dt.val < 0 := by scalar_tac
    have hd' : ¬ (Int64.ofInt dt.val ≥ 0) := by rw [ge_zero]; omega
    simp only [hneg, ite_true, hd', ite_false]
    step
    rw [ms_per_day_val] at r_post
    by_cases h0 : r = 0#i64
    · have hr0 : r.val = 0 := by rw [h0]; rfl
      have hz : (Int64.ofInt dt.val).mod M == 0 := by rw [beq_zero, hm]; simp; omega
      simp only [h0, ite_true, hz, WP.spec_ok]
      congr 1; apply Int64.toInt_inj.mp; rw [hm]; simp; omega
    · have hr0 : r.val ≠ 0 := fun e => h0 (by scalar_tac)
      have hz : ((Int64.ofInt dt.val).mod M == 0) = false := by rw [beq_zero, hm]; simp; omega
      simp only [h0, ite_false, hz, Bool.false_eq_true]
      have hr0v := r_post
      step*
      rw [ms_per_day_val] at r_post
      congr 1; apply Int64.toInt_inj.mp
      rw [Int64.toInt_add, hm, hMv, toInt_ofInt_val, r_post, hr0v]
      rw [Int.bmod_eq_of_le (by omega) (by omega)]
  · have hd : 0 ≤ dt.val := by scalar_tac
    have hd' : (Int64.ofInt dt.val ≥ 0) := by rw [ge_zero]; omega
    simp only [hneg, ite_false, hd', ite_true]
    step
    rw [ms_per_day_val] at r_post
    congr 1; apply Int64.toInt_inj.mp; rw [hm, toInt_ofInt_val, r_post]

theorem div_lit (a b : Int64) (k : Int) (hb : b.toInt = k) (hk : 0 < k) :
    (a / b).toInt = a.toInt.tdiv k := by
  have : b ≠ -1 := by intro h; rw [h] at hb; simp at hb; omega
  rw [Int64.toInt_div_of_ne_right _ _ this, hb]

theorem toSeconds_toInt (x : I64) :
    (Datetime.Duration.toSeconds ⟨Int64.ofInt x.val⟩).toInt = x.val.tdiv 1000 := by
  simp only [Datetime.Duration.toSeconds, Datetime.Duration.toMilliseconds]
  rw [div_lit _ _ 1000 (by decide) (by omega), toInt_ofInt_val]

theorem toMinutes_toInt (x : I64) :
    (Datetime.Duration.toMinutes ⟨Int64.ofInt x.val⟩).toInt = (x.val.tdiv 1000).tdiv 60 := by
  simp only [Datetime.Duration.toMinutes]
  rw [div_lit _ _ 60 (by decide) (by omega), toSeconds_toInt]

theorem toHours_toInt (x : I64) :
    (Datetime.Duration.toHours ⟨Int64.ofInt x.val⟩).toInt = ((x.val.tdiv 1000).tdiv 60).tdiv 60 := by
  simp only [Datetime.Duration.toHours]
  rw [div_lit _ _ 60 (by decide) (by omega), toMinutes_toInt]

theorem toDays_toInt (x : I64) :
    (Datetime.Duration.toDays ⟨Int64.ofInt x.val⟩).toInt = (((x.val.tdiv 1000).tdiv 60).tdiv 60).tdiv 24 := by
  simp only [Datetime.Duration.toDays]
  rw [div_lit _ _ 24 (by decide) (by omega), toHours_toInt]

theorem i64_eq_of_toInt {a : I64} {b : Int64} (h : a.val = b.toInt) : Int64.ofInt a.val = b := by
  rw [h, Int64.ofInt_toInt]

/-! ## Calls -/

/-- The relation between a model call and a Lean call -/
abbrev CallRel (f : ext.ExtFun) (args : value.List value.Value) (r : core.result.Result ext.ExtRes value.Error) : Prop :=
  Result.toSpec ExtRes.toSpec r = Cedar.Spec.call (ExtFun.toSpec f) (Values.toSpec args)

set_option hygiene false in
macro "ext_tc" : tactic => `(tactic| (simp [ext.one_arg, ext.two_args, ext.ext_or_err, CallRel, Result.toSpec,
  Error.toSpec, ExtRes.toSpec, Ext.toSpec, List.toList, Cedar.Spec.call, ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, res,
  WP.spec_ok, ext.call_string, ext.call_decimal_cmp, ext.call_ip_pred, ext.call_duration_conv]; done))

set_option hygiene false in
macro "ext_cases1" : tactic => `(tactic| (rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
  (try rcases a with ((_|_|s|_)|_|_|(x|x|x|x)))))

set_option hygiene false in
macro "ext_cases2" : tactic => `(tactic| (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
  (try rcases a with ((_|_|s|_)|_|_|(x|x|x|x))) <;> (try rcases b with ((_|_|t|_)|_|_|(y|y|y|y)))))

theorem call_string_correct (f : ext.ExtFun)
    (hf : f = .Decimal ∨ f = .Ip ∨ f = .Datetime ∨ f = .Duration) (args : value.List value.Value) :
    ext.call f args ⦃ r => CallRel f args r ⦄ := by
  rcases hf with rfl | rfl | rfl | rfl <;> unfold ext.call <;> ext_cases1
  all_goals first
    | ext_tc
    | (simp only [ext.call_string, ext.one_arg, bind_ok]
       first
        | (obtain ⟨r, hr, hpost⟩ := spec_ok_exists (parse_decimal_correct s)
           rw [hr]; simp only [bind_ok]
           have hl : Decimal.decimal (Str.toSpec s) = r.map (fun d => Int64.ofInt d.val) := hpost.symm
           cases r <;> simp_all [ext.ext_or_err, CallRel, Result.toSpec, Error.toSpec, ExtRes.toSpec,
             Ext.toSpec, List.toList, Cedar.Spec.call, ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, res, WP.spec_ok] <;> rfl)
        | (obtain ⟨r, hr, hpost⟩ := spec_ok_exists (parse_ip_correct s)
           rw [hr]; simp only [bind_ok]
           have hl : IPAddr.ip (Str.toSpec s) = r.map IPNet.toSpec := hpost.symm
           cases r <;> simp_all [ext.ext_or_err, CallRel, Result.toSpec, Error.toSpec, ExtRes.toSpec,
             Ext.toSpec, List.toList, Cedar.Spec.call, ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, res, WP.spec_ok] <;> rfl)
        | (obtain ⟨r, hr, hpost⟩ := spec_ok_exists (parse_datetime_correct s)
           rw [hr]; simp only [bind_ok]
           have hl : Datetime.parse (Str.toSpec s) = r.map (fun d => (⟨Int64.ofInt d.val⟩ : Datetime)) := hpost.symm
           cases r <;> simp_all [ext.ext_or_err, CallRel, Result.toSpec, Error.toSpec, ExtRes.toSpec,
             Ext.toSpec, List.toList, Cedar.Spec.call, ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, res, WP.spec_ok] <;> rfl)
        | (obtain ⟨r, hr, hpost⟩ := spec_ok_exists (parse_duration_correct s)
           rw [hr]; simp only [bind_ok]
           have hl : Datetime.Duration.parse (Str.toSpec s) =
             r.map (fun d => (⟨Int64.ofInt d.val⟩ : Duration)) := hpost.symm
           cases r <;> simp_all [ext.ext_or_err, CallRel, Result.toSpec, Error.toSpec, ExtRes.toSpec,
             Ext.toSpec, List.toList, Cedar.Spec.call, ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, res, WP.spec_ok] <;> rfl))

set_option maxHeartbeats 1000000 in
theorem call_decimal_cmp_correct (f : ext.ExtFun)
    (hf : f = .LessThan ∨ f = .LessThanOrEqual ∨ f = .GreaterThan ∨ f = .GreaterThanOrEqual)
    (args : value.List value.Value) :
    ext.call f args ⦃ r => CallRel f args r ⦄ := by
  rcases hf with rfl | rfl | rfl | rfl <;> unfold ext.call <;> ext_cases2
  all_goals first
    | ext_tc
    | (simp [ext.call_decimal_cmp, ext.two_args, CallRel, Result.toSpec, ExtRes.toSpec, List.toList,
        Cedar.Spec.call, ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, Ext.toSpec, WP.spec_ok, i64_lt, i64_le, val_lt, val_le]; done)

theorem call_ip_pred_correct (f : ext.ExtFun)
    (hf : f = .IsIpv4 ∨ f = .IsIpv6 ∨ f = .IsLoopback ∨ f = .IsMulticast)
    (args : value.List value.Value) :
    ext.call f args ⦃ r => CallRel f args r ⦄ := by
  rcases hf with rfl | rfl | rfl | rfl <;> unfold ext.call <;> ext_cases1
  all_goals first
    | ext_tc
    | (simp only [ext.call_ip_pred, ext.one_arg, bind_ok]
       step*
       simp_all [CallRel, Result.toSpec, ExtRes.toSpec, List.toList, Cedar.Spec.call, ExtFun.toSpec,
         Value.toSpec, Values.toSpec, Prim.toSpec, Ext.toSpec])

theorem call_in_range_correct (args : value.List value.Value) :
    ext.call .IsInRange args ⦃ r => CallRel .IsInRange args r ⦄ := by
  unfold ext.call; ext_cases2
  all_goals first
    | ext_tc
    | (simp only [ext.two_args, bind_ok]
       step*
       simp_all [CallRel, Result.toSpec, ExtRes.toSpec, List.toList, Cedar.Spec.call, ExtFun.toSpec,
         Value.toSpec, Values.toSpec, Prim.toSpec, Ext.toSpec])

theorem call_offset_correct (args : value.List value.Value) :
    ext.call .Offset args ⦃ r => CallRel .Offset args r ⦄ := by
  unfold ext.call; ext_cases2
  all_goals first
    | ext_tc
    | (simp only [ext.two_args, ext.dt_offset, bind_ok]
       have h := (add?_eq x y).symm
       cases hc : I64.checked_add x y <;> simp_all [ext.ext_or_err, CallRel, Result.toSpec, Error.toSpec,
         ExtRes.toSpec, List.toList, Cedar.Spec.call, ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, Ext.toSpec, res, WP.spec_ok,
         Datetime.offset] <;> rfl)

theorem call_duration_since_correct (args : value.List value.Value) :
    ext.call .DurationSince args ⦃ r => CallRel .DurationSince args r ⦄ := by
  unfold ext.call; ext_cases2
  all_goals first
    | ext_tc
    | (simp only [ext.two_args, ext.dt_duration_since, bind_ok]
       have h := (sub?_eq x y).symm
       cases hc : I64.checked_sub x y <;> simp_all [ext.ext_or_err, CallRel, Result.toSpec, Error.toSpec,
         ExtRes.toSpec, List.toList, Cedar.Spec.call, ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, Ext.toSpec, res, WP.spec_ok,
         Datetime.durationSince] <;> rfl)

theorem call_to_date_correct (args : value.List value.Value) :
    ext.call .ToDate args ⦃ r => CallRel .ToDate args r ⦄ := by
  unfold ext.call; ext_cases1
  all_goals first
    | ext_tc
    | (simp only [ext.one_arg, bind_ok]
       obtain ⟨r, hr, hpost⟩ := spec_ok_exists (dt_to_date_correct x)
       rw [hr]; simp only [bind_ok]
       have hl := hpost.symm
       cases r <;> simp_all [ext.ext_or_err, CallRel, Result.toSpec, Error.toSpec, ExtRes.toSpec,
         Ext.toSpec, List.toList, Cedar.Spec.call, ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, res, WP.spec_ok] <;> rfl)

theorem call_to_time_correct (args : value.List value.Value) :
    ext.call .ToTime args ⦃ r => CallRel .ToTime args r ⦄ := by
  unfold ext.call; ext_cases1
  all_goals first
    | ext_tc
    | (simp only [ext.one_arg, bind_ok]
       obtain ⟨r, hr, hpost⟩ := spec_ok_exists (dt_to_time_correct x)
       rw [hr]; simp only [bind_ok]
       simp only [CallRel, Result.toSpec, ExtRes.toSpec, Ext.toSpec, List.toList, Cedar.Spec.call,
         ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, WP.spec_ok, List.map, hpost])

theorem call_duration_conv_correct (f : ext.ExtFun)
    (hf : f = .ToMilliseconds ∨ f = .ToSeconds ∨ f = .ToMinutes ∨ f = .ToHours ∨ f = .ToDays)
    (args : value.List value.Value) :
    ext.call f args ⦃ r => CallRel f args r ⦄ := by
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> unfold ext.call <;> ext_cases1
  all_goals first
    | ext_tc
    | (simp only [ext.call_duration_conv, ext.one_arg, bind_ok]
       step*
       simp only [CallRel, Result.toSpec, ExtRes.toSpec, Ext.toSpec, List.toList, Cedar.Spec.call,
         ExtFun.toSpec, Value.toSpec, Values.toSpec, Prim.toSpec, WP.spec_ok, List.map]
       first
         | rfl
         | (congr 3; done)
         | (congr 3
            apply i64_eq_of_toInt
            first
              | (rw [toSeconds_toInt]; simp_all)
              | (rw [toMinutes_toInt]; simp_all)
              | (rw [toHours_toInt]; simp_all)
              | (rw [toDays_toInt]; simp_all)))

/-- The model's extension functions compute Lean's `Cedar.Spec.call`. -/
public theorem call_correct (f : ext.ExtFun) (args : value.List value.Value)
    :
    ext.call f args ⦃ r => Result.toSpec ExtRes.toSpec r =
      Cedar.Spec.call (ExtFun.toSpec f) (Values.toSpec args) ⦄ := by
  cases f
  · exact call_string_correct _ (by simp) args
  · exact call_decimal_cmp_correct _ (by simp) args
  · exact call_decimal_cmp_correct _ (by simp) args
  · exact call_decimal_cmp_correct _ (by simp) args
  · exact call_decimal_cmp_correct _ (by simp) args
  · exact call_string_correct _ (by simp) args
  · exact call_ip_pred_correct _ (by simp) args
  · exact call_ip_pred_correct _ (by simp) args
  · exact call_ip_pred_correct _ (by simp) args
  · exact call_ip_pred_correct _ (by simp) args
  · exact call_in_range_correct args
  · exact call_string_correct _ (by simp) args
  · exact call_string_correct _ (by simp) args
  · exact call_offset_correct args
  · exact call_duration_since_correct args
  · exact call_to_date_correct args
  · exact call_to_time_correct args
  · exact call_duration_conv_correct _ (by simp) args
  · exact call_duration_conv_correct _ (by simp) args
  · exact call_duration_conv_correct _ (by simp) args
  · exact call_duration_conv_correct _ (by simp) args
  · exact call_duration_conv_correct _ (by simp) args

/-! ## Equality and order -/

/-- Equality of model extension values is equality of their translations. -/
public theorem ext_eq_correct (a b : ext.Ext) :
    ext.ext_eq a b ⦃ r => r = decide (Ext.toSpec a = Ext.toSpec b) ⦄ := by
  rw [ext_eq_ok]; simp [WP.spec_ok]

/-- The order of model extension values is Lean's `Ext.lt` on their translations. -/
public theorem ext_lt_correct (a b : ext.Ext) :
    ext.ext_lt a b ⦃ r => r = Cedar.Spec.Ext.lt (Ext.toSpec a) (Ext.toSpec b) ⦄ := by
  rw [ext_lt_ok]; simp [WP.spec_ok]

/-- `ext_wf` decides `Ext.WF`. -/
public theorem ext_wf_correct (a : ext.Ext) : ext.ext_wf a ⦃ r => (r = true ↔ Ext.WF a) ⦄ := by
  unfold ext.ext_wf
  rcases a with _ | (_ | _) | _ | _ <;> simp [WP.spec_ok, Ext.WF] <;> scalar_tac

end CedarRustModel
