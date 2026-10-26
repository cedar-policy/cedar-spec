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

public import CedarRustModel.Ext.Datetime
public import Cedar.Thm.Ext.Datetime
import all Cedar.Spec.Ext.Datetime
import all Cedar.Spec.Ext.Util
import all Cedar.Thm.Data.String
import all Cedar.Thm.Ext.Datetime.Grammar
import all Cedar.Data.Int64

/-! `XL.parseDatetime` (the shadow of the model's datetime parser) is Lean's
`Datetime.parse`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.deprecated false

namespace CedarRustModel.XL

open Cedar.Spec.Ext Cedar.Thm String
open Cedar.Thm.Datetime (DateComponents TimeComponents OffsetComponents Zone TimePart
  DatetimeComponents IsDatetimeValue DatetimeProduction IsWfDatetime epochDays parse_sound
  parse_complete parse_eq_none_iff wf_iff_exists_value)

section

/-! ## Matchers -/

theorem takeDigits_some {n : Nat} {l a b : List Char} (h : takeDigits n l = some (a, b)) :
    l = a ++ b ∧ a.length = n ∧ allDigits a = true := by
  unfold takeDigits at h
  split at h
  · rename_i hc; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(List.take_append_drop n l).symm, by simp; omega, hc.2⟩
  · simp at h

theorem takeDigits_append {n : Nat} {a b : List Char} (hn : a.length = n) (ha : allDigits a = true) :
    takeDigits n (a ++ b) = some (a, b) := by
  subst hn; simp [takeDigits, ha]

theorem takeDigits_self {n : Nat} {a : List Char} (hn : a.length = n) (ha : allDigits a = true) :
    takeDigits n a = some (a, []) := by
  simpa using takeDigits_append (b := []) hn ha

theorem takeChar_some {c : Char} {l r : List Char} (h : takeChar c l = some r) : l = c :: r := by
  cases l with
  | nil => simp [takeChar] at h
  | cons d l =>
    simp only [takeChar] at h
    split at h
    · simp_all
    · simp at h

theorem takeChar_cons (c : Char) (r : List Char) : takeChar c (c :: r) = some r := by
  simp [takeChar]

theorem takeChar_ne {c : Char} {l : List Char} (h : l.head? ≠ some c) : takeChar c l = none := by
  cases l with
  | nil => rfl
  | cons d l => simp only [List.head?_cons, ne_eq, Option.some.injEq] at h; simp [takeChar, h]

/-! ## Digits -/

theorem fixed_digits (s : String) (n : Nat) (hn : 0 < n) :
    IsFixedDigits n s ↔ s.toList.length = n ∧ allDigits s.toList = true := by
  simp only [IsFixedDigits, IsDigits, allDigits, List.all_eq_true, ← String.length_toList]
  constructor
  · rintro ⟨⟨_, h⟩, rfl⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨⟨hn, h⟩, rfl⟩

theorem smallNat_eq {l : List Char} (hd : allDigits l = true) (hl : 0 < l.length ∧ l.length ≤ 4) :
    smallNat l = natOf (String.ofList l) := by
  have hne : l ≠ [] := by intro h; subst h; simp at hl
  have hlt := Nat.lt_of_lt_of_le (digitsVal_lt l hd) (Nat.pow_le_pow_right (by omega) hl.2)
  norm_num at hlt
  rw [natOf_ofList l ⟨hne, hd⟩]
  unfold smallNat
  rw [digU64_eq 0 l (by scalar_tac), if_pos ⟨hd, by rw [U64_max_eq]; omega⟩]
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [if_pos (by omega)]

/-! ## Constraints and values -/

theorem isLeapYear_eq (y : Nat) : XL.isLeapYear (y : Int) = Cedar.Thm.Datetime.isLeapYear y := by
  have h0 : (0 : Int) ≤ y := by omega
  simp only [XL.isLeapYear, Cedar.Thm.Datetime.isLeapYear, Int.tmod_eq_emod_of_nonneg h0]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq]
  omega

theorem daysInMonth_eq (y m : Nat) :
    XL.daysInMonth (y : Int) (m : Int) = (Cedar.Thm.Datetime.daysInMonth y m : Int) := by
  simp only [XL.daysInMonth, Cedar.Thm.Datetime.daysInMonth, isLeapYear_eq]
  split_ifs <;> simp_all <;> omega

theorem validDate_eq (y m d : Nat) :
    XL.validDate (y : Int) (m : Int) (d : Int) = true ↔
      1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ Cedar.Thm.Datetime.daysInMonth y m := by
  simp only [XL.validDate, daysInMonth_eq, decide_eq_true_eq]; omega

theorem daysFromCivil_eq (y m d : Nat) :
    XL.daysFromCivil (y : Int) (m : Int) (d : Int) = epochDays y m d := by
  simp only [XL.daysFromCivil, epochDays]
  split_ifs <;> simp only [Int.add_neg_eq_sub] at * <;> simp_all <;> omega

/-! ## Renderings -/

def msList : Option String → List Char
  | none => []
  | some sss => '.' :: sss.toList

def zoneList : Zone → List Char
  | .utc => ['Z']
  | .offset o => (if o.negative then '-' else '+') :: (o.hours.toList ++ o.minutes.toList)

def timeList (tp : TimePart) : List Char :=
  'T' :: (tp.time.hours.toList ++ ':' :: (tp.time.minutes.toList ++ ':' ::
    (tp.time.seconds.toList ++ (msList tp.millis ++ zoneList tp.zone))))

def dateList (d : DateComponents) (rest : List Char) : List Char :=
  d.year.toList ++ '-' :: (d.month.toList ++ '-' :: (d.day.toList ++ rest))

theorem toList_zone (z : Zone) : z.asString.toList = zoneList z := by
  cases z with
  | utc => rfl
  | offset o => cases h : o.negative <;> simp [Zone.asString, OffsetComponents.asString, zoneList, h]

theorem toList_timePart (tp : TimePart) : tp.asString.toList = timeList tp := by
  simp only [TimePart.asString, TimeComponents.asString, String.toList_append, timeList, ← toList_zone]
  cases tp.millis <;> simp [msList]

theorem toList_datetime (c : DatetimeComponents) :
    c.asString.toList = dateList c.date (match c.time with | none => [] | some tp => timeList tp) := by
  simp only [DatetimeComponents.asString, DateComponents.asString, String.toList_append, dateList]
  cases c.time <;> simp [toList_timePart]

theorem matchDate_dateList (d : DateComponents) (h : d.syntaxWf) (rest : List Char) :
    matchDate (dateList d rest) = some (d.year.toList, d.month.toList, d.day.toList, rest) := by
  obtain ⟨hy, hm, hd⟩ := h
  rw [fixed_digits _ _ (by omega)] at hy hm hd
  simp only [matchDate, dateList, takeDigits_append hy.1 hy.2, takeChar_cons,
    takeDigits_append hm.1 hm.2, takeDigits_append hd.1 hd.2]

/-- The offset that `matchOffset` reads from a rendered zone -/
def zoneOff : Zone → Option (Bool × List Char × List Char)
  | .utc => none
  | .offset o => some (!o.negative, o.hours.toList, o.minutes.toList)

theorem matchOffset_zoneList (z : Zone) (h : z.syntaxWf) :
    matchOffset (zoneList z) = some (zoneOff z) := by
  cases z with
  | utc => simp [zoneList, matchOffset, zoneOff]
  | offset o =>
    obtain ⟨hh, hm⟩ := h
    rw [fixed_digits _ _ (by omega)] at hh hm
    cases hn : o.negative <;>
      simp [zoneList, matchOffset, zoneOff, hn, takeDigits_append hh.1 hh.2,
        takeDigits_self hm.1 hm.2]

theorem zoneList_head (z : Zone) : (zoneList z).head? ≠ some '.' := by
  cases z with
  | utc => simp [zoneList]
  | offset o => cases h : o.negative <;> simp [zoneList, h]

theorem offsetDelta_zoneOff (z : Zone) (h : z.syntaxWf) (hc : z.constraintsWf) :
    offsetDelta (zoneOff z) = some (-z.offsetSeconds) := by
  cases z with
  | utc => simp [zoneOff, offsetDelta, Zone.offsetSeconds]
  | offset o =>
    obtain ⟨hh, hm⟩ := h
    obtain ⟨ch, cm⟩ := hc
    rw [fixed_digits _ _ (by omega)] at hh hm
    have e1 := smallNat_eq hh.2 (by omega)
    have e2 := smallNat_eq hm.2 (by omega)
    simp only [String.ofList_toList] at e1 e2
    simp only [zoneOff, offsetDelta, e1, e2, Zone.offsetSeconds, OffsetComponents.seconds]
    cases o.negative <;> simp <;> omega

def millisVal : Option String → Int
  | none => 0
  | some sss => natOf sss

theorem optSmallNat_millis (m : Option String) (h : Cedar.Thm.Datetime.IsWfOptionalMillis m) :
    optSmallNat (m.map String.toList) = millisVal m := by
  cases m with
  | none => rfl
  | some sss =>
    have := (fixed_digits _ _ (by omega)).1 h
    have e := smallNat_eq this.2 (by omega)
    simp only [String.ofList_toList] at e
    simp [optSmallNat, millisVal, e]

theorem timeList_ne_nil (tp : TimePart) : timeList tp ≠ [] := by simp [timeList]

theorem parseTime_timeList (tp : TimePart) (h : tp.syntaxWf) (hc : tp.constraintsWf) :
    parseTime (timeList tp) = some tp.toMillis := by
  obtain ⟨⟨hh, hmi, hs⟩, hms, hz⟩ := h
  obtain ⟨⟨ch, cmi, cs⟩, cz⟩ := hc
  rw [fixed_digits _ _ (by omega)] at hh hmi hs
  have hmz := matchOffset_zoneList tp.zone hz
  have hMs : matchMsOffset (msList tp.millis ++ zoneList tp.zone) =
      some (tp.millis.map String.toList, zoneOff tp.zone) := by
    cases hm : tp.millis with
    | none => simp [matchMsOffset, msList, takeChar_ne (zoneList_head _), hmz]
    | some sss =>
      rw [hm] at hms
      have := (fixed_digits _ _ (by omega)).1 hms
      simp [matchMsOffset, msList, takeChar_cons, takeDigits_append this.1 this.2, hmz]
  have e1 := smallNat_eq hh.2 (by omega)
  have e2 := smallNat_eq hmi.2 (by omega)
  have e3 := smallNat_eq hs.2 (by omega)
  simp only [String.ofList_toList] at e1 e2 e3
  simp only [parseTime, timeList, matchHms, takeChar_cons, takeDigits_append hh.1 hh.2,
    takeDigits_append hmi.1 hmi.2, takeDigits_append hs.1 hs.2, hMs,
    offsetDelta_zoneOff _ hz cz, e1, e2, e3, optSmallNat_millis _ hms]
  rw [if_pos (by omega)]
  unfold TimePart.toMillis
  simp only [Option.some.injEq]
  split <;> simp_all [millisVal] <;> ring

/-! ## Completeness -/

theorem parseDatetime_complete (c : DatetimeComponents) (hs : c.syntaxWf) (hc : c.constraintsWf) :
    parseDatetime c.asString.toList = some c.toMillis := by
  rw [toList_datetime]
  obtain ⟨hsd, hst⟩ := hs
  obtain ⟨hcd, hct⟩ := hc
  have hsd' := hsd
  obtain ⟨hy, hm, hd⟩ := hsd'
  rw [fixed_digits _ _ (by omega)] at hy hm hd
  have ey := smallNat_eq hy.2 (by omega)
  have em := smallNat_eq hm.2 (by omega)
  have ed := smallNat_eq hd.2 (by omega)
  simp only [String.ofList_toList] at ey em ed
  have hv : XL.validDate (natOf c.date.year : Int) (natOf c.date.month : Int) (natOf c.date.day : Int) = true :=
    (validDate_eq _ _ _).2 (by simpa [DateComponents.constraintsWf] using hcd)
  unfold parseDatetime
  rw [matchDate_dateList _ hsd]
  simp only [ey, em, ed, hv, daysFromCivil_eq, DatetimeComponents.toMillis, DateComponents.toMillis]
  cases ht : c.time with
  | none => simp
  | some tp =>
    rw [ht] at hst hct
    simp [timeList_ne_nil, parseTime_timeList tp hst hct]

/-! ## Soundness -/

theorem matchDate_some {l y m d rest : List Char} (h : matchDate l = some (y, m, d, rest)) :
    l = y ++ '-' :: (m ++ '-' :: (d ++ rest)) ∧ IsFixedDigits 4 (String.ofList y) ∧
      IsFixedDigits 2 (String.ofList m) ∧ IsFixedDigits 2 (String.ofList d) := by
  unfold matchDate at h
  split at h; · simp at h
  rename_i y' r1 h1
  split at h; · simp at h
  rename_i r2 h2
  split at h; · simp at h
  rename_i m' r3 h3
  split at h; · simp at h
  rename_i r4 h4
  split at h; · simp at h
  rename_i d' r5 h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨e1, l1, a1⟩ := takeDigits_some h1
  obtain ⟨e3, l3, a3⟩ := takeDigits_some h3
  obtain ⟨e5, l5, a5⟩ := takeDigits_some h5
  have e2 := takeChar_some h2
  have e4 := takeChar_some h4
  refine ⟨by simp_all, ?_, ?_, ?_⟩ <;>
    rw [fixed_digits _ _ (by omega)] <;> simp_all

theorem matchHms_some {l h mi sec rest : List Char} (hm : matchHms l = some (h, mi, sec, rest)) :
    l = 'T' :: (h ++ ':' :: (mi ++ ':' :: (sec ++ rest))) ∧ IsFixedDigits 2 (String.ofList h) ∧
      IsFixedDigits 2 (String.ofList mi) ∧ IsFixedDigits 2 (String.ofList sec) := by
  unfold matchHms at hm
  split at hm; · simp at hm
  rename_i r0 h0
  split at hm; · simp at hm
  rename_i h' r1 h1
  split at hm; · simp at hm
  rename_i r2 h2
  split at hm; · simp at hm
  rename_i m' r3 h3
  split at hm; · simp at hm
  rename_i r4 h4
  split at hm; · simp at hm
  rename_i s' r5 h5
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
  obtain ⟨e1, l1, a1⟩ := takeDigits_some h1
  obtain ⟨e3, l3, a3⟩ := takeDigits_some h3
  obtain ⟨e5, l5, a5⟩ := takeDigits_some h5
  have e0 := takeChar_some h0
  have e2 := takeChar_some h2
  have e4 := takeChar_some h4
  refine ⟨by simp_all, ?_, ?_, ?_⟩ <;>
    rw [fixed_digits _ _ (by omega)] <;> simp_all

/-- The zone read by `matchOffset` -/
def offZone : Option (Bool × List Char × List Char) → Zone
  | none => .utc
  | some (pos, hh, mm) => .offset ⟨!pos, String.ofList hh, String.ofList mm⟩

theorem matchOffset_some {l : List Char} {off : Option (Bool × List Char × List Char)}
    (h : matchOffset l = some off) :
    l = zoneList (offZone off) ∧ (offZone off).syntaxWf := by
  unfold matchOffset at h
  split at h; · simp at h
  rename_i c rest
  split at h
  · rename_i hc
    split at h
    · rename_i hr; simp only [Option.some.injEq] at h; subst h hc hr
      simp [offZone, zoneList, Zone.syntaxWf]
    · simp at h
  · split at h
    · rename_i _ hpm
      split at h; · simp at h
      rename_i hh r1 h1
      split at h; · simp at h
      rename_i mm r2 h2
      split at h
      · rename_i hr2
        simp only [Option.some.injEq] at h
        subst h hr2
        obtain ⟨e1, l1, a1⟩ := takeDigits_some h1
        obtain ⟨e2, l2, a2⟩ := takeDigits_some h2
        refine ⟨?_, ?_⟩
        · rcases hpm with rfl | rfl <;> simp_all [offZone, zoneList]
        · simp only [offZone, Zone.syntaxWf, OffsetComponents.syntaxWf]
          rw [fixed_digits _ _ (by omega), fixed_digits _ _ (by omega)]
          simp_all
      · simp at h
    · simp at h

theorem matchMsOffset_some {l : List Char} {ms : Option (List Char)} {off : Option (Bool × List Char × List Char)}
    (h : matchMsOffset l = some (ms, off)) :
    l = msList (ms.map String.ofList) ++ zoneList (offZone off) ∧ (offZone off).syntaxWf ∧
      Cedar.Thm.Datetime.IsWfOptionalMillis (ms.map String.ofList) := by
  unfold matchMsOffset at h
  split at h
  · rename_i r0 h0
    split at h; · simp at h
    rename_i ms' r1 h1
    cases ho : matchOffset r1 with
    | none => simp [ho] at h
    | some off' =>
      simp only [ho, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e1, l1, a1⟩ := takeDigits_some h1
      obtain ⟨z1, z2⟩ := matchOffset_some ho
      refine ⟨?_, z2, ?_⟩
      · rw [takeChar_some h0, e1, z1]; simp [msList]
      · simp only [Option.map_some, Cedar.Thm.Datetime.IsWfOptionalMillis]
        rw [fixed_digits _ _ (by omega)]; simp_all
  · rename_i h0
    cases ho : matchOffset l with
    | none => simp [ho] at h
    | some off' =>
      simp only [ho, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨z1, z2⟩ := matchOffset_some ho
      exact ⟨by simp [msList, ← z1], z2, trivial⟩

theorem smallNat_fixed {l : List Char} {n : Nat} (h : IsFixedDigits n (String.ofList l))
    (hn : 0 < n ∧ n ≤ 4) : smallNat l = natOf (String.ofList l) := by
  have := (fixed_digits _ _ hn.1).1 h
  simp only [String.toList_ofList] at this
  exact smallNat_eq this.2 (by omega)

theorem offsetDelta_some {off : Option (Bool × List Char × List Char)} {dl : Int}
    (h : offsetDelta off = some dl) (hs : (offZone off).syntaxWf) : (offZone off).constraintsWf := by
  cases off with
  | none => trivial
  | some p =>
    obtain ⟨pos, hh, mm⟩ := p
    obtain ⟨fh, fm⟩ := hs
    simp only [offsetDelta] at h
    split at h
    · rename_i hc
      rw [smallNat_fixed fh (by omega), smallNat_fixed fm (by omega)] at hc
      simp only [offZone, Zone.constraintsWf, OffsetComponents.constraintsWf]
      omega
    · simp at h

theorem parseDatetime_sound {l : List Char} {v : Int} (h : parseDatetime l = some v) :
    IsWfDatetime (String.ofList l) := by
  unfold parseDatetime at h
  split at h; · simp at h
  rename_i ys mos ds rest hmd
  obtain ⟨hl, fy, fm, fd⟩ := matchDate_some hmd
  rw [smallNat_fixed fy (by omega), smallNat_fixed fm (by omega), smallNat_fixed fd (by omega)] at h
  split at h; · simp at h
  rename_i hv
  simp only [Bool.not_eq_true, Bool.not_eq_false, not_not] at hv
  have hcd := (validDate_eq _ _ _).1 hv
  have hdate : DateComponents.syntaxWf ⟨String.ofList ys, String.ofList mos, String.ofList ds⟩ :=
    ⟨fy, fm, fd⟩
  have hdc : DateComponents.constraintsWf ⟨String.ofList ys, String.ofList mos, String.ofList ds⟩ := by
    simpa [DateComponents.constraintsWf] using hcd
  split at h
  · rename_i hr
    subst hr
    refine ⟨⟨⟨String.ofList ys, String.ofList mos, String.ofList ds⟩, none⟩, ⟨hdate, trivial⟩,
      ⟨hdc, trivial⟩, ?_⟩
    apply String.toList_inj.mp
    rw [toList_datetime]
    simp [dateList, hl]
  · split at h; · simp at h
    rename_i t ht
    unfold parseTime at ht
    split at ht; · simp at ht
    rename_i hs mis ss rest2 hmh
    obtain ⟨hr1, fh, fmi, fs⟩ := matchHms_some hmh
    split at ht; · simp at ht
    rename_i msopt off hmo
    obtain ⟨hr2, fz, fms⟩ := matchMsOffset_some hmo
    split at ht; · simp at ht
    rename_i dl hdl
    have zc := offsetDelta_some hdl fz
    split at ht
    · rename_i hc
      rw [smallNat_fixed fh (by omega), smallNat_fixed fmi (by omega), smallNat_fixed fs (by omega)] at hc
      refine ⟨⟨⟨String.ofList ys, String.ofList mos, String.ofList ds⟩,
        some ⟨⟨String.ofList hs, String.ofList mis, String.ofList ss⟩, msopt.map String.ofList, offZone off⟩⟩,
        ⟨hdate, ⟨fh, fmi, fs⟩, fms, fz⟩, ⟨hdc, ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩, zc⟩, ?_⟩
      apply String.toList_inj.mp
      rw [toList_datetime]
      simp [dateList, timeList, hl, hr1, hr2]
    · simp at ht

public theorem parseDatetime_eq (l : List Char) :
    parseDatetime l = (Datetime.parse (String.ofList l)).map (fun d => d.val.toInt) := by
  cases hp : Datetime.parse (String.ofList l) with
  | some d =>
    obtain ⟨c, ⟨hs, hc, hstr⟩, hv⟩ := parse_sound _ d hp
    have hl : l = c.asString.toList := by rw [← hstr]; simp
    rw [hl, parseDatetime_complete c hs hc, ← hv]; rfl
  | none =>
    cases hq : parseDatetime l with
    | none => rfl
    | some v => exact absurd (parseDatetime_sound hq) ((parse_eq_none_iff _).1 hp)

end

end CedarRustModel.XL
