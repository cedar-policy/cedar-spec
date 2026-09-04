module

public import Cedar.Data.Int64
public import Cedar.Spec.Ext.Datetime
public import Cedar.Thm.Ext.Duration.Grammar

import all Cedar.Thm.Ext.Duration.Grammar
import all Cedar.Thm.Ext.Duration.Lemmas

/-!
Duration parser theorem surface.

`parse_eq_none_iff` characterizes exactly when parsing rejects a string.
`parse_sound` and `parse_complete` state the parser soundness and completeness
properties against `IsWfDuration` and `computeValue`.
-/

namespace Cedar.Thm.Duration
open Cedar.Spec.Ext
open Datetime

/-- Failure characterization for `Duration.parse`: parsing rejects exactly strings that are
    not well-formed or whose computed value overflows the `Int64` range. -/
public theorem parse_eq_none_iff (str : String) :
    Duration.parse str = none ↔
    ¬ IsWfDuration str ∨
      ∃ v, computeValue str = some v ∧ (v < Int64.MIN ∨ v > Int64.MAX) := by
  cases hsign : isNegativeDuration str with
  | mk isNegative body =>
    have hwf := wf_str_iff_signed_body str
    simp only [hsign] at hwf
    have hcv : computeValue str = computeSignedBodyValue isNegative body := by
      unfold computeValue; rw [hsign]
    by_cases hwfstr : IsWfDuration str
    · -- Well-formed: `computeValue` is defined and equals its total mirror, so the failure is
      -- purely the overflow condition on `computeSignedBodyValueD`.
      have hbody : IsWfBody body := hwf.mp hwfstr
      have hcvD : computeValue str = some (computeSignedBodyValueD isNegative body) := by
        rw [hcv]; exact computeSignedBodyValue_eq_some_D_of_wf isNegative body hbody
      unfold Duration.parse; rw [hsign, parseDuration?_eq_none_iff]
      constructor
      · intro h
        rcases h with hnb | hovf
        · exact absurd hbody hnb
        · exact Or.inr ⟨_, hcvD, hovf⟩
      · intro h
        rcases h with hns | ⟨v, hv, hovf⟩
        · exact absurd hwfstr hns
        · right; rw [hcvD] at hv; cases hv; exact hovf
    · -- Not well-formed: parsing always rejects, and the `¬ IsWfDuration` disjunct holds.
      constructor
      · intro _; exact Or.inl hwfstr
      · intro _
        unfold Duration.parse; rw [hsign]
        exact parseDuration?_none_of_not_wf isNegative body (fun hb => hwfstr (hwf.mpr hb))

/-- A well-formed duration string always has a computed value. Proved from well-formedness: every
    component of a well-formed body parses, so `computeBodyValue` never short-circuits to `none`. -/
public theorem computeValue_isSome_of_isWfDuration {str : String} (hwf : IsWfDuration str) :
    (computeValue str).isSome = true := by
  cases hsign : isNegativeDuration str with
  | mk isNegative body =>
    have hwfb := (wf_str_iff_signed_body str).mp hwf
    simp only [hsign] at hwfb
    have hcv : computeValue str = computeSignedBodyValue isNegative body := by
      unfold computeValue; rw [hsign]
    rw [hcv, computeSignedBodyValue_eq_some_D_of_wf isNegative body hwfb]; rfl

/-- Core completeness of `Duration.parse`: if a string is well-formed with computed value `some v`,
    then parsing agrees with `duration?` applied to `v`. -/
public theorem parse_eq_duration?_of_wf (str : String) (v : Int) (hwf : IsWfDuration str)
    (hval : computeValue str = some v) :
    Duration.parse str = duration? v := by
  unfold Duration.parse
  cases hsign : isNegativeDuration str with
  | mk isNegative body =>
    have hbody : IsWfBody body := by
      have h := (wf_str_iff_signed_body str).mp hwf
      simp [hsign] at h
      exact h
    have hcvD : computeValue str = some (computeSignedBodyValueD isNegative body) := by
      unfold computeValue; rw [hsign]
      exact computeSignedBodyValue_eq_some_D_of_wf isNegative body hbody
    have hv : v = computeSignedBodyValueD isNegative body := by
      rw [hcvD] at hval; cases hval; rfl
    rw [hv]
    exact parseDuration?_eq_duration?_of_wf isNegative body hbody

/-- Soundness of `Duration.parse`: if parsing succeeds, then the input is well-formed and
    `computeValue` yields exactly the returned duration's value. (The value is automatically in
    `Int64` range, since `d.val : Int64`, so no range conjunct is stated.) -/
public theorem parse_sound (str : String) (d : Duration)
    (h : Duration.parse str = some d) :
    IsWfDuration str ∧ computeValue str = some d.val.toInt := by
  have hwf : IsWfDuration str := by
    by_contra hnot
    have hnone := (parse_eq_none_iff str).mpr (Or.inl hnot)
    rw [h] at hnone
    contradiction
  obtain ⟨v, hval⟩ := Option.isSome_iff_exists.mp (computeValue_isSome_of_isWfDuration hwf)
  have hsome : duration? v = some d := by
    rw [← parse_eq_duration?_of_wf str v hwf hval]
    exact h
  have hvd : d.val.toInt = v := duration?_some_toInt v d hsome
  rw [hval, hvd]
  exact ⟨hwf, rfl⟩

/-- Completeness of `Duration.parse`: if a string is well-formed and its computed value matches
    `d.val.toInt`, then parsing accepts the string as `d`. -/
public theorem parse_complete (str : String) (d : Duration)
    (hwf : IsWfDuration str) (hval : computeValue str = some d.val.toInt) :
    Duration.parse str = some d := by
  rw [parse_eq_duration?_of_wf str d.val.toInt hwf hval]
  exact duration?_of_val_toInt d

/-- Parsing a negated duration string negates the underlying value. -/
public theorem parse_neg (s : String) (d : Duration)
    (hpos : ¬ s.startsWith "-")
    (h : Duration.parse s = some d) :
    Duration.parse ("-" ++ s) = duration? (-d.val.toInt) := by
  have hfront : s.front ≠ '-' := by
    intro hf
    have hs : s = "-" ++ (s.drop 1).copy :=
      string_eq_dash_append_drop_one_of_front_eq_dash s hf
    have hstarts : s.startsWith "-" = true := by
      rw [hs]
      simp
    exact hpos hstarts
  have hs_pos : isNegativeDuration s = (false, s) := by
    unfold isNegativeDuration
    split
    · contradiction
    · rfl
  have hs_neg : isNegativeDuration ("-" ++ s) = (true, s) := by
    unfold isNegativeDuration
    rw [dash_append_front_eq_dash]
    simp [dash_append_drop_one_copy]
  unfold Duration.parse at h ⊢
  simp [hs_pos] at h
  simp [hs_neg]
  have hwf : IsWfBody s := wf_of_parseDuration?_eq_some false s d h
  rw [parseDuration?_eq_duration?_of_wf true s hwf]
  rw [parseDuration?_eq_duration?_of_wf false s hwf] at h
  unfold computeSignedBodyValueD at h ⊢
  simp at h ⊢
  have hvalue : d.val.toInt = computeBodyValueD s :=
    duration?_some_toInt (computeBodyValueD s) d h
  rw [← hvalue]

/-- `offset` and `durationSince` are inverses: adding a duration then computing
    the difference gives back the same duration. -/
public theorem offset_durationSince_inverse (dt : Datetime) (dur : Duration) (dt' : Datetime)
    (h : offset dt dur = some dt') :
    durationSince dt' dt = some dur := by
  unfold offset at h
  unfold durationSince
  cases h_add : Int64.add? dt.val dur.val with
  | none =>
    simp [h_add] at h
  | some i =>
    simp [h_add] at h
    subst h
    rw [Int64.sub?_add?_inverse dt.val dur.val i h_add]
    rfl

/-- `parse ∘ toString` roundtrip: parsing the string representation recovers the original. -/
public theorem parse_toString_roundtrip (d : Duration) :
    Duration.parse (Duration.toString d) = some d := by
  let totalMs := d.val.toInt.natAbs
  let days := totalMs / MILLISECONDS_PER_DAY.toNat
  let rem₁ := totalMs % MILLISECONDS_PER_DAY.toNat
  let hours := rem₁ / MILLISECONDS_PER_HOUR.toNat
  let rem₂ := rem₁ % MILLISECONDS_PER_HOUR.toNat
  let minutes := rem₂ / MILLISECONDS_PER_MINUTE.toNat
  let rem₃ := rem₂ % MILLISECONDS_PER_MINUTE.toNat
  let seconds := rem₃ / MILLISECONDS_PER_SECOND.toNat
  let ms := rem₃ % MILLISECONDS_PER_SECOND.toNat
  let body := canonicalBody days hours minutes seconds ms
  have hbody_wf : IsWfBody body := canonicalDurationBody_wf days hours minutes seconds ms
  have hbody_value :
      computeBodyValueD body =
        (days : Int) * MILLISECONDS_PER_DAY +
        (hours : Int) * MILLISECONDS_PER_HOUR +
        (minutes : Int) * MILLISECONDS_PER_MINUTE +
        (seconds : Int) * MILLISECONDS_PER_SECOND +
        (ms : Int) := by
    have h1 : computeBodyValue body = some ((days : Int) * MILLISECONDS_PER_DAY +
        (hours : Int) * MILLISECONDS_PER_HOUR + (minutes : Int) * MILLISECONDS_PER_MINUTE +
        (seconds : Int) * MILLISECONDS_PER_SECOND + (ms : Int)) :=
      canonicalDurationBody_value days hours minutes seconds ms
    rw [computeBodyValue_eq_some_D_of_wf body hbody_wf] at h1
    injection h1 with h1'
  have hparts :
      (days : Int) * MILLISECONDS_PER_DAY +
        (hours : Int) * MILLISECONDS_PER_HOUR +
        (minutes : Int) * MILLISECONDS_PER_MINUTE +
        (seconds : Int) * MILLISECONDS_PER_SECOND +
        (ms : Int) = (totalMs : Int) := by
    dsimp [days, hours, minutes, seconds, ms, rem₁, rem₂, rem₃]
    exact durationParts_value_int totalMs
  have htoString :
      Duration.toString d = if d.val < 0 then "-" ++ body else body := by
    simp [Duration.toString, body, canonicalBody, durationComponent,
      Datetime.durationComponent, days, hours, minutes, seconds, ms, rem₁, rem₂,
      rem₃, totalMs]
  rw [htoString]
  unfold Duration.parse
  by_cases hneg : d.val < 0
  · simp [hneg, isNegativeDuration_neg_body]
    rw [parseDuration?_eq_duration?_of_wf true body hbody_wf]
    unfold computeSignedBodyValueD
    rw [hbody_value, hparts]
    have htoInt_neg : -((totalMs : Nat) : Int) = d.val.toInt := by
      have hlt : d.val.toInt < 0 := by simpa [Int64.lt_def_toInt] using hneg
      dsimp [totalMs]
      omega
    simp [htoInt_neg]
    exact duration?_of_val_toInt d
  · have hfront : body.front ≠ '-' := duration_body_front_ne_dash body hbody_wf
    simp [hneg, isNegativeDuration_canonical_body body hfront]
    rw [parseDuration?_eq_duration?_of_wf false body hbody_wf]
    unfold computeSignedBodyValueD
    rw [hbody_value, hparts]
    have htoInt_nonneg : ((totalMs : Nat) : Int) = d.val.toInt := by
      have hle : ¬ d.val.toInt < 0 := by
        intro hlt
        exact hneg (by simpa [Int64.lt_def_toInt] using hlt)
      dsimp [totalMs]
      omega
    simp [htoInt_nonneg]
    exact duration?_of_val_toInt d

/-- `toString` is injective: distinct durations produce distinct strings. -/
public theorem toString_injective (d d' : Duration)
    (h : Duration.toString d = Duration.toString d') :
    d = d' := by
  have h1 := parse_toString_roundtrip d
  have h2 := parse_toString_roundtrip d'
  rw [h] at h1
  rw [h1] at h2
  injection h2

/-- Equal normal form iff equal value: normalization decides duration equality. -/
public theorem normalize_eq_iff_parse_eq (s s' : String) :
    normalize s = normalize s' ↔ Duration.parse s = Duration.parse s' := by
  constructor
  · intro h
    unfold normalize at h
    match hps : Duration.parse s, hps' : Duration.parse s' with
    | .some d, .some d' =>
      simp [hps, hps', Option.map] at h
      exact congrArg _ (toString_injective d d' h)
    | .some d, .none => simp [hps, hps', Option.map] at h
    | .none, .some d' => simp [hps, hps', Option.map] at h
    | .none, .none => rfl
  · intro h
    simp [normalize, h]

end Cedar.Thm.Duration
