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

public import Cedar.Data.Int64
public import Cedar.Spec.Ext.Datetime
public import Cedar.Thm.Ext.Duration.Grammar

import all Cedar.Thm.Ext.Duration.Grammar
import all Cedar.Thm.Ext.Duration.Lemmas

/-!
Duration parser theorem surface.

`parse_sound` and `parse_complete` characterize successful parsing against the declarative
`IsDurationValue` relation. `parse_eq_none_iff` characterizes exactly when parsing rejects.
-/

namespace Cedar.Thm.Duration
open Cedar.Spec.Ext
open Datetime

/-- Completeness of `Duration.parse`: if the grammar assigns `str` the value `d.val.toInt`, then
    parsing accepts the string as `d`. -/
public theorem parse_complete (str : String) (d : Duration)
    (hval : IsDurationValue str d.val.toInt) :
    Duration.parse str = some d := by
  rw [parse_eq_duration?_of_isDurationValue hval]
  exact duration?_of_val_toInt d

/-- Soundness of `Duration.parse`: if parsing succeeds, the declarative grammar relation assigns
    the input exactly the returned duration's value. -/
public theorem parse_sound (str : String) (d : Duration)
    (h : Duration.parse str = some d) :
    IsDurationValue str d.val.toInt := by
  unfold Duration.parse at h
  cases hsign : isNegativeDuration str with
  | mk isNegative body =>
    simp only [hsign] at h
    have hbody : IsWfBody body := wf_of_parseDuration?_eq_some isNegative body d h
    have hwf : IsWfDuration str := by
      apply (wf_str_iff_signed_body str).mpr
      simp [hsign, hbody]
    obtain ⟨v, hval⟩ := isWfDuration_iff_exists_value.mp hwf
    have hparse := parse_eq_duration?_of_isDurationValue hval
    unfold Duration.parse at hparse
    rw [hsign] at hparse
    simp only at hparse
    rw [h] at hparse
    have hdval : d.val.toInt = v := duration?_some_toInt v d hparse.symm
    rw [hdval]
    exact hval

/-- Exact parser characterization: parsing succeeds with `d` precisely when the declarative
    grammar relation assigns the input the value `d.val.toInt`. -/
public theorem parse_eq_some_iff_isDurationValue (str : String) (d : Duration) :
    Duration.parse str = some d ↔ IsDurationValue str d.val.toInt :=
  ⟨parse_sound str d, parse_complete str d⟩

/-- Failure characterization for `Duration.parse`: parsing rejects exactly malformed strings and
    well-formed strings whose grammar value overflows the `Int64` range. -/
public theorem parse_eq_none_iff (str : String) :
    Duration.parse str = none ↔
    ¬ IsWfDuration str ∨
      ∃ v, IsDurationValue str v ∧ (v < Int64.MIN ∨ v > Int64.MAX) := by
  constructor
  · intro h
    by_cases hwf : IsWfDuration str
    · obtain ⟨v, hval⟩ := isWfDuration_iff_exists_value.mp hwf
      rw [parse_eq_duration?_of_isDurationValue hval] at h
      exact Or.inr ⟨v, hval, (duration?_eq_none_iff_overflow v).mp h⟩
    · exact Or.inl hwf
  · rintro (h | ⟨v, hval, hoverflow⟩)
    · by_contra hne
      obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hne
      exact h (isWfDuration_iff_exists_value.mpr ⟨d.val.toInt, parse_sound str d hd⟩)
    · rw [parse_eq_duration?_of_isDurationValue hval]
      exact (duration?_eq_none_iff_overflow v).mpr hoverflow

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
  let body := Datetime.canonicalDurationBody totalMs
  have hbody_wf : IsWfBody body := specCanonicalDurationBody_wf totalMs
  have hbody_value : computeBodyValueD body = (totalMs : Int) :=
    specCanonicalDurationBody_value totalMs
  have htoString :
      Duration.toString d = if d.val < 0 then "-" ++ body else body := by
    simp [Duration.toString, body, totalMs]
  rw [htoString]
  unfold Duration.parse
  by_cases hneg : d.val < 0
  · simp [hneg, isNegativeDuration_neg_body]
    rw [parseDuration?_eq_duration?_of_wf true body hbody_wf]
    unfold computeSignedBodyValueD
    rw [hbody_value]
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
    rw [hbody_value]
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
