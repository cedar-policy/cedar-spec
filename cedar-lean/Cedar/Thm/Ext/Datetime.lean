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

public import Cedar.Thm.Ext.Datetime.Lemmas

import all Cedar.Data.Int64
import all Cedar.Spec.Ext.Datetime
import all Cedar.Spec.Ext.Util
import all Cedar.Thm.Ext.Datetime.Grammar
import all Cedar.Thm.Ext.Datetime.Lemmas

namespace Cedar.Thm.Datetime
open Cedar.Spec.Ext
open Datetime

/-! # Datetime parser correctness

`parse_sound`, `parse_complete`, and `parse_eq_none_iff` characterize parsing against the
grammar-level `IsDatetimeValue` relation. On top of them sit the serialization results —
`parse_toString_roundtrip`, `toString?_injective`, and `normalize_eq_iff_parse_eq` — the datetime
analogues of the decimal and duration surfaces, adapted to the *partial* serializer `toString?`
(datetime rendering only covers the grammar-representable range). The parser-independent
roundtrip lemmas they build on live in `Cedar.Thm.Ext.Datetime.Lemmas`. -/

/-! ## Soundness, completeness, and failure characterization

The theorems below relate `Datetime.parse` to the parser-independent `IsDatetimeValue` relation.
Unlike the decimal and duration parsers — hand-written character manipulation we reason about
directly — `Datetime.parse` delegates to `Std.Time.GenericFormat.parse`, whose field parsers use
well-founded recursion. The bulk of the work is therefore a parser-inversion library (in
`Cedar.Thm.Ext.Datetime.Lemmas`) that symbolically evaluates that recursion once and for all,
showing a successful `Std.Time` parse is exactly the rendering of well-formed witnessing
components. That reduces both soundness and completeness to reasoning about the components, not
about the parser's recursion.

All three are proven with no proof placeholders or custom axioms (`propext`, `Classical.choice`,
`Quot.sound` only). -/

/-- Soundness of `Datetime.parse`: if parsing succeeds, the declarative grammar relation assigns
    the input exactly the returned datetime's value. The value is automatically in `Int64` range,
    since it equals `d.val.toInt` for `d.val : Int64`.

    Idea: read the successful parse backwards to recover the witnessing components, which are
    well-formed by construction, then use the `Std.Time` value bridge to identify their
    `toMillis` denotation with the returned value. -/
public theorem parse_sound (str : String) (d : Datetime)
    (h : Datetime.parse str = some d) :
    IsDatetimeValue str d.val.toInt := by
  -- Read the successful parse backwards: guards passed, the alternation produced `zt`, its offset
  -- was in range, and `datetime? zt`'s epoch-ms value returned `d`. (Pure `Option` reasoning.)
  obtain ⟨_hleap, _hlen, _htz, zt, halt, _hrange, hdt⟩ := parse_some_decompose h
  -- Invert the successful `Std.Time` parse to fully well-formed witnessing components `c`.
  obtain ⟨c, hstr, hsyn, hcon⟩ := wf_of_parse zt _hlen halt
  -- `datetime? v = some d` gives `d.val.toInt = v` (the `Int64.ofInt?` roundtrip).
  have hdval : d.val.toInt = zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt :=
    datetime?_some_toInt _ _ hdt
  -- The alternation's value is `c.toMillis` (the `Std.Time` bridge), so `d.val.toInt = c.toMillis`.
  have hcmillis : c.toMillis = d.val.toInt := by
    have haltval := stdTime_alternation_value hsyn hcon
    rw [← hstr, halt, Option.map_some] at haltval
    have hzt : zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = c.toMillis :=
      Option.some.inj haltval
    omega
  exact ⟨c, hsyn, hcon, hstr, hcmillis.symm⟩

/-- Completeness of `Datetime.parse`: if the grammar assigns a string the value `d.val.toInt`,
    then parsing accepts the string as `d`. Well-formedness is already part of
    `IsDatetimeValue`.

    Idea: the relation gives witnessing components whose rendering is the input. On such a
    rendering every guard passes and the `Std.Time` parse succeeds with the components' value.
    That value is `d`'s, so parsing lands on `d`. -/
public theorem parse_complete (str : String) (d : Datetime)
    (hval : IsDatetimeValue str d.val.toInt) :
    Datetime.parse str = some d := by
  obtain ⟨c, hsyn, hcon, hstr, hvc⟩ := hval
  subst str
  -- The format alternation evaluates to `some c.toMillis`; extract the witnessing `zt`.
  have haltval := stdTime_alternation_value hsyn hcon
  obtain ⟨zt, hzt, hztval⟩ := Option.map_eq_some_iff.mp haltval
  -- The offset-range guard passes.
  have hrange : zt.timezone.offset.second.val.natAbs < MAX_OFFSET_SECONDS :=
    offset_lt_max_of_syntaxWf hsyn hcon zt hzt
  -- Reduce `Datetime.parse` through its three (discharged) guards and the alternation bind.
  unfold Datetime.parse
  rw [dateContainsLeapSeconds_asString hsyn hcon, checkComponentLen_asString hsyn,
    tzOffsetMinsLt60_asString hsyn hcon]
  simp only [Bool.false_eq_true, reduceIte, Bool.not_true]
  simp only [bind, Option.bind, hzt, hrange, ite_eq_left]
  -- Final: `datetime? (zt value) = some d`, since that value is `c.toMillis = d.val.toInt`.
  show datetime? zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = some d
  rw [hztval, ← hvc]
  unfold datetime?
  rw [Int64.ofInt?_toInt d.val]
  simp only [bind, Option.bind, pure]

/-- Exact parser characterization: parsing succeeds with `d` precisely when the declarative
    grammar relation assigns the input the value `d.val.toInt`. -/
public theorem parse_eq_some_iff_isDatetimeValue (str : String) (d : Datetime) :
    Datetime.parse str = some d ↔ IsDatetimeValue str d.val.toInt :=
  ⟨parse_sound str d, parse_complete str d⟩

/-- `parse ∘ toString?` roundtrip: every successfully serialized datetime parses back to the
    original value. -/
public theorem parse_toString_roundtrip {d : Datetime} {str : String}
    (h : toString? d = some str) :
    Datetime.parse str = some d := by
  exact parse_complete str d (toString?_some_value h)

/-- Total `Option` formulation of the partial serialization roundtrip. -/
public theorem bind_parse_toString? (d : Datetime) :
    (toString? d).bind Datetime.parse = (toString? d).map (fun _ => d) := by
  cases h : toString? d with
  | none => rfl
  | some str =>
    simp only [Option.bind_some, Option.map_some]
    exact parse_toString_roundtrip h

/-- `toString?` is injective on the values it serializes: datetimes with the same (defined)
    canonical string are equal. (Partial-serializer analogue of `Decimal`/`Duration`'s
    `toString_injective`.) -/
public theorem toString?_injective {d d' : Datetime} {str : String}
    (h : toString? d = some str) (h' : toString? d' = some str) :
    d = d' := by
  have h1 := parse_toString_roundtrip h
  have h2 := parse_toString_roundtrip h'
  rw [h1] at h2
  exact Option.some.inj h2

/-- Because the grammar bounds years to four digits and zone offsets to `±23:59`, every
    well-formed datetime value fits in `Int64`. Parsing therefore rejects exactly malformed
    strings. -/
public theorem parse_eq_none_iff_not_wf (str : String) :
    Datetime.parse str = none ↔ ¬ IsWfDatetime str := by
  constructor
  · intro hnone
    intro hwf
    obtain ⟨v, hvalue⟩ := isWfDatetime_iff_exists_value.mp hwf
    obtain ⟨components, hsyntax, hconstraints, hstr, hv⟩ := hvalue
    have hrange : Int64.MIN ≤ v ∧ v ≤ Int64.MAX := by
      rw [hv]
      exact toMillis_int64_range hsyntax hconstraints
    have hsome := (Int64.ofInt?_some_iff (i := v)).mp hrange
    have htoInt : (Int64.ofInt v).toInt = v := Int64.ofInt?_some_toInt hsome
    let d : Datetime := ⟨Int64.ofInt v⟩
    have hvalue' : IsDatetimeValue str d.val.toInt := by
      change IsDatetimeValue str (Int64.ofInt v).toInt
      rw [htoInt]
      exact ⟨components, hsyntax, hconstraints, hstr, hv⟩
    have hparse := parse_complete str d hvalue'
    rw [hparse] at hnone
    exact absurd hnone (by simp)
  · intro hnwf
    cases hparse : Datetime.parse str with
    | none => rfl
    | some d =>
      exfalso
      exact hnwf (isWfDatetime_iff_exists_value.mpr
        ⟨d.val.toInt, parse_sound str d hparse⟩)

/-- Failure characterization in the same uniform form as Decimal and Duration: parsing rejects
    malformed strings or well-formed values outside `Int64`. For Datetime the overflow branch is
    impossible by the grammar's four-digit-year and offset bounds. -/
public theorem parse_eq_none_iff (str : String) :
    Datetime.parse str = none ↔
    ¬ IsWfDatetime str ∨
      ∃ v, IsDatetimeValue str v ∧ (v < Int64.MIN ∨ v > Int64.MAX) := by
  rw [parse_eq_none_iff_not_wf]
  constructor
  · exact Or.inl
  · rintro (hnwf | ⟨v, hvalue, hoverflow⟩)
    · exact hnwf
    · exfalso
      obtain ⟨components, hsyntax, hconstraints, _, hv⟩ := hvalue
      have hrange := toMillis_int64_range hsyntax hconstraints
      rw [hv] at hoverflow
      simp only [Int64.MIN, Int64.MAX] at hrange hoverflow
      omega

/-- Equal normal form iff equal parse — normalization decides datetime equality.

    Datetime serialization is *partial* (`toString?`), so `normalize = (parse ·).bind toString?`
    can collapse two distinct parseable-but-unserializable values to the shared `none`. The forward
    direction therefore carries a serializability hypothesis on the parsed values; this is exactly
    what a full *serialization-completeness* result (`parse s = some d → (toString? d).isSome`,
    which needs the `Std.Time` civil-calendar round-trip) would discharge unconditionally, closing
    the gap with `Decimal`/`Duration`'s total-`toString` versions. The backward direction is
    unconditional. -/
public theorem normalize_eq_iff_parse_eq (s s' : String)
    (hs : ∀ d, Datetime.parse s = some d → (toString? d).isSome)
    (hs' : ∀ d, Datetime.parse s' = some d → (toString? d).isSome) :
    normalize s = normalize s' ↔ Datetime.parse s = Datetime.parse s' := by
  constructor
  · intro h
    unfold normalize at h
    cases hps : Datetime.parse s with
    | none =>
      cases hps' : Datetime.parse s' with
      | none => rfl
      | some d' =>
        -- `s'` parses and (by `hs'`) serializes, so its normal form is `some`, not `none`.
        obtain ⟨str', hstr'⟩ := Option.isSome_iff_exists.mp (hs' d' hps')
        rw [hps, hps', Option.bind_none, Option.bind_some, hstr'] at h
        exact absurd h (by simp)
    | some d =>
      obtain ⟨str, hstr⟩ := Option.isSome_iff_exists.mp (hs d hps)
      cases hps' : Datetime.parse s' with
      | none =>
        rw [hps, hps', Option.bind_none, Option.bind_some, hstr] at h
        exact absurd h (by simp)
      | some d' =>
        obtain ⟨str', hstr'⟩ := Option.isSome_iff_exists.mp (hs' d' hps')
        rw [hps, hps', Option.bind_some, Option.bind_some, hstr, hstr'] at h
        -- Equal serializations ⟹ equal datetimes (`toString?_injective`) ⟹ equal parses.
        have hstr'' : toString? d' = some str := h ▸ hstr'
        have hdd : d = d' := toString?_injective hstr hstr''
        rw [hdd]
  · intro h
    unfold normalize
    rw [h]

end Cedar.Thm.Datetime
