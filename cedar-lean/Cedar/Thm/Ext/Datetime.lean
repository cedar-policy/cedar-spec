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

`parse_sound`, `parse_complete`, and `parse_eq_none_iff` characterize exactly when parsing
succeeds, stated in terms of the grammar-level `IsWfDatetime` predicate and the `computeValue`
function (both in `Cedar.Thm.Ext.Datetime.Grammar`) that maps well-formed components to their
epoch-millisecond value. On top of them sit the serialization results — `parse_toString_roundtrip`,
`toString?_injective`, and `normalize_eq_iff_parse_eq` — the datetime analogues of the decimal and
duration surfaces, adapted to the *partial* serializer `toString?` (datetime rendering only covers
the grammar-representable range). The parser-independent roundtrip lemmas they build on live in
`Cedar.Thm.Ext.Datetime.Lemmas`. -/

/-- A well-formed datetime string always has a computed value. -/
public theorem computeValue_isSome_of_isWfDatetime {str : String} (h : IsWfDatetime str) :
    (computeValue str).isSome = true := by
  obtain ⟨c, hsyn, _, hstr⟩ := h
  unfold computeValue
  rw [hstr, parseComponents_asString hsyn]
  rfl

/-! ## Soundness, completeness, and failure characterization

The three theorems below relate `Datetime.parse` to the parser-independent `IsWfDatetime` and
`computeValue`. Unlike the decimal and duration parsers — hand-written character manipulation we
reason about directly — `Datetime.parse` delegates to `Std.Time.GenericFormat.parse`, whose field
parsers use well-founded recursion. The bulk of the work is therefore a parser-inversion library
(in `Cedar.Thm.Ext.Datetime.Lemmas`) that symbolically evaluates that recursion once and for all,
showing a successful `Std.Time` parse is *exactly* the rendering of well-formed witnessing
components. That reduces both soundness and completeness to reasoning about the components, not
about the parser's recursion.

All three are proven with no proof placeholders or custom axioms (`propext`, `Classical.choice`,
`Quot.sound` only). -/

/-- Soundness of `Datetime.parse`: if parsing succeeds, then the input is well-formed and
    `computeValue` yields exactly the returned datetime's value. (The value is in `Int64` range
    automatically, since it equals `d.val.toInt` for `d.val : Int64`.)

    Idea: read the successful parse backwards to recover the witnessing components, which are
    well-formed by construction — that gives `IsWfDatetime`. Both the parser and `computeValue`
    then evaluate those same components with the same value formula, so the value the parser
    returned is exactly the one `computeValue` computes. -/
public theorem parse_sound (str : String) (d : Datetime)
    (h : Datetime.parse str = some d) :
    IsWfDatetime str ∧ computeValue str = some d.val.toInt := by
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
    have hzt : zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = c.toMillis := Option.some.inj haltval
    omega
  refine ⟨⟨c, hsyn, hcon, hstr⟩, ?_⟩
  -- Value side is fully discharged: `computeValue str = some c.toMillis = some d.val.toInt`.
  rw [hstr, computeValue_asString hsyn, hcmillis]

/-- Completeness of `Datetime.parse`: if a string is well-formed and its computed value matches
    `d.val.toInt`, then parsing accepts the string as `d`.

    Idea: well-formedness gives witnessing components whose rendering is the input. On such a
    rendering every guard passes (a well-formed time can't spell a leap second, the fixed widths
    satisfy the length check, the offset is grammar-bounded) and the `Std.Time` parse succeeds
    with the components' value. That value is `d`'s, so parsing lands on `d`. -/
public theorem parse_complete (str : String) (d : Datetime)
    (hwf : IsWfDatetime str) (hval : computeValue str = some d.val.toInt) :
    Datetime.parse str = some d := by
  obtain ⟨c, hsyn, hcon, hstr⟩ := hwf
  -- Identify the target value `c.toMillis = d.val.toInt`.
  have hvc : c.toMillis = d.val.toInt := by
    have := computeValue_asString hsyn
    rw [hstr, this] at hval
    exact Option.some.inj hval
  subst hstr
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
  simp only [bind, Option.bind, hzt, hrange, if_pos]
  -- Final: `datetime? (zt value) = some d`, since that value is `c.toMillis = d.val.toInt`.
  show datetime? zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = some d
  rw [hztval, hvc]
  unfold datetime?
  rw [Int64.ofInt?_toInt d.val]
  simp only [bind, Option.bind, pure]

/-- `parse ∘ toString?` roundtrip: every successfully serialized datetime parses back to the
    original value. -/
public theorem parse_toString_roundtrip {d : Datetime} {str : String}
    (h : toString? d = some str) :
    Datetime.parse str = some d := by
  obtain ⟨hwf, hvalue⟩ := toString?_some_wf_value h
  exact parse_complete str d hwf hvalue

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

/-- Failure characterization for `Datetime.parse`: parsing rejects exactly strings that are
    not well-formed or whose computed value overflows the `Int64` range.

    Idea: the `Option` contrapositive of soundness and completeness, with no `Std.Time` reasoning
    of its own. If parsing fails yet the string is well-formed, its value must be out of range —
    otherwise completeness would have accepted it. Conversely a successful parse is well-formed
    with an in-range value (it is stored in an `Int64`), so it can meet neither failure clause. -/
public theorem parse_eq_none_iff (str : String) :
    Datetime.parse str = none ↔
    ¬ IsWfDatetime str ∨
    ∃ v, computeValue str = some v ∧ (v < Int64.MIN ∨ v > Int64.MAX) := by
  constructor
  · intro hnone
    -- Contrapose against `parse_complete`: if well-formed and in range, parsing would succeed.
    by_cases hwf : IsWfDatetime str
    · right
      -- Well-formed ⟹ the value exists; it must be out of range or `parse_complete` bites.
      have hsome := computeValue_isSome_of_isWfDatetime hwf
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      refine ⟨v, hv, ?_⟩
      by_contra hin
      -- In range ⟹ `ofInt? v` succeeds; its witness `i` satisfies `i.toInt = v`.
      have hrange : Int64.MIN ≤ v ∧ v ≤ Int64.MAX := by
        simp only [Int64.MIN, Int64.MAX] at hin ⊢; omega
      have hsome' := (Int64.ofInt?_some_iff (i := v)).mp hrange
      have htoInt : (Int64.ofInt v).toInt = v := Int64.ofInt?_some_toInt hsome'
      -- `parse_complete` then parses `str` as `⟨Int64.ofInt v⟩`, contradicting `hnone`.
      have hval : computeValue str = some (Datetime.mk (Int64.ofInt v)).val.toInt := by
        show computeValue str = some (Int64.ofInt v).toInt
        rw [htoInt]; exact hv
      have hparse := parse_complete str ⟨Int64.ofInt v⟩ hwf hval
      rw [hparse] at hnone
      exact absurd hnone (by simp)
    · exact Or.inl hwf
  · intro hbad
    -- A successful parse would contradict either branch via `parse_sound`.
    cases hparse : Datetime.parse str with
    | none => rfl
    | some d =>
      exfalso
      obtain ⟨hwf, hval⟩ := parse_sound str d hparse
      rcases hbad with hnwf | ⟨v, hv, hout⟩
      · exact hnwf hwf
      · -- `v = d.val.toInt`, which is always in `Int64` range — contradiction with `hout`.
        rw [hval] at hv
        have hveq : v = d.val.toInt := (Option.some.inj hv).symm
        subst hveq
        -- `ofInt? d.val.toInt = some d.val` (the roundtrip), so it is not `none`;
        -- out-of-range would force `none` by `ofInt?_none_iff`.
        have hnone' := (Int64.ofInt?_none_iff (i := d.val.toInt)).mp hout
        rw [Int64.ofInt?_toInt d.val] at hnone'
        exact absurd hnone' (by simp)

/-- Sharpened failure characterization: because the grammar bounds years to four digits and
    zone offsets to `±23:59`, a well-formed datetime's value always fits in `Int64`, so the
    overflow branch of `parse_eq_none_iff` is vacuous and parsing rejects *exactly* the malformed
    strings.

    Idea: take the previous characterization and discharge its overflow disjunct using the proven
    range bound on well-formed values. -/
public theorem parse_eq_none_iff_not_wf (str : String) :
    Datetime.parse str = none ↔ ¬ IsWfDatetime str := by
  rw [parse_eq_none_iff]
  constructor
  · rintro (hnwf | ⟨v, hv, hout⟩)
    · exact hnwf
    · -- The overflow branch contradicts the grammar's range bound on well-formed strings —
      -- and on malformed ones the left disjunct would have been taken; either way ¬wf holds
      -- unless `str` is well-formed, in which case `v = c.toMillis` is in range.
      intro hwf
      obtain ⟨c, hsyn, hcon, hstr⟩ := hwf
      rw [hstr, computeValue_asString hsyn] at hv
      have hveq : v = c.toMillis := (Option.some.inj hv).symm
      subst hveq
      have hrange := toMillis_int64_range hsyn hcon
      simp only [Int64.MIN, Int64.MAX] at hrange hout
      omega
  · exact Or.inl

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
