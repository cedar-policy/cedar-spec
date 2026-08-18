module

public import Cedar.Thm.Ext.Datetime.Grammar

/- The proofs below symbolically evaluate `Std.Time`'s parser/builder internals (`unfold`,
`simp [def]`, defeq `show`s on non-`@[expose]` definitions), which under the module system
requires `import all` OF THE DEFINING MODULE — `import all` exposure is per-module and NOT
transitive, so an umbrella `import all Std.Time` would not work. Each line below is needed
by some unfold; the set is bisection-minimal (dropping any listed module breaks the build). -/
import all Cedar.Data.Int64
import all Cedar.Spec.Ext.Datetime
import all Cedar.Thm.Data.String
import all Cedar.Thm.Ext.Datetime.Grammar
import all Std.Internal.Parsec.Basic
import all Std.Internal.Parsec.String
import all Std.Time.Format.Basic
import all Std.Time.Date.PlainDate
import all Std.Time.Date.Unit.Day
import all Std.Time.Date.Unit.Year
import all Std.Time.Zoned.ZoneRules
import all Std.Time.Zoned.TimeZone
import all Std.Time.DateTime.Timestamp
import all Std.Time.DateTime.PlainDateTime
import all Std.Time.DateTime.WallTime
import all Std.Time.DateTime
import all Std.Time.Duration
import all Std.Time.Time.PlainTime
import all Std.Time.Time.Unit.Basic
import all Std.Time.Time.Unit.Nanosecond
import all Std.Time.Time.Unit.Hour
import all Std.Time.Time.Unit.Minute

namespace Std.Time

abbrev ZonedDateTime := DateTime

namespace ZonedDateTime

abbrev ofPlainDateTime := DateTime.ofPlainDateTime

end ZonedDateTime

namespace Awareness

abbrev type (_ : Awareness) := DateTime

end Awareness

end Std.Time

namespace Cedar.Thm.Datetime
open Cedar.Spec.Ext
open Datetime

/-! # Datetime grammar roundtrip lemmas

The value function `computeValue = (parseComponents ·).map toMillis` re-parses the string. On a
well-formed string — one that equals `c.asString` for some structurally valid `c` — this re-parse
succeeds, giving `computeValue` a value. These lemmas establish the roundtrip nonterminal by
nonterminal, using the digit-field separator-freeness established from `IsDigits`. They culminate
in `parseComponents_asString`, which the aggregator's `computeValue_isSome_of_isWfDatetime` builds
on. -/

/-- A non-digit separator character never occurs in a digit string. -/
theorem not_mem_of_isDigits {s : String} (h : IsDigits s) {sep : Char} (hsep : sep.isDigit = false) :
    ∀ c ∈ s.toList, decide (c = sep) = false := by
  intro c hc
  have hcd : c.isDigit = true := h.2 c hc
  simp only [decide_eq_false_iff_not]
  intro he
  rw [he, hsep] at hcd
  exact absurd hcd (by simp)

/-- `parseDate` inverts `DateComponents.asString` on a syntactically well-formed date. -/
theorem parseDate_asString {d : DateComponents} (h : d.syntaxWf) :
    parseDate d.asString = some d := by
  obtain ⟨hy, hm, hd⟩ := h
  have hsep : ('-' : Char).isDigit = false := by decide
  show (match (d.year ++ String.singleton '-' ++ d.month ++ String.singleton '-' ++ d.day).splitToList
              (· = '-') with
        | [year, month, day] => some { year, month, day }
        | _ => none) = some d
  rw [splitToList_eq3 d.year d.month d.day (· = '-') '-' (by simp)
    (not_mem_of_isDigits hy.1 hsep) (not_mem_of_isDigits hm.1 hsep) (not_mem_of_isDigits hd.1 hsep)]

/-- `parseTime` inverts `TimeComponents.asString` on a syntactically well-formed time. -/
theorem parseTime_asString {t : TimeComponents} (h : t.syntaxWf) :
    parseTime t.asString = some t := by
  obtain ⟨hh, hm, hs⟩ := h
  have hsep : (':' : Char).isDigit = false := by decide
  show (match (t.hours ++ String.singleton ':' ++ t.minutes ++ String.singleton ':' ++ t.seconds).splitToList
              (· = ':') with
        | [hours, minutes, seconds] => some { hours, minutes, seconds }
        | _ => none) = some t
  rw [splitToList_eq3 t.hours t.minutes t.seconds (· = ':') ':' (by simp)
    (not_mem_of_isDigits hh.1 hsep) (not_mem_of_isDigits hm.1 hsep) (not_mem_of_isDigits hs.1 hsep)]

/-- `parseOffset` inverts `OffsetComponents.asString` on a syntactically well-formed offset. -/
theorem parseOffset_asString {o : OffsetComponents} (h : o.syntaxWf) :
    parseOffset o.asString = some o := by
  obtain ⟨neg, hrs, mins⟩ := o
  obtain ⟨hh, hm⟩ := h
  have hhlen' : hrs.toList.length = 2 := by rw [String.length_toList]; exact hh.2
  have hmlen' : mins.toList.length = 2 := by rw [String.length_toList]; exact hm.2
  have hrest_len : (hrs.toList ++ mins.toList).length = 4 := by
    rw [List.length_append, hhlen', hmlen']
  have htake : (hrs.toList ++ mins.toList).take 2 = hrs.toList := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hdrop : (hrs.toList ++ mins.toList).drop 2 = mins.toList := by
    rw [List.drop_append_of_le_length (by omega)]
    simp [hhlen']
  -- Expose the sign character so the `sign :: rest` match in `parseOffset` fires.
  have hstr : (OffsetComponents.mk neg hrs mins).asString.toList
      = (if neg then '-' else '+') :: (hrs.toList ++ mins.toList) := by
    unfold OffsetComponents.asString
    rw [show (if neg then "-" else "+")
          = String.singleton (if neg then '-' else '+') from by cases neg <;> rfl]
    simp [String.toList_append]
  unfold parseOffset
  rw [hstr]
  cases neg <;>
    simp only [Bool.false_eq_true, ↓reduceIte, hrest_len, htake, hdrop,
      String.ofList_toList, and_true, or_true, true_or, decide_true, decide_false,
      Char.reduceEq]

/-- The `'.' SSS` chunk of a time-bearing tail: `""` when `SSS` is absent, `"." ++ sss` otherwise. -/
def millisChunk (millis : Option String) : String :=
  match millis with | none => "" | some sss => "." ++ sss

/-- The post-`'T'` body of a time-bearing tail: `time.asString ++ millisChunk ++ zone.asString`.
    This is `tp.asString` with the leading `"T"` removed — exactly what `parseComponents` hands to
    `parseTimePart` after splitting on `'T'`. -/
def timePartBody (tp : TimePart) : String :=
  tp.time.asString ++ millisChunk tp.millis ++ tp.zone.asString

theorem timePart_asString_eq (tp : TimePart) :
    tp.asString = "T" ++ timePartBody tp := by
  unfold TimePart.asString timePartBody millisChunk
  cases tp.millis with
  | none => simp [String.append_assoc]
  | some sss => simp [String.append_assoc]

/-- The inner `splitToList (· = '.')` roundtrip inside `parseTimePart`, factored out: on a
    well-formed time and optional `SSS`, `time.asString ++ millisChunk millis` splits back into the
    time and the optional `SSS`, and both re-parse to the original. -/
theorem parseTimePart_millisSplit {t : TimeComponents} {millis : Option String} {zone : Zone}
    (ht : t.syntaxWf) (hms : IsWfOptionalMillis millis) :
    (match (t.asString ++ millisChunk millis).splitToList (· = '.') with
      | [time] => (parseTime time).bind (fun tt => some (TimePart.mk tt none zone))
      | [time, sss] => (parseTime time).bind (fun tt => some (TimePart.mk tt (some sss) zone))
      | _ => none) = some (TimePart.mk t millis zone) := by
  obtain ⟨hh, hm, hs⟩ := ht
  have hdot : ('.' : Char).isDigit = false := by decide
  -- No digit field of the time contains '.', and ':' ≠ '.'.
  have hcolon : (":" : String).toList = [':'] := rfl
  have htime_no_dot : ∀ c ∈ t.asString.toList, decide (c = '.') = false := by
    intro c hc
    unfold TimeComponents.asString at hc
    rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
      hcolon] at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((((hc | hc) | hc) | hc) | hc)
    · exact not_mem_of_isDigits hh.1 hdot c hc
    · rw [hc]; decide
    · exact not_mem_of_isDigits hm.1 hdot c hc
    · rw [hc]; decide
    · exact not_mem_of_isDigits hs.1 hdot c hc
  cases millis with
  | none =>
    unfold millisChunk
    simp only [String.append_empty]
    rw [splitToList_no_sep _ _ htime_no_dot]
    simp [parseTime_asString ⟨hh, hm, hs⟩]
  | some sss =>
    have hsss_no_dot : ∀ c ∈ sss.toList, decide (c = '.') = false :=
      not_mem_of_isDigits hms.1 hdot
    unfold millisChunk
    rw [show t.asString ++ ("." ++ sss) = t.asString ++ String.singleton '.' ++ sss from by
          rw [show ("." : String) = String.singleton '.' from rfl, String.append_assoc]]
    rw [splitToList_eq t.asString sss (· = '.') '.' (by simp) htime_no_dot hsss_no_dot]
    simp [parseTime_asString ⟨hh, hm, hs⟩]

/-- `parseTimePart` inverts the post-`'T'` body `timePartBody tp` on a well-formed tail. -/
theorem parseTimePart_asString {tp : TimePart} (h : tp.syntaxWf) :
    parseTimePart (timePartBody tp) = some tp := by
  obtain ⟨ht, hms, hz⟩ := h
  -- Body is `time.asString ++ millisChunk ++ zone.asString`; write its reversed char list.
  have hbody : (timePartBody tp).toList
      = (tp.time.asString ++ millisChunk tp.millis).toList ++ tp.zone.asString.toList := by
    unfold timePartBody
    rw [String.toList_append]
  unfold parseTimePart
  cases hzone : tp.zone with
  | utc =>
    -- zone renders as "Z"; the reversed list starts with 'Z'.
    have hz_str : tp.zone.asString = "Z" := by rw [hzone]; rfl
    have hZlist : ("Z" : String).toList = ['Z'] := rfl
    have hrev : (timePartBody tp).toList.reverse
        = 'Z' :: (tp.time.asString ++ millisChunk tp.millis).toList.reverse := by
      rw [hbody, hz_str, hZlist, List.reverse_append]; rfl
    rw [hrev]
    simp only [↓reduceIte, List.reverse_reverse, String.ofList_toList, Option.bind_eq_bind,
      Option.bind_some]
    have hsplit := parseTimePart_millisSplit (t := tp.time) (millis := tp.millis)
      (zone := Zone.utc) ht hms
    rw [show tp = TimePart.mk tp.time tp.millis Zone.utc from by rw [← hzone]]
    exact hsplit
  | offset o =>
    have ho : o.syntaxWf := by rw [hzone] at hz; exact hz
    obtain ⟨hoh, hom⟩ := ho
    have hz_str : tp.zone.asString = o.asString := by rw [hzone]; rfl
    -- The offset renders to exactly 5 characters, none of which is 'Z'.
    have hlen5 : o.asString.toList.length = 5 := by
      unfold OffsetComponents.asString
      simp only [String.toList_append, List.length_append, String.length_toList, hoh.2, hom.2]
      cases o.negative <;> decide
    have hno_Z : ∀ c ∈ o.asString.toList, c ≠ 'Z' := by
      intro c hc
      unfold OffsetComponents.asString at hc
      rw [String.toList_append, String.toList_append] at hc
      simp only [List.mem_append] at hc
      have hsign : (if o.negative then "-" else "+").toList = [if o.negative then '-' else '+'] := by
        cases o.negative <;> rfl
      rw [hsign] at hc
      simp only [List.mem_singleton] at hc
      rcases hc with (hc | hc) | hc
      · subst hc; cases o.negative <;> decide
      · have := not_mem_of_isDigits hoh.1 (sep := 'Z') (by decide) c hc
        simp only [decide_eq_false_iff_not] at this
        intro he; exact this (by rw [he])
      · have := not_mem_of_isDigits hom.1 (sep := 'Z') (by decide) c hc
        simp only [decide_eq_false_iff_not] at this
        intro he; exact this (by rw [he])
    -- Decompose the reversed offset string as a nonempty cons.
    obtain ⟨c, revZ, hcons⟩ : ∃ c revZ, o.asString.toList.reverse = c :: revZ := by
      cases hrz : o.asString.toList.reverse with
      | nil =>
        exfalso
        have : o.asString.toList.reverse.length = 5 := by rw [List.length_reverse, hlen5]
        rw [hrz] at this; simp at this
      | cons c revZ => exact ⟨c, revZ, rfl⟩
    have hrevZ_len : revZ.length = 4 := by
      have h5 : (c :: revZ).length = 5 := by rw [← hcons, List.length_reverse, hlen5]
      simpa using h5
    have hc_ne_Z : c ≠ 'Z' := by
      apply hno_Z
      have hmem : c ∈ o.asString.toList.reverse := by rw [hcons]; exact List.mem_cons_self ..
      rwa [List.mem_reverse] at hmem
    have hrev : (timePartBody tp).toList.reverse
        = c :: (revZ ++ (tp.time.asString ++ millisChunk tp.millis).toList.reverse) := by
      rw [hbody, hz_str, List.reverse_append, hcons]; rfl
    have htake : (c :: (revZ ++ (tp.time.asString ++ millisChunk tp.millis).toList.reverse)).take 5
        = c :: revZ := by
      rw [show (5 : Nat) = 4 + 1 from rfl, List.take_succ_cons,
        List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have hdrop : (c :: (revZ ++ (tp.time.asString ++ millisChunk tp.millis).toList.reverse)).drop 5
        = (tp.time.asString ++ millisChunk tp.millis).toList.reverse := by
      rw [show (5 : Nat) = 4 + 1 from rfl, List.drop_succ_cons,
        List.drop_append_of_le_length (by omega)]
      simp [hrevZ_len]
    -- `parseOffset` recovers the offset from the last 5 (reversed) characters.
    have hoff : parseOffset (String.ofList (c :: revZ).reverse) = some o := by
      rw [← hcons, List.reverse_reverse, String.ofList_toList]
      exact parseOffset_asString ⟨hoh, hom⟩
    rw [hrev]
    -- The `c :: rev` branch: c is not 'Z', so we take the offset path; reduce the do-bind.
    simp only [hc_ne_Z, ↓reduceIte, htake, hdrop, hoff, Option.bind_eq_bind, Option.bind_some,
      List.reverse_reverse, String.ofList_toList]
    have hsplit := parseTimePart_millisSplit (t := tp.time) (millis := tp.millis)
      (zone := Zone.offset o) ht hms
    rw [show tp = TimePart.mk tp.time tp.millis (Zone.offset o) from by rw [← hzone]]
    exact hsplit

/-- `parseComponents` inverts `DatetimeComponents.asString` on a syntactically well-formed
    datetime — the top-level roundtrip. The date part never contains `'T'` (it is `'-'`-separated
    digit fields), so the split on `'T'` cleanly separates the date from the time-bearing tail. -/
theorem parseComponents_asString {c : DatetimeComponents} (h : c.syntaxWf) :
    parseComponents c.asString = some c := by
  obtain ⟨hdate, htime⟩ := h
  obtain ⟨hy, hm, hd⟩ := hdate
  have hT : ('T' : Char).isDigit = false := by decide
  -- The date's rendering contains no 'T'.
  have hdate_no_T : ∀ ch ∈ c.date.asString.toList, decide (ch = 'T') = false := by
    intro ch hc
    unfold DateComponents.asString at hc
    have hdash : ("-" : String).toList = ['-'] := rfl
    rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
      hdash] at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((((hc | hc) | hc) | hc) | hc)
    · exact not_mem_of_isDigits hy.1 hT ch hc
    · rw [hc]; decide
    · exact not_mem_of_isDigits hm.1 hT ch hc
    · rw [hc]; decide
    · exact not_mem_of_isDigits hd.1 hT ch hc
  unfold parseComponents
  cases htp : c.time with
  | none =>
    have hstr : c.asString = c.date.asString := by
      unfold DatetimeComponents.asString; rw [htp]; simp
    rw [hstr, splitToList_no_sep _ _ hdate_no_T]
    simp only [Option.bind_eq_bind]
    rw [parseDate_asString ⟨hy, hm, hd⟩]
    rw [show c = DatetimeComponents.mk c.date none from by rw [← htp]]
    rfl
  | some tp =>
    have htp_wf : tp.syntaxWf := by rw [htp] at htime; exact htime
    -- asString = date ++ "T" ++ timePartBody tp
    have hstr : c.asString = c.date.asString ++ String.singleton 'T' ++ timePartBody tp := by
      unfold DatetimeComponents.asString
      rw [htp]
      simp only []
      rw [timePart_asString_eq]
      rw [show ("T" : String) = String.singleton 'T' from rfl, String.append_assoc]
    have hbody_no_T : ∀ ch ∈ (timePartBody tp).toList, decide (ch = 'T') = false := by
      obtain ⟨htt, htms, htz⟩ := htp_wf
      obtain ⟨hth, htm, hts⟩ := htt
      intro ch hc
      simp only [decide_eq_false_iff_not]; intro heq; subst heq
      unfold timePartBody at hc
      rw [String.toList_append, String.toList_append] at hc
      simp only [List.mem_append] at hc
      -- 'T' is not a digit, and differs from ':', '.', '+', '-', 'Z'.
      have hnd : ∀ {x : String}, IsDigits x → 'T' ∉ x.toList := by
        intro x hx hmem; have := not_mem_of_isDigits hx (sep := 'T') (by decide) 'T' hmem; simp at this
      rcases hc with (hc | hc) | hc
      · -- in time.asString
        unfold TimeComponents.asString at hc
        have hcolon : (":" : String).toList = [':'] := rfl
        rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
          hcolon] at hc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with ((((hc | hc) | hc) | hc) | hc)
        · exact hnd hth.1 hc
        · exact absurd hc (by decide)
        · exact hnd htm.1 hc
        · exact absurd hc (by decide)
        · exact hnd hts.1 hc
      · -- in millisChunk
        cases htms' : tp.millis with
        | none => rw [htms'] at hc; simp [millisChunk] at hc
        | some sss =>
          rw [htms'] at hc htms
          unfold millisChunk at hc
          have hdotL : ("." : String).toList = ['.'] := rfl
          rw [String.toList_append, hdotL] at hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with hc | hc
          · exact absurd hc (by decide)
          · exact hnd htms.1 hc
      · -- in zone.asString
        cases htz' : tp.zone with
        | utc =>
          rw [htz'] at hc
          have : (Zone.utc.asString).toList = ['Z'] := rfl
          rw [this] at hc; simp only [List.mem_singleton] at hc; exact absurd hc (by decide)
        | offset o =>
          rw [htz'] at hc htz
          obtain ⟨hoh, hom⟩ := htz
          unfold Zone.asString OffsetComponents.asString at hc
          have hsign : (if o.negative then "-" else "+").toList = [if o.negative then '-' else '+'] := by
            cases o.negative <;> rfl
          rw [String.toList_append, String.toList_append, hsign] at hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with (hc | hc) | hc
          · revert hc; cases o.negative <;> decide
          · exact hnd hoh.1 hc
          · exact hnd hom.1 hc
    rw [hstr, splitToList_eq c.date.asString (timePartBody tp) (· = 'T') 'T' (by simp)
      hdate_no_T hbody_no_T]
    simp only [Option.bind_eq_bind]
    rw [parseDate_asString ⟨hy, hm, hd⟩, parseTimePart_asString htp_wf]
    rw [show c = DatetimeComponents.mk c.date (some tp) from by rw [← htp]]
    rfl

/-! ## Canonical serialization certificates -/

/-- The executable fixed-width digit check reflects the grammar predicate. -/
theorem isFixedDigits_eq_true_iff (width : Nat) (s : String) :
    isFixedDigits width s = true ↔ IsFixedDigits width s := by
  unfold isFixedDigits IsFixedDigits
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hdigits, hwidth⟩
    exact ⟨isDigits_of_toNat?'_isSome hdigits, beq_iff_eq.mp hwidth⟩
  · rintro ⟨hdigits, hwidth⟩
    exact ⟨hdigits.toNat?'_isSome, beq_iff_eq.mpr hwidth⟩

/-- The executable syntax check on datetime components reflects `syntaxWf`. -/
theorem DatetimeComponents.syntaxWfB_eq_true_iff (components : DatetimeComponents) :
    components.syntaxWfB = true ↔ components.syntaxWf := by
  rcases components with ⟨⟨year, month, day⟩, time⟩
  cases time with
  | none =>
    simp only [DatetimeComponents.syntaxWfB, DatetimeComponents.syntaxWf,
      DateComponents.syntaxWf, isFixedDigits_eq_true_iff, Bool.and_eq_true]
    simp only [and_assoc, and_true]
  | some time =>
    rcases time with ⟨⟨hours, minutes, seconds⟩, millis, zone⟩
    cases millis <;> cases zone <;>
      simp only [DatetimeComponents.syntaxWfB, DatetimeComponents.syntaxWf,
        DateComponents.syntaxWf, TimePart.syntaxWf, TimeComponents.syntaxWf,
        IsWfOptionalMillis, Zone.syntaxWf, OffsetComponents.syntaxWf,
        isFixedDigits_eq_true_iff, Bool.and_eq_true] <;>
      simp only [and_assoc, and_true, true_and]

/-- The executable numeric-constraint check reflects `constraintsWf`. -/
theorem DatetimeComponents.constraintsWfB_eq_true_iff (components : DatetimeComponents) :
    components.constraintsWfB = true ↔ components.constraintsWf := by
  rcases components with ⟨⟨year, month, day⟩, time⟩
  cases time with
  | none =>
    simp only [DatetimeComponents.constraintsWfB, DatetimeComponents.constraintsWf,
      DateComponents.constraintsWf, Bool.and_eq_true, decide_eq_true_eq]
    simp only [and_assoc, and_true]
  | some time =>
    rcases time with ⟨⟨hours, minutes, seconds⟩, millis, zone⟩
    cases zone <;>
      simp only [DatetimeComponents.constraintsWfB, DatetimeComponents.constraintsWf,
        DateComponents.constraintsWf, TimePart.constraintsWf, TimeComponents.constraintsWf,
        Zone.constraintsWf, OffsetComponents.constraintsWf, Bool.and_eq_true,
        decide_eq_true_eq] <;>
      simp only [and_assoc, and_true]

/-- Successful component serialization carries exactly the certificate checked by
    `canonicalComponents?`. -/
theorem canonicalComponents?_some {d : Cedar.Spec.Ext.Datetime} {components : DatetimeComponents}
    (h : canonicalComponents? d = some components) :
    components.syntaxWf ∧ components.constraintsWf ∧ components.toMillis = d.val.toInt := by
  unfold canonicalComponents? at h
  cases hlocal : canonicalLocalTime? d.val.toInt with
  | none => simp [hlocal] at h
  | some localTime =>
    simp only [hlocal] at h
    let candidate := canonicalComponents localTime
    change (if candidate.syntaxWfB && candidate.constraintsWfB &&
        candidate.toMillis == d.val.toInt then some candidate else none) = some components at h
    split at h
    · rename_i hvalid
      simp only [Bool.and_eq_true, beq_iff_eq] at hvalid
      obtain ⟨⟨hsyntax, hconstraints⟩, hvalue⟩ := hvalid
      replace hsyntax := DatetimeComponents.syntaxWfB_eq_true_iff candidate |>.mp hsyntax
      replace hconstraints :=
        DatetimeComponents.constraintsWfB_eq_true_iff candidate |>.mp hconstraints
      exact Option.some.inj h ▸ ⟨hsyntax, hconstraints, hvalue⟩
    · contradiction

/-- Every string returned by `toString?` is a well-formed datetime rendering with the source
    datetime's exact millisecond value. -/
theorem toString?_some_wf_value {d : Cedar.Spec.Ext.Datetime} {str : String}
    (h : toString? d = some str) :
    IsWfDatetime str ∧ computeValue str = some d.val.toInt := by
  unfold toString? at h
  cases hc : canonicalComponents? d with
  | none => simp [hc] at h
  | some components =>
    simp only [hc, Option.map_some, Option.some.injEq] at h
    subst str
    obtain ⟨hsyntax, hconstraints, hvalue⟩ := canonicalComponents?_some hc
    refine ⟨⟨components, hsyntax, hconstraints, rfl⟩, ?_⟩
    unfold computeValue
    rw [parseComponents_asString hsyntax, Option.map_some, hvalue]

/-- Values outside the exact grammar-representable millisecond interval do not serialize: the
    canonical local-time selection returns `none`, so `toString?` short-circuits. -/
public theorem toString?_eq_none_of_not_representable (d : Cedar.Spec.Ext.Datetime)
    (h : d.val.toInt < MIN_REPRESENTABLE_MILLIS ∨ MAX_REPRESENTABLE_MILLIS < d.val.toInt) :
    toString? d = none := by
  have hlocal : canonicalLocalTime? d.val.toInt = none := by
    unfold canonicalLocalTime?
    rw [if_pos h]
  unfold toString? canonicalComponents?
  rw [hlocal]
  rfl

/-! ## Foundational `Parsec` symbolic-evaluation lemmas

`Std.Time.GenericFormat.parse` is built on the `Std.Internal.Parsec` combinator library over the
string iterator `It := Σ s : String, s.Pos`. The alternation-value bridge below
(`stdTime_alternation_value`) ultimately needs to symbolically evaluate that parser on the
rendering of well-formed components. These lemmas are the base of that evaluation ladder: they give
the one-step reduction of the primitive combinators (`any`, monadic `bind`, `satisfy`) on the
string iterator, and — on top of them — the `exactlyChars` walk lemma (`exactlyChars_digits`),
which shows a fixed-width run of digit characters is consumed exactly and advances the iterator past
it. They are parser-agnostic (nothing datetime-specific).

Built on top of these are the evaluation lemmas for `parseNum`/`parseWith`/`parseWithDate`,
`DateBuilder.build`, and `toTimestamp` that follow further below. -/

/-- The string-iterator type underlying `Std.Time`'s parsers: a string paired with a position
    into it. -/
abbrev ParseIt := Σ s : String, s.Pos

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- One-step reduction of `any` on the string iterator: succeed with the current character and the
    advanced iterator when input remains, otherwise fail with EOF. -/
theorem any_eq (it : ParseIt) :
    (any (ι := ParseIt) (elem := Char) it) =
      if h : Input.hasNext it = true
      then ParseResult.success (Input.next' it h) (Input.curr' it h)
      else ParseResult.error it Error.eof := rfl

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- Applying a monadic `bind` to an iterator reduces to the `match`-on-result case split. -/
theorem parsec_bind_app {α β : Type} (g : Std.Internal.Parsec ParseIt α)
    (f : α → Std.Internal.Parsec ParseIt β) (it : ParseIt) :
    Std.Internal.Parsec.bind g f it
      = (match g it with | .success rem a => f a rem | .error pos msg => .error pos msg) := by
  cases hg : g it <;> simp only [Std.Internal.Parsec.bind, hg]

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- One-step reduction of `satisfy p` on the string iterator: consume the current character when it
    satisfies `p`, fail (without consuming) when it does not, and fail with EOF at end of input. -/
theorem satisfy_eq (p : Char → Bool) (it : ParseIt) :
    (satisfy (ι := ParseIt) (elem := Char) p it) =
      if h : Input.hasNext it = true then
        (if p (Input.curr' it h) then ParseResult.success (Input.next' it h) (Input.curr' it h)
         else ParseResult.error it (.other "condition not satisfied"))
      else ParseResult.error it Error.eof := by
  unfold satisfy
  simp only [bind, Bind.bind, pure, Pure.pure, attempt]
  rw [parsec_bind_app, any_eq]
  by_cases h : Input.hasNext it = true
  · by_cases hp : p (Input.curr' it h) <;> simp [h, hp, Std.Internal.Parsec.pure, fail]
  · simp [h]

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `hasNext` on the string iterator holds exactly when the position is not the end position. -/
theorem hasNext_iff (s : String) (p : s.Pos) :
    Input.hasNext (⟨s, p⟩ : ParseIt) = true ↔ p ≠ s.endPos := by
  show decide (¬ p.IsAtEnd) = true ↔ _
  rw [decide_eq_true_iff]

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `curr'` reads the character at the current position. -/
theorem curr'_eq (s : String) (p : s.Pos) (h : Input.hasNext (⟨s, p⟩ : ParseIt) = true) :
    Input.curr' (⟨s, p⟩ : ParseIt) h = p.get ((hasNext_iff s p).mp h) := rfl

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `next'` advances the position by one character. -/
theorem next'_eq (s : String) (p : s.Pos) (h : Input.hasNext (⟨s, p⟩ : ParseIt) = true) :
    Input.next' (⟨s, p⟩ : ParseIt) h = (⟨s, p.next ((hasNext_iff s p).mp h)⟩ : ParseIt) := rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- Unfolding equation for the tail-recursive core of `exactlyChars`. -/
theorem exactlyChars_go_eq (parse : Parser Char) (size : Nat) (acc : String) (count : Nat) :
    exactlyChars.go parse size acc count =
      if count ≥ size then Std.Internal.Parsec.pure acc
      else Std.Internal.Parsec.bind parse
        (fun res => exactlyChars.go parse size (acc.push res) count.succ) :=
  exactlyChars.go.eq_def parse size acc count

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- Core walk lemma for `exactlyChars.go` over a digit char-list. Running the accumulator loop on
    an iterator positioned at `pre ⧺ (ofList L ⧺ rest)` with `size - count = |L|` remaining digits
    consumes exactly `L`, returning `acc ++ ofList L` and advancing the position past `L`. Proved by
    induction on `L`, using the `String.Pos.Splits` API for position bookkeeping. -/
theorem exactlyChars_go_digits (L : List Char) (hdig : ∀ c ∈ L, c.isDigit = true)
    (s : String) (size count : Nat) (hcnt : size - count = L.length)
    (acc pre rest : String) (p : s.Pos)
    (hsplit : p.Splits pre (String.ofList L ++ rest)) :
    ∃ p' : s.Pos,
      exactlyChars.go (satisfy Char.isDigit) size acc count ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ (acc ++ String.ofList L) ∧
      p'.Splits (pre ++ String.ofList L) rest := by
  induction L generalizing count acc pre p with
  | nil =>
    have hge : count ≥ size := by simp at hcnt; omega
    refine ⟨p, ?_, ?_⟩
    · rw [exactlyChars_go_eq, if_pos hge]
      simp only [String.ofList_nil, String.append_empty, Std.Internal.Parsec.pure]
    · simpa using hsplit
  | cons c L' ih =>
    have hlt : ¬ count ≥ size := by
      simp only [List.length_cons] at hcnt; omega
    rw [String.ofList_cons, String.append_assoc] at hsplit
    have hp : p ≠ s.endPos := hsplit.ne_endPos_of_singleton
    have hnext : (p.next hp).Splits (pre ++ String.singleton c) (String.ofList L' ++ rest) :=
      hsplit.next
    have hgetc : p.get hp = c := by
      obtain ⟨t₂', ht⟩ := hsplit.exists_eq_singleton_append hp
      rw [String.singleton_append_inj] at ht
      exact ht.1.symm
    have hcdig : c.isDigit = true := hdig c (List.mem_cons_self ..)
    rw [exactlyChars_go_eq, if_neg hlt, parsec_bind_app]
    have hhn : Input.hasNext (⟨s, p⟩ : ParseIt) = true := (hasNext_iff s p).mpr hp
    rw [satisfy_eq]
    simp only [hhn, dif_pos]
    rw [curr'_eq, next'_eq]
    have hcurr : Char.isDigit (p.get ((hasNext_iff s p).mp hhn)) = true := by
      rw [hgetc]; exact hcdig
    simp only [hcurr, if_pos]
    rw [show (p.get ((hasNext_iff s p).mp hhn)) = c from hgetc]
    have hcnt' : size - count.succ = L'.length := by
      simp only [List.length_cons] at hcnt; omega
    obtain ⟨p', hgo, hsp⟩ := ih (fun x hx => hdig x (List.mem_cons_of_mem _ hx))
      count.succ hcnt' (acc.push c) (pre ++ String.singleton c)
      (p.next ((hasNext_iff s p).mp hhn)) (by rw [hgetc] at *; exact hnext)
    refine ⟨p', ?_, ?_⟩
    · rw [hgo, String.ofList_cons, ← String.append_assoc, String.append_singleton]
    · rw [String.ofList_cons, ← String.append_assoc]
      exact hsp

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- **`exactlyChars` walk lemma.** Running `exactlyChars (satisfy Char.isDigit) n` on an iterator at
    the start of `digits ++ rest`, where `digits` is exactly `n` digit characters, succeeds:
    it returns `digits` and leaves the iterator on the same string with its offset advanced by
    `digits`' byte size (i.e. positioned at the start of `rest`). This is the first rung above the
    primitive combinators; the fixed-width numeric field parsers build directly on it. -/
theorem exactlyChars_digits {digits rest : String} (n : Nat)
    (hlen : digits.length = n)
    (hdig : ∀ c ∈ digits.toList, c.isDigit = true) :
    ∃ (it' : ParseIt),
      exactlyChars (satisfy Char.isDigit) n ⟨digits ++ rest, (digits ++ rest).startPos⟩
        = ParseResult.success it' digits ∧
      it'.1 = digits ++ rest ∧
      it'.2.offset.byteIdx = digits.utf8ByteSize := by
  have hgo0 : exactlyChars (satisfy Char.isDigit) n
      = exactlyChars.go (satisfy Char.isDigit) n "" 0 := rfl
  have hsplit0 : ((digits ++ rest).startPos).Splits ""
      (String.ofList digits.toList ++ rest) := by
    rw [String.ofList_toList]
    exact String.splits_startPos (digits ++ rest)
  have hcnt : n - 0 = digits.toList.length := by rw [String.length_toList, hlen]; omega
  obtain ⟨p', hgo, hsp⟩ := exactlyChars_go_digits digits.toList (by simpa using hdig)
    (digits ++ rest) n 0 hcnt "" "" rest (digits ++ rest).startPos hsplit0
  refine ⟨⟨digits ++ rest, p'⟩, ?_, rfl, ?_⟩
  · rw [hgo0, hgo]; simp [String.ofList_toList]
  · rw [String.empty_append, String.ofList_toList] at hsp
    rw [hsp.offset_eq_rawEndPos, String.byteIdx_rawEndPos]

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- One-step reduction of the `Parsec` functor's `<$>` (`Functor.map`) on an iterator: run the
    underlying parser and, on success, apply `f` to the produced value. The `Parsec` `Monad`
    instance uses the default `map f x := bind x (pure ∘ f)`, so this follows from
    `parsec_bind_app`. -/
theorem parsec_map_app {α β : Type} (f : α → β) (p : Std.Internal.Parsec ParseIt α) (it : ParseIt) :
    (f <$> p) it = (match p it with
      | .success rem a => .success rem (f a)
      | .error pos msg => .error pos msg) := by
  show Std.Internal.Parsec.bind p (Function.comp Std.Internal.Parsec.pure f) it = _
  rw [parsec_bind_app]
  cases p it <;> rfl

/-- For an `isNat` string, `String.toNat!` agrees with the total `String.toNat?` defaulted to `0`. -/
theorem toNat!_eq_getD_toNat? (s : String) (h : s.isNat = true) :
    s.toNat! = (s.toNat?).getD 0 := by
  unfold String.toNat! String.toNat?
  unfold String.Slice.toNat! String.Slice.toNat?
  rw [String.isNat_toSlice]
  simp only [h, if_true, Option.getD_some]

/-- On a digit string (which contains no `'_'`), Cedar's underscore-rejecting `toNat?'` coincides
    with the stdlib `String.toNat?`. -/
theorem toNat?'_eq_toNat? (s : String) (h : IsDigits s) : toNat?' s = s.toNat? := by
  unfold toNat?'
  rw [no_underscore_of_isDigits h]
  simp

/-- On a digit string, `String.toNat!` equals the grammar's `fieldValue`
    (`fieldValue s = (toNat?' s).getD 0`). -/
theorem toNat!_eq_fieldValue (s : String) (h : IsDigits s) : s.toNat! = fieldValue s := by
  unfold fieldValue
  rw [toNat?'_eq_toNat? s h, toNat!_eq_getD_toNat? s (isNat_of_isDigits h)]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- `parseNum n` on a fixed-width digit field. Running `Std.Time`'s `parseNum` (which is
    `String.toNat! <$> exactlyChars (satisfy Char.isDigit) n`) on `digits ++ rest`, where `digits`
    is exactly `n` digit characters, succeeds: it produces `String.toNat! digits`, leaves the string
    unchanged, and advances the position past `digits`. See `parseNum_digits_fieldValue` for the
    same result phrased via the grammar's `fieldValue`. -/
theorem parseNum_digits {digits rest : String} (n : Nat)
    (hlen : digits.length = n)
    (hdig : ∀ c ∈ digits.toList, c.isDigit = true) :
    ∃ (it' : ParseIt),
      parseNum n ⟨digits ++ rest, (digits ++ rest).startPos⟩
        = ParseResult.success it' (String.toNat! digits) ∧
      it'.1 = digits ++ rest ∧
      it'.2.offset.byteIdx = digits.utf8ByteSize := by
  obtain ⟨it', hpar, hstr, hoff⟩ := exactlyChars_digits n hlen hdig
  refine ⟨it', ?_, hstr, hoff⟩
  unfold parseNum
  rw [parsec_map_app, hpar]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- `parseNum n` on a fixed-width digit field, value phrased via the grammar's `fieldValue` — the
    form the datetime roundtrip consumer wants: on `digits ++ rest` with `digits` exactly `n`
    digits, `parseNum n` succeeds producing `fieldValue digits`, keeps the string, and advances
    past `digits`. -/
theorem parseNum_digits_fieldValue {digits rest : String} (n : Nat)
    (hdigits : IsFixedDigits n digits) :
    ∃ (it' : ParseIt),
      parseNum n ⟨digits ++ rest, (digits ++ rest).startPos⟩
        = ParseResult.success it' (fieldValue digits) ∧
      it'.1 = digits ++ rest ∧
      it'.2.offset.byteIdx = digits.utf8ByteSize := by
  obtain ⟨hdig, hlen⟩ := hdigits
  obtain ⟨it', hpar, hstr, hoff⟩ := parseNum_digits n hlen hdig.2
  exact ⟨it', by rw [hpar, toNat!_eq_fieldValue digits hdig], hstr, hoff⟩

open Std.Time Std.Time.Internal in
/-- Cedar's grammar-level `epochDays` agrees with `Std.Time.PlainDate.toEpochDay` whenever
    the `PlainDate`'s field projections equal the corresponding `Nat` field values. Both compute the
    same Howard-Hinnant `days_from_civil` arithmetic; the proof unfolds both, lines up the
    `Bounded`/`UnitVal`/`Int` field coercions, and closes definitionally. This is the bridge between
    the parser's `PlainDate` (built from the parsed fields) and the value function's `epochDays`. -/
theorem epochDays_eq (year month day : Nat) (date : PlainDate)
    (hy : date.year.toInt = (year : Int))
    (hm : date.month.toInt = (month : Int))
    (hd : date.day.toInt = (day : Int)) :
    epochDays year month day = date.toEpochDay.toInt := by
  unfold PlainDate.toEpochDay
  simp only [epochDays, Internal.UnitVal.toInt, Day.Offset.ofInt]
  rw [hm, hd, hy, show (date.year : Int) = (year : Int) from hy]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- `parseWith` on the four-digit year modifier. On `digits ++ rest` with `IsFixedDigits 4 digits`,
    it succeeds with value `Int.ofNat (fieldValue digits)`, string unchanged, position advanced. -/
theorem parseWith_year {digits rest : String} (config : Std.Time.FormatConfig)
    (hdigits : IsFixedDigits 4 digits) :
    ∃ (it' : ParseIt),
      parseWith config (.y .fourDigit) ⟨digits ++ rest, (digits ++ rest).startPos⟩
        = ParseResult.success it' (Int.ofNat (fieldValue digits)) ∧
      it'.1 = digits ++ rest ∧
      it'.2.offset.byteIdx = digits.utf8ByteSize := by
  obtain ⟨it', hpar, hstr, hoff⟩ := parseNum_digits_fieldValue 4 hdigits
  refine ⟨it', ?_, hstr, hoff⟩
  show (Int.ofNat <$> parseNum 4) _ = _
  rw [parsec_map_app, hpar]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith` on the two-digit month modifier. On `digits ++ rest` with `IsFixedDigits 2 digits`
    and the month bound `1 ≤ fieldValue digits ≤ 12` (the grammar's `constraintsWf`, which is
    exactly what makes `parseNatToBounded`'s range check pass), it succeeds with the `Bounded.LE`
    value whose `.val` is `fieldValue digits`, string unchanged, position advanced. -/
theorem parseWith_month {digits rest : String} (config : Std.Time.FormatConfig)
    (hdigits : IsFixedDigits 2 digits)
    (hbound : 1 ≤ fieldValue digits ∧ fieldValue digits ≤ 12) :
    ∃ (it' : ParseIt) (h : 1 ≤ fieldValue digits ∧ fieldValue digits ≤ 12),
      parseWith config (.M (.inl {padding := 2}))
          ⟨digits ++ rest, (digits ++ rest).startPos⟩
        = ParseResult.success it' (Bounded.LE.ofNat' (fieldValue digits) h) ∧
      (Bounded.LE.ofNat' (fieldValue digits) h).val = fieldValue digits ∧
      it'.1 = digits ++ rest ∧
      it'.2.offset.byteIdx = digits.utf8ByteSize := by
  obtain ⟨it', hpar, hstr, hoff⟩ := parseNum_digits_fieldValue 2 hdigits
  refine ⟨it', hbound, ?_, rfl, hstr, hoff⟩
  show (parseNatToBounded (parseFlexibleNum 2)) _ = _
  unfold parseNatToBounded parseFlexibleNum
  simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind]
  rw [parsec_bind_app, hpar]
  simp only [hbound, and_self, dif_pos]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith` on the two-digit day modifier. As `parseWith_month`, with the day bound
    `1 ≤ fieldValue digits ≤ 31`. -/
theorem parseWith_day {digits rest : String} (config : Std.Time.FormatConfig)
    (hdigits : IsFixedDigits 2 digits)
    (hbound : 1 ≤ fieldValue digits ∧ fieldValue digits ≤ 31) :
    ∃ (it' : ParseIt) (h : 1 ≤ fieldValue digits ∧ fieldValue digits ≤ 31),
      parseWith config (.d {padding := 2})
          ⟨digits ++ rest, (digits ++ rest).startPos⟩
        = ParseResult.success it' (Bounded.LE.ofNat' (fieldValue digits) h) ∧
      (Bounded.LE.ofNat' (fieldValue digits) h).val = fieldValue digits ∧
      it'.1 = digits ++ rest ∧
      it'.2.offset.byteIdx = digits.utf8ByteSize := by
  obtain ⟨it', hpar, hstr, hoff⟩ := parseNum_digits_fieldValue 2 hdigits
  refine ⟨it', hbound, ?_, rfl, hstr, hoff⟩
  show (parseNatToBounded (parseFlexibleNum 2)) _ = _
  unfold parseNatToBounded parseFlexibleNum
  simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind]
  rw [parsec_bind_app, hpar]
  simp only [hbound, and_self, dif_pos]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith` on the two-digit hour modifier `.H`. As `parseWith_month`, with `Hour.Ordinal`
    bounds `0..23`. -/
theorem parseWith_hour {digits rest : String} (config : Std.Time.FormatConfig)
    (hdigits : IsFixedDigits 2 digits) (hbound : fieldValue digits ≤ 23) :
    ∃ (it' : ParseIt) (h : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 23),
      parseWith config (.H {padding := 2}) ⟨digits ++ rest, (digits ++ rest).startPos⟩
        = ParseResult.success it' (Bounded.LE.ofNat' (fieldValue digits) h) ∧
      (Bounded.LE.ofNat' (fieldValue digits) h).val = fieldValue digits ∧
      it'.1 = digits ++ rest ∧ it'.2.offset.byteIdx = digits.utf8ByteSize := by
  obtain ⟨it', hpar, hstr, hoff⟩ := parseNum_digits_fieldValue 2 hdigits
  have hbound' : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 23 := ⟨Nat.zero_le _, hbound⟩
  refine ⟨it', hbound', ?_, rfl, hstr, hoff⟩
  show (parseNatToBounded (parseFlexibleNum 2)) _ = _
  unfold parseNatToBounded parseFlexibleNum
  simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind]
  rw [parsec_bind_app, hpar]
  simp only [hbound', and_self, dif_pos]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith` on the two-digit minute modifier `.m`. As `parseWith_hour`, with `Minute.Ordinal`
    bounds `0..59`. -/
theorem parseWith_minute {digits rest : String} (config : Std.Time.FormatConfig)
    (hdigits : IsFixedDigits 2 digits) (hbound : fieldValue digits ≤ 59) :
    ∃ (it' : ParseIt) (h : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 59),
      parseWith config (.m {padding := 2}) ⟨digits ++ rest, (digits ++ rest).startPos⟩
        = ParseResult.success it' (Bounded.LE.ofNat' (fieldValue digits) h) ∧
      (Bounded.LE.ofNat' (fieldValue digits) h).val = fieldValue digits ∧
      it'.1 = digits ++ rest ∧ it'.2.offset.byteIdx = digits.utf8ByteSize := by
  obtain ⟨it', hpar, hstr, hoff⟩ := parseNum_digits_fieldValue 2 hdigits
  have hbound' : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 59 := ⟨Nat.zero_le _, hbound⟩
  refine ⟨it', hbound', ?_, rfl, hstr, hoff⟩
  show (parseNatToBounded (parseFlexibleNum 2)) _ = _
  unfold parseNatToBounded parseFlexibleNum
  simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind]
  rw [parsec_bind_app, hpar]
  simp only [hbound', and_self, dif_pos]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith` on the two-digit second modifier `.s`. The datetime configs set
    `allowLeapSeconds := false`, so the else-branch parses to `Bounded.LE 0 59` and `expandTop`s to
    `Second.Ordinal true = Bounded.LE 0 60`; the value is unchanged. The `Bounded.LE 0 60` type
    ascriptions on `expandTop` are load-bearing (they pin the existential's value type). -/
theorem parseWith_second {digits rest : String} (config : Std.Time.FormatConfig)
    (hcfg : config.allowLeapSeconds = false)
    (hdigits : IsFixedDigits 2 digits) (hbound : fieldValue digits ≤ 59) :
    ∃ (it' : ParseIt) (h : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 59),
      parseWith config (.s {padding := 2}) ⟨digits ++ rest, (digits ++ rest).startPos⟩
        = ParseResult.success it'
            (((Bounded.LE.ofNat' (fieldValue digits) h).expandTop (by decide) : Bounded.LE 0 60)) ∧
      (((Bounded.LE.ofNat' (fieldValue digits) h).expandTop (by decide) : Bounded.LE 0 60)).val
        = fieldValue digits ∧
      it'.1 = digits ++ rest ∧ it'.2.offset.byteIdx = digits.utf8ByteSize := by
  obtain ⟨it', hpar, hstr, hoff⟩ := parseNum_digits_fieldValue 2 hdigits
  have hbound' : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 59 := ⟨Nat.zero_le _, hbound⟩
  refine ⟨it', hbound', ?_, rfl, hstr, hoff⟩
  show (if config.allowLeapSeconds then parseNatToBounded (parseFlexibleNum 2)
        else (do let res : Bounded.LE 0 59 ← parseNatToBounded (parseFlexibleNum 2)
                 return res.expandTop (by decide))) _ = _
  rw [hcfg]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hinner : (parseNatToBounded (parseFlexibleNum 2) :
        Std.Internal.Parsec ParseIt (Bounded.LE 0 59))
      ⟨digits ++ rest, (digits ++ rest).startPos⟩
      = ParseResult.success it' (Bounded.LE.ofNat' (fieldValue digits) hbound') := by
    unfold parseNatToBounded parseFlexibleNum
    simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind]
    rw [parsec_bind_app, hpar]
    simp only [hbound', and_self, dif_pos]
    rfl
  show (Std.Internal.Parsec.bind
        (parseNatToBounded (parseFlexibleNum 2) : Std.Internal.Parsec ParseIt (Bounded.LE 0 59))
        (fun res => Std.Internal.Parsec.pure
          (res.expandTop (by decide) : Bounded.LE 0 60))) _ = _
  rw [parsec_bind_app, hinner]
  rfl

/-! ### Fraction (millisecond) field: right-padded digit arithmetic

The `.S (.truncated 3)` modifier reads three digits, right-pads to nine `'0'`s (via `rightPadAscii`), and
converts to a nanosecond count — so `SSS` milliseconds become `SSS × 10⁶` nanoseconds. These helpers
establish that `String.toNat!` of a digit string with `k` appended zeros multiplies its value by
`10ᵏ`, then `parseWith_fraction` assembles the modifier reduction. -/

open Std in
/-- `Std.Time` bridge: the `positions` iterator enumerates one position per character, so its
    `length` is the string's character length. The current `rightPadAscii` measures the
    input via `s.positions.length` where v4.30's `rightPad` used `s.length`.) -/
theorem positions_length_eq (s : String) : s.positions.length = s.length := by
  rw [← Iter.length_toList_eq_length, String.toList_positions,
    ← String.length_toList, ← String.Model.map_get_positionsFrom_startPos, List.length_map]

/-- `pushn` over a general base string, as a `toList` append of a character replication. -/
theorem pushn_toList_gen (s : String) (c : Char) (n : Nat) :
    (Nat.repeat (fun s => s.push c) n s).toList = s.toList ++ List.replicate n c := by
  induction n generalizing s with
  | zero => simp [Nat.repeat]
  | succ k ih =>
    show ((Nat.repeat (fun s => s.push c) k s).push c).toList = _
    rw [String.toList_push, ih s, List.append_assoc]
    congr 1
    rw [← List.replicate_succ']

/-- `("".pushn c n).toList = List.replicate n c`. -/
theorem pushn_empty_toList (c : Char) (n : Nat) :
    ("".pushn c n).toList = List.replicate n c := by
  rw [String.pushn_eq_repeat_push, pushn_toList_gen "" c n]
  simp

/-- Appending `'0'`s to a digit string keeps it a digit string. -/
theorem isDigits_append_zeros (sss : String) (h : IsDigits sss) (k : Nat) :
    IsDigits (sss ++ "".pushn '0' k) := by
  refine ⟨?_, ?_⟩
  · have := h.1
    rw [String.length_append]; omega
  · intro c hc
    rw [String.toList_append, List.mem_append] at hc
    cases hc with
    | inl hc => exact h.2 c hc
    | inr hc =>
      rw [pushn_empty_toList] at hc
      have hce := List.eq_of_mem_replicate hc
      rw [hce]; decide

/-- `fieldValue` of a digit string as the explicit base-10 digit fold over its characters. -/
theorem fieldValue_isDigits (s : String) (h : IsDigits s) :
    fieldValue s = List.foldl (fun n c => n * 10 + (c.toNat - 48)) 0 s.toList := by
  unfold fieldValue
  rw [toNat?'_eq_toNat? s h, String.toNat?_eq_some_ofDigitChars (isNat_of_isDigits h)]
  rw [Option.getD_some]
  have hfilter : s.toList.filter (· != '_') = s.toList := by
    apply List.filter_eq_self.mpr
    intro c hc
    have hcd := h.2 c hc
    rw [bne_iff_ne, ne_eq]
    intro he
    rw [he] at hcd
    exact absurd hcd (by decide)
  rw [hfilter, ← foldl_eq_ofDigitChars]

/-- Folding the base-10 digit accumulator over `k` `'0'` characters multiplies the accumulator by
    `10ᵏ`. -/
theorem foldl_replicate_zero (k : Nat) (a : Nat) :
    List.foldl (fun n c => n * 10 + (c.toNat - 48)) a (List.replicate k '0') = a * 10 ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.foldl_cons]
    have hz : ('0'.toNat - 48) = 0 := by decide
    rw [hz, Nat.add_zero, ih (a * 10), Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ j)]

/-- `String.toNat!` of a digit string with `k` appended `'0'`s equals its value times `10ᵏ`. -/
theorem toNat!_append_zeros (sss : String) (h : IsDigits sss) (k : Nat) :
    String.toNat! (sss ++ "".pushn '0' k) = fieldValue sss * (10 ^ k) := by
  have hd : IsDigits (sss ++ "".pushn '0' k) := isDigits_append_zeros sss h k
  rw [toNat!_eq_fieldValue _ hd, fieldValue_isDigits _ hd, fieldValue_isDigits _ h]
  rw [String.toList_append, pushn_empty_toList, List.foldl_append, foldl_replicate_zero]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- `parseWith` on the truncated-3 fraction modifier `.S (.truncated 3)` (the `SSS` millisecond
    field). On a 3-digit `sss`, it succeeds with the `Nanosecond.Ordinal` value `fieldValue sss ×
    10⁶` (milliseconds → nanoseconds), string unchanged, position advanced. The `≤ 999999999` bound
    follows from `fieldValue sss ≤ 999`. -/
theorem parseWith_fraction {sss rest : String} (config : Std.Time.FormatConfig)
    (hsss : IsFixedDigits 3 sss) (hb : fieldValue sss ≤ 999) :
    ∃ (it' : ParseIt) (h : 0 ≤ fieldValue sss * 1000000 ∧ fieldValue sss * 1000000 ≤ 999999999),
      parseWith config (.S (.truncated 3)) ⟨sss ++ rest, (sss ++ rest).startPos⟩
        = ParseResult.success it' (Bounded.LE.ofNat' (fieldValue sss * 1000000) h) ∧
      (Bounded.LE.ofNat' (fieldValue sss * 1000000) h).val = fieldValue sss * 1000000 ∧
      it'.1 = sss ++ rest ∧ it'.2.offset.byteIdx = sss.utf8ByteSize := by
  obtain ⟨hdig, hlen⟩ := hsss
  obtain ⟨it', hpar, hstr, hoff⟩ := exactlyChars_digits 3 hlen hdig.2
  have hbound : 0 ≤ fieldValue sss * 1000000 ∧ fieldValue sss * 1000000 ≤ 999999999 :=
    ⟨Nat.zero_le _, by omega⟩
  have hfval : String.toNat! (rightPadAscii 9 '0' sss) = fieldValue sss * 1000000 := by
    unfold rightPadAscii
    rw [positions_length_eq]
    rw [hlen, show (9 : Nat) - 3 = 6 from rfl, toNat!_append_zeros sss hdig 6,
      show (10 : Nat) ^ 6 = 1000000 from by decide]
  refine ⟨it', hbound, ?_, rfl, hstr, hoff⟩
  show (parseNatToBounded (parseFractionNum 3 9)) ⟨sss ++ rest, (sss ++ rest).startPos⟩ = _
  unfold parseNatToBounded parseFractionNum
  simp only [bind, Bind.bind]
  rw [parsec_bind_app, parsec_map_app, parsec_map_app, hpar]
  simp only []
  rw [hfval, dif_pos hbound]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `pstring` on a literal prefix. Parsing the separator string `sep` at the start of `sep ++ rest`
    succeeds, returning `sep`, leaving the string unchanged, and advancing the position past `sep`.
    Used for the datetime grammar's literal separators (`-`, `:`, `T`, `.`, `Z`, `±`). The guard is
    discharged via the slice `startsWith` prefix characterization, and the offset via the
    `String.Pos.Splits` API. -/
theorem pstring_prefix {sep rest : String} :
    ∃ (it' : ParseIt),
      pstring sep ⟨sep ++ rest, (sep ++ rest).startPos⟩ = ParseResult.success it' sep ∧
      it'.1 = sep ++ rest ∧
      it'.2.offset.byteIdx = sep.utf8ByteSize := by
  unfold pstring
  have hguard : ((sep ++ rest).sliceFrom (sep ++ rest).startPos).startsWith sep = true := by
    rw [String.sliceFrom_startPos, String.Slice.startsWith_string_iff, String.copy_toSlice,
      String.toList_append]
    exact List.prefix_append _ _
  simp only [hguard, ↓reduceIte]
  refine ⟨⟨sep ++ rest, (sep ++ rest).startPos.nextn sep.length⟩, rfl, rfl, ?_⟩
  have hsp := String.splits_nextn_startPos (sep ++ rest) sep.length
  rw [← String.length_toList, String.toList_append,
    List.take_left, String.ofList_toList, String.length_toList] at hsp
  rw [hsp.offset_eq_rawEndPos, String.byteIdx_rawEndPos]

/-! ## Assembling the DateOnly parser: `parseWithDate` sequence

These lemmas lift the primitive rungs to arbitrary interior positions (the `_at` suffix, via
the `String.Pos.Splits` API) and thread the five `parseWithDate` steps of the `yyyy-MM-dd`
format through a `DateBuilder`, culminating in `parseWithDate_dateOnly`. -/

/-! ## Position-general foundations

The existing repo lemmas (`parseWith_year`, `pstring_prefix`, …) are stated with the iterator at
`startPos` of `sub ++ rest`. To compose the five DateOnly parser steps we need to run each parser at
an *interior* position of the single fixed string. The `String.Pos.Splits` API makes this clean:
`exactlyChars_go_digits` is already position-general, so we lift each rung to an "at position `p`"
form, where `p.Splits pre (field ++ rest)`. -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- `exactlyChars` at an arbitrary interior position `p` that splits the string as
    `pre ++ (digits ++ rest)`. -/
theorem exactlyChars_digits_at {s : String} (p : s.Pos) (pre rest digits : String) (n : Nat)
    (hlen : digits.length = n)
    (hdig : ∀ c ∈ digits.toList, c.isDigit = true)
    (hsplit : p.Splits pre (digits ++ rest)) :
    ∃ p' : s.Pos,
      exactlyChars (satisfy Char.isDigit) n ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ digits ∧
      p'.Splits (pre ++ digits) rest := by
  have hgo0 : exactlyChars (satisfy Char.isDigit) n
      = exactlyChars.go (satisfy Char.isDigit) n "" 0 := rfl
  have hsplit' : p.Splits pre (String.ofList digits.toList ++ rest) := by
    rw [String.ofList_toList]; exact hsplit
  have hcnt : n - 0 = digits.toList.length := by rw [String.length_toList, hlen]; omega
  obtain ⟨p', hgo, hsp⟩ := exactlyChars_go_digits digits.toList (by simpa using hdig)
    s n 0 hcnt "" pre rest p hsplit'
  refine ⟨p', ?_, ?_⟩
  · rw [hgo0, hgo]; simp [String.ofList_toList]
  · rw [String.ofList_toList] at hsp; exact hsp

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- `parseNum n` at an interior position, value via `fieldValue`. -/
theorem parseNum_digits_fieldValue_at {s : String} (p : s.Pos) (pre rest digits : String) (n : Nat)
    (hdigits : IsFixedDigits n digits)
    (hsplit : p.Splits pre (digits ++ rest)) :
    ∃ p' : s.Pos,
      parseNum n ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ (fieldValue digits) ∧
      p'.Splits (pre ++ digits) rest := by
  obtain ⟨hdig, hlen⟩ := hdigits
  obtain ⟨p', hpar, hsp⟩ := exactlyChars_digits_at p pre rest digits n hlen hdig.2 hsplit
  refine ⟨p', ?_, hsp⟩
  unfold parseNum
  rw [parsec_map_app, hpar]
  simp only [toNat!_eq_fieldValue digits hdig]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- `parseWith` on the four-digit year modifier, at an interior position. -/
theorem parseWith_year_at {s : String} (p : s.Pos) (pre rest digits : String)
    (config : Std.Time.FormatConfig)
    (hdigits : IsFixedDigits 4 digits)
    (hsplit : p.Splits pre (digits ++ rest)) :
    ∃ p' : s.Pos,
      parseWith config (.y .fourDigit) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ (Int.ofNat (fieldValue digits)) ∧
      p'.Splits (pre ++ digits) rest := by
  obtain ⟨p', hpar, hsp⟩ := parseNum_digits_fieldValue_at p pre rest digits 4 hdigits hsplit
  refine ⟨p', ?_, hsp⟩
  show (Int.ofNat <$> parseNum 4) _ = _
  rw [parsec_map_app, hpar]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith` on the two-digit month modifier, at an interior position. -/
theorem parseWith_month_at {s : String} (p : s.Pos) (pre rest digits : String)
    (config : Std.Time.FormatConfig)
    (hdigits : IsFixedDigits 2 digits)
    (hbound : 1 ≤ fieldValue digits ∧ fieldValue digits ≤ 12)
    (hsplit : p.Splits pre (digits ++ rest)) :
    ∃ (p' : s.Pos) (h : 1 ≤ fieldValue digits ∧ fieldValue digits ≤ 12),
      parseWith config (.M (.inl {padding := 2})) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ (Bounded.LE.ofNat' (fieldValue digits) h) ∧
      p'.Splits (pre ++ digits) rest := by
  obtain ⟨p', hpar, hsp⟩ := parseNum_digits_fieldValue_at p pre rest digits 2 hdigits hsplit
  refine ⟨p', hbound, ?_, hsp⟩
  show (parseNatToBounded (parseFlexibleNum 2)) _ = _
  unfold parseNatToBounded parseFlexibleNum
  simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind]
  rw [parsec_bind_app, hpar]
  simp only [hbound, and_self, dif_pos]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith` on the two-digit day modifier, at an interior position. -/
theorem parseWith_day_at {s : String} (p : s.Pos) (pre rest digits : String)
    (config : Std.Time.FormatConfig)
    (hdigits : IsFixedDigits 2 digits)
    (hbound : 1 ≤ fieldValue digits ∧ fieldValue digits ≤ 31)
    (hsplit : p.Splits pre (digits ++ rest)) :
    ∃ (p' : s.Pos) (h : 1 ≤ fieldValue digits ∧ fieldValue digits ≤ 31),
      parseWith config (.d {padding := 2}) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ (Bounded.LE.ofNat' (fieldValue digits) h) ∧
      p'.Splits (pre ++ digits) rest := by
  obtain ⟨p', hpar, hsp⟩ := parseNum_digits_fieldValue_at p pre rest digits 2 hdigits hsplit
  refine ⟨p', hbound, ?_, hsp⟩
  show (parseNatToBounded (parseFlexibleNum 2)) _ = _
  unfold parseNatToBounded parseFlexibleNum
  simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind]
  rw [parsec_bind_app, hpar]
  simp only [hbound, and_self, dif_pos]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `pstring sep` at an interior position `p` that splits the string as `pre ++ (sep ++ rest)`. -/
theorem pstring_at {s : String} (p : s.Pos) (pre rest sep : String)
    (hsplit : p.Splits pre (sep ++ rest)) :
    ∃ p' : s.Pos,
      pstring sep ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ sep ∧
      p'.Splits (pre ++ sep) rest := by
  unfold pstring
  have hguard : (s.sliceFrom p).startsWith sep = true := by
    rw [String.Slice.startsWith_string_iff, hsplit.copy_sliceFrom_eq, String.toList_append]
    exact List.prefix_append _ _
  simp only [hguard, ↓reduceIte]
  -- The advanced position is `p.nextn sep.length`; relate it to Splits via `Splits.nextn`.
  have hsp := hsplit.nextn sep.length
  rw [← String.length_toList, String.toList_append, List.take_left, String.ofList_toList,
    List.drop_left, String.ofList_toList] at hsp
  exact ⟨p.nextn sep.length, rfl, hsp⟩

/-! ### Offset parsing (`.x .hourMinute`)

The timezone-offset modifier `±hhmm` (`DateWithOffset`/`DateWithOffsetAndMillis`) reduces to
`Std.Time.parseOffset .yes .no false`: a sign character (`<|>` alternation), two bounded 2-digit
fields (no colon, since `withColon = false`), and no seconds. These helpers give the `pchar`,
`seqRight` (`*>`), and `orElse` (`<|>`) reductions, then `parseWith_hourMinute_at` assembles them. -/

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- One-step reduction of `pchar c` on the string iterator (analogue of `satisfy_eq`). -/
theorem pchar_eq (c : Char) (it : ParseIt) :
    pchar c it = if h : Input.hasNext it = true then
        (if Input.curr' it h = c then ParseResult.success (Input.next' it h) c
         else ParseResult.error it (.other s!"expected: '{c}'"))
      else ParseResult.error it .eof := by
  unfold pchar
  simp only [bind, Bind.bind, pure, Pure.pure, attempt]
  rw [parsec_bind_app, any_eq]
  by_cases h : Input.hasNext it = true
  · by_cases hp : Input.curr' it h = c <;>
      simp [h, hp, Std.Internal.Parsec.pure, fail]
  · simp [h]

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `pchar c` at an interior position `p` splitting the string as `pre ++ (singleton c ++ rest)`
    succeeds, consuming `c`. -/
theorem pchar_at {s : String} (p : s.Pos) (pre rest : String) (c : Char)
    (hsplit : p.Splits pre (String.singleton c ++ rest)) :
    ∃ p' : s.Pos,
      pchar c ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ c ∧
      p'.Splits (pre ++ String.singleton c) rest := by
  have hp : p ≠ s.endPos := hsplit.ne_endPos_of_singleton
  have hnext : (p.next hp).Splits (pre ++ String.singleton c) rest := hsplit.next
  have hgetc : p.get hp = c := by
    obtain ⟨t₂', ht⟩ := hsplit.exists_eq_singleton_append hp
    rw [String.singleton_append_inj] at ht
    exact ht.1.symm
  refine ⟨p.next hp, ?_, hnext⟩
  rw [pchar_eq]
  have hhn : Input.hasNext (⟨s, p⟩ : ParseIt) = true := (hasNext_iff s p).mpr hp
  simp only [hhn, dif_pos]
  rw [curr'_eq, next'_eq]
  have hcurr : p.get ((hasNext_iff s p).mp hhn) = c := hgetc
  simp only [hcurr, if_pos]

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `satisfy Char.isDigit` consumes a known digit at an interior position. -/
theorem satisfy_digit_at {s : String} (p : s.Pos) (pre rest : String) (c : Char)
    (hdig : c.isDigit = true)
    (hsplit : p.Splits pre (String.singleton c ++ rest)) :
    ∃ p' : s.Pos,
      (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ =
        ParseResult.success ⟨s, p'⟩ c ∧
      p'.Splits (pre ++ String.singleton c) rest := by
  have hp : p ≠ s.endPos := hsplit.ne_endPos_of_singleton
  have hnext : (p.next hp).Splits (pre ++ String.singleton c) rest := hsplit.next
  have hgetc : p.get hp = c := by
    obtain ⟨t₂', ht⟩ := hsplit.exists_eq_singleton_append hp
    rw [String.singleton_append_inj] at ht
    exact ht.1.symm
  refine ⟨p.next hp, ?_, hnext⟩
  rw [satisfy_eq]
  have hhn : Input.hasNext (⟨s, p⟩ : ParseIt) = true := (hasNext_iff s p).mpr hp
  simp only [hhn, dif_pos]
  rw [curr'_eq, next'_eq]
  have hcurr : p.get ((hasNext_iff s p).mp hhn) = c := hgetc
  simp only [hcurr, hdig, if_true]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- On a known two-digit field, `parseOneOrTwoNum` consumes both digits. -/
theorem parseOneOrTwoNum_digits_fieldValue_at {s : String} (p : s.Pos)
    (pre rest digits : String) (hdigits : IsFixedDigits 2 digits)
    (hsplit : p.Splits pre (digits ++ rest)) :
    ∃ p' : s.Pos,
      parseOneOrTwoNum ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ (fieldValue digits) ∧
      p'.Splits (pre ++ digits) rest := by
  obtain ⟨hdig, hlen⟩ := hdigits
  have hlist_len : digits.toList.length = 2 := by
    rw [String.length_toList, hlen]
  obtain ⟨c₁, c₂, hchars⟩ : ∃ c₁ c₂, digits.toList = [c₁, c₂] := by
    match hl : digits.toList with
    | [a, b] => exact ⟨a, b, rfl⟩
    | [] => rw [hl] at hlist_len; simp at hlist_len
    | [_] => rw [hl] at hlist_len; simp at hlist_len
    | _ :: _ :: _ :: _ => rw [hl] at hlist_len; simp at hlist_len
  have hdigits_eq : digits = String.singleton c₁ ++ String.singleton c₂ := by
    apply String.ext
    simp [hchars]
  have hc₁ : c₁.isDigit = true := hdig.2 c₁ (by rw [hchars]; simp)
  have hc₂ : c₂.isDigit = true := hdig.2 c₂ (by rw [hchars]; simp)
  have hsplit' :
      p.Splits pre (String.singleton c₁ ++ (String.singleton c₂ ++ rest)) := by
    rwa [← String.append_assoc, ← hdigits_eq]
  obtain ⟨p₁, h₁, hsp₁⟩ :=
    satisfy_digit_at p pre (String.singleton c₂ ++ rest) c₁ hc₁ hsplit'
  obtain ⟨p₂, h₂, hsp₂⟩ :=
    satisfy_digit_at p₁ (pre ++ String.singleton c₁) rest c₂ hc₂ hsp₁
  have hoptional :
      optional (satisfy Char.isDigit : Parser Char) (⟨s, p₁⟩ : ParseIt) =
        ParseResult.success ⟨s, p₂⟩ (some c₂) := by
    show ((some <$> (satisfy Char.isDigit : Parser Char)) <|> pure none)
      (⟨s, p₁⟩ : ParseIt) = _
    change Std.Internal.Parsec.orElse
      (some <$> (satisfy Char.isDigit : Parser Char)) (fun _ => pure none)
        (⟨s, p₁⟩ : ParseIt) = _
    unfold Std.Internal.Parsec.orElse Std.Internal.Parsec.tryCatch
    rw [parsec_map_app, h₂]
    rfl
  have hvalue :
      (c₁.toNat - 48) * 10 + (c₂.toNat - 48) = fieldValue digits := by
    rw [fieldValue_isDigits digits hdig, hchars]
    simp
  refine ⟨p₂, ?_, ?_⟩
  · unfold parseOneOrTwoNum
    simp only [bind, Bind.bind]
    rw [parsec_bind_app, h₁]
    simp only []
    rw [parsec_bind_app, hoptional]
    change ParseResult.success (⟨s, p₂⟩ : ParseIt)
      ((c₁.toNat - 48) * 10 + (c₂.toNat - 48)) =
        ParseResult.success (⟨s, p₂⟩ : ParseIt) (fieldValue digits)
    rw [hvalue]
  · rw [hdigits_eq, ← String.append_assoc]
    exact hsp₂

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- Reduction of `*>` (`seqRight`) on the string iterator: run `p`, then `q`, keeping `q`'s value. -/
theorem seqRight_app {α β : Type} (p : Std.Internal.Parsec ParseIt α)
    (q : Std.Internal.Parsec ParseIt β) (it : ParseIt) :
    (p *> q) it = (match p it with
      | .success rem _ => q rem
      | .error pos msg => .error pos msg) := by
  show Std.Internal.Parsec.bind p (fun _ => q) it = _
  rw [parsec_bind_app]

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- Reduction of `<|>` (`orElse`/`tryCatch`) on the string iterator, keying on the `Input.pos`
    equality that decides whether the alternative runs. -/
theorem orElse_app {α : Type} (p q : Std.Internal.Parsec ParseIt α) (it : ParseIt) :
    (p <|> q) it = (match p it with
      | .success rem a => .success rem a
      | .error rem err =>
        if Input.pos it = Input.pos rem then q rem else .error rem err) := by
  show Std.Internal.Parsec.orElse p (fun _ => q) it = _
  unfold Std.Internal.Parsec.orElse Std.Internal.Parsec.tryCatch
  cases hp : p it with
  | success rem a => rfl
  | error rem err => simp only []

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- The sign alternation `(pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1))` at an interior
    position starting with the sign char. Produces `1` for `+` (`neg = false`) and `-1` for `-`. -/
theorem sign_at {s : String} (p : s.Pos) (pre rest : String) (neg : Bool)
    (hsplit : p.Splits pre (String.singleton (if neg then '-' else '+') ++ rest)) :
    ∃ p' : s.Pos,
      ((pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1)) : Parser Int) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ (if neg then (-1 : Int) else 1) ∧
      p'.Splits (pre ++ String.singleton (if neg then '-' else '+')) rest := by
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hsplit ⊢
    obtain ⟨p', hpar, hsp⟩ := pchar_at p pre rest '+' hsplit
    refine ⟨p', ?_, hsp⟩
    rw [orElse_app, seqRight_app, hpar]
    rfl
  | true =>
    simp only [if_true] at hsplit ⊢
    obtain ⟨p', hpar, hsp⟩ := pchar_at p pre rest '-' hsplit
    refine ⟨p', ?_, hsp⟩
    have hp : p ≠ s.endPos := hsplit.ne_endPos_of_singleton
    have hhn : Input.hasNext (⟨s, p⟩ : ParseIt) = true := (hasNext_iff s p).mpr hp
    have hgetc : p.get hp = '-' := by
      obtain ⟨t₂', ht⟩ := hsplit.exists_eq_singleton_append hp
      rw [String.singleton_append_inj] at ht
      exact ht.1.symm
    have hplus : pchar '+' (⟨s, p⟩ : ParseIt)
        = ParseResult.error ⟨s, p⟩ (.other s!"expected: '{'+'}'") := by
      rw [pchar_eq]
      simp only [hhn, dif_pos]
      rw [curr'_eq]
      have hne : ¬ (p.get ((hasNext_iff s p).mp hhn) = '+') := by rw [hgetc]; decide
      simp only [hne, if_false]
    rw [orElse_app, seqRight_app, hplus]
    simp only [Input.pos]
    rw [seqRight_app, hpar]
    rfl

set_option backward.isDefEq.respectTransparency false in
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **`parseWith config (.x .hourMinute)` on a symbolic `±hhmm` offset string, position-general.**
    On `signStr ++ hh ++ mm ++ rest` with `signStr = "-"` (neg) or `"+"`, `hh`/`mm` fixed 2-digit
    fields, `fieldValue hh ≤ 23`, `fieldValue mm ≤ 59`, at a position `p` splitting
    `pre (signStr ++ hh ++ mm ++ rest)`, it succeeds producing
    `Offset.ofSeconds ⟨(fieldValue hh × 3600 + fieldValue mm × 60) × sign⟩` (sign `+`→1, `-`→-1),
    advancing past the sign, `hh` and `mm`. -/
theorem parseWith_hourMinute_at {s : String} (p : s.Pos) (pre rest hh mm : String)
    (neg : Bool) (config : Std.Time.FormatConfig)
    (hhh : IsFixedDigits 2 hh) (hmm : IsFixedDigits 2 mm)
    (hhb : fieldValue hh ≤ 23) (hmb : fieldValue mm ≤ 59)
    (hsplit : p.Splits pre
      (String.singleton (if neg then '-' else '+') ++ (hh ++ (mm ++ rest)))) :
    ∃ p' : s.Pos,
      parseWith config (.x .hourMinute) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩
            (TimeZone.Offset.ofSeconds
              ⟨((fieldValue hh : Int) * 3600 + (fieldValue mm : Int) * 60)
                * (if neg then -1 else 1)⟩) ∧
      p'.Splits (pre ++ String.singleton (if neg then '-' else '+') ++ hh ++ mm) rest := by
  obtain ⟨p1, hsign, hsp1⟩ := sign_at p pre (hh ++ (mm ++ rest)) neg hsplit
  obtain ⟨p2, hpar2, hsp2⟩ := parseOneOrTwoNum_digits_fieldValue_at p1
    (pre ++ String.singleton (if neg then '-' else '+')) (mm ++ rest) hh hhh hsp1
  obtain ⟨p3, hpar3, hsp3⟩ := parseOneOrTwoNum_digits_fieldValue_at p2
    (pre ++ String.singleton (if neg then '-' else '+') ++ hh) rest mm hmm hsp2
  refine ⟨p3, ?_, by
    have := hsp3
    rwa [String.append_assoc, String.append_assoc, ← String.append_assoc,
      ← String.append_assoc] at this ⊢⟩
  show Std.Time.parseOffset .yes .no false ⟨s, p⟩ = _
  unfold Std.Time.parseOffset
  simp only [bind, Bind.bind]
  rw [parsec_bind_app, hsign]
  simp only []
  rw [parsec_bind_app]
  have hpure : ∀ (a : Int) (q : ParseIt),
      (Pure.pure a : Parser Int) q = ParseResult.success q a := fun _ _ => rfl
  simp only [parsec_map_app, parsec_bind_app, hpar2, hpure]
  have hhle : ¬ (((fieldValue hh : Int)) < 0 ∨ ((fieldValue hh : Int)) > 23) := by
    have : ((fieldValue hh : Int)) ≤ 23 := by exact_mod_cast hhb
    omega
  simp only [hhle, if_false]
  rw [parsec_bind_app, parsec_map_app, seqRight_app]
  have hcolon : (if false = true then pchar ':' else Pure.pure ':') (⟨s, p2⟩ : ParseIt)
      = ParseResult.success ⟨s, p2⟩ ':' := by simp only [Bool.false_eq_true, if_false]; rfl
  rw [hcolon]
  simp only []
  rw [parsec_map_app, parsec_bind_app, hpar3]
  simp only [hpure]
  have hmle : ¬ (((fieldValue mm : Int)) > 59) := by
    have : ((fieldValue mm : Int)) ≤ 59 := by exact_mod_cast hmb
    omega
  simp only [hmle, if_false]
  rw [parsec_bind_app]
  show ParseResult.success (⟨s, p3⟩ : ParseIt)
      (TimeZone.Offset.ofSeconds { val :=
        (Hour.Offset.toSeconds { val := (fieldValue hh : Int) }
          + ((some { val := (fieldValue mm : Int) } : Option Minute.Offset).getD 0).toSeconds
          + (none : Option Second.Offset).getD 0).val * (if neg then -1 else 1) }) = _
  have eh : (Hour.Offset.toSeconds { val := (fieldValue hh : Int) }).val
      = (fieldValue hh : Int) * 3600 := by
    unfold Hour.Offset.toSeconds UnitVal.cast UnitVal.mul; rfl
  have em : (Minute.Offset.toSeconds { val := (fieldValue mm : Int) }).val
      = (fieldValue mm : Int) * 60 := by
    unfold Minute.Offset.toSeconds UnitVal.cast UnitVal.mul; rfl
  have hval : (Hour.Offset.toSeconds { val := (fieldValue hh : Int) }
        + ((some { val := (fieldValue mm : Int) } : Option Minute.Offset).getD 0).toSeconds
        + (none : Option Second.Offset).getD 0).val
      = (fieldValue hh : Int) * 3600 + (fieldValue mm : Int) * 60 := by
    show (Hour.Offset.toSeconds { val := (fieldValue hh : Int) }).val
        + (Minute.Offset.toSeconds { val := (fieldValue mm : Int) }).val + (0 : Int)
        = (fieldValue hh : Int) * 3600 + (fieldValue mm : Int) * 60
    rw [eh, em]; omega
  rw [hval]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith` on the two-digit hour modifier `.H`, at an interior position. -/
theorem parseWith_hour_at {s : String} (p : s.Pos) (pre rest digits : String)
    (config : Std.Time.FormatConfig)
    (hdigits : IsFixedDigits 2 digits) (hbound : fieldValue digits ≤ 23)
    (hsplit : p.Splits pre (digits ++ rest)) :
    ∃ (p' : s.Pos) (h : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 23),
      parseWith config (.H {padding := 2}) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ (Bounded.LE.ofNat' (fieldValue digits) h) ∧
      p'.Splits (pre ++ digits) rest := by
  obtain ⟨p', hpar, hsp⟩ := parseNum_digits_fieldValue_at p pre rest digits 2 hdigits hsplit
  have hbound' : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 23 := ⟨Nat.zero_le _, hbound⟩
  refine ⟨p', hbound', ?_, hsp⟩
  show (parseNatToBounded (parseFlexibleNum 2)) _ = _
  unfold parseNatToBounded parseFlexibleNum
  simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind]
  rw [parsec_bind_app, hpar]
  simp only [hbound', and_self, dif_pos]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith` on the two-digit minute modifier `.m`, at an interior position. -/
theorem parseWith_minute_at {s : String} (p : s.Pos) (pre rest digits : String)
    (config : Std.Time.FormatConfig)
    (hdigits : IsFixedDigits 2 digits) (hbound : fieldValue digits ≤ 59)
    (hsplit : p.Splits pre (digits ++ rest)) :
    ∃ (p' : s.Pos) (h : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 59),
      parseWith config (.m {padding := 2}) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ (Bounded.LE.ofNat' (fieldValue digits) h) ∧
      p'.Splits (pre ++ digits) rest := by
  obtain ⟨p', hpar, hsp⟩ := parseNum_digits_fieldValue_at p pre rest digits 2 hdigits hsplit
  have hbound' : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 59 := ⟨Nat.zero_le _, hbound⟩
  refine ⟨p', hbound', ?_, hsp⟩
  show (parseNatToBounded (parseFlexibleNum 2)) _ = _
  unfold parseNatToBounded parseFlexibleNum
  simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind]
  rw [parsec_bind_app, hpar]
  simp only [hbound', and_self, dif_pos]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith` on the two-digit second modifier `.s`, at an interior position.
    `allowLeapSeconds := false`, so it parses to `Bounded.LE 0 59` and `expandTop`s to
    `Bounded.LE 0 60`; the value is unchanged. -/
theorem parseWith_second_at {s : String} (p : s.Pos) (pre rest digits : String)
    (config : Std.Time.FormatConfig)
    (hcfg : config.allowLeapSeconds = false)
    (hdigits : IsFixedDigits 2 digits) (hbound : fieldValue digits ≤ 59)
    (hsplit : p.Splits pre (digits ++ rest)) :
    ∃ (p' : s.Pos) (h : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 59),
      parseWith config (.s {padding := 2}) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩
            ((Bounded.LE.ofNat' (fieldValue digits) h).expandTop (by decide) : Bounded.LE 0 60) ∧
      p'.Splits (pre ++ digits) rest := by
  obtain ⟨p', hpar, hsp⟩ := parseNum_digits_fieldValue_at p pre rest digits 2 hdigits hsplit
  have hbound' : 0 ≤ fieldValue digits ∧ fieldValue digits ≤ 59 := ⟨Nat.zero_le _, hbound⟩
  refine ⟨p', hbound', ?_, hsp⟩
  show (if config.allowLeapSeconds then parseNatToBounded (parseFlexibleNum 2)
        else (do let res : Bounded.LE 0 59 ← parseNatToBounded (parseFlexibleNum 2)
                 return res.expandTop (by decide))) _ = _
  rw [hcfg]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hinner : (parseNatToBounded (parseFlexibleNum 2) :
        Std.Internal.Parsec ParseIt (Bounded.LE 0 59))
      ⟨s, p⟩
      = ParseResult.success ⟨s, p'⟩ (Bounded.LE.ofNat' (fieldValue digits) hbound') := by
    unfold parseNatToBounded parseFlexibleNum
    simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind]
    rw [parsec_bind_app, hpar]
    simp only [hbound', and_self, dif_pos]
    rfl
  show (Std.Internal.Parsec.bind
        (parseNatToBounded (parseFlexibleNum 2) : Std.Internal.Parsec ParseIt (Bounded.LE 0 59))
        (fun res => Std.Internal.Parsec.pure
          (res.expandTop (by decide) : Bounded.LE 0 60))) _ = _
  rw [parsec_bind_app, hinner]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- `parseWith` on the truncated-3 fraction modifier `.S (.truncated 3)` (`SSS` millisecond
    field), at an interior position. On a 3-digit `sss`, succeeds with the `Nanosecond.Ordinal`
    value `fieldValue sss × 10⁶`. -/
theorem parseWith_fraction_at {s : String} (p : s.Pos) (pre rest sss : String)
    (config : Std.Time.FormatConfig)
    (hsss : IsFixedDigits 3 sss) (hb : fieldValue sss ≤ 999)
    (hsplit : p.Splits pre (sss ++ rest)) :
    ∃ (p' : s.Pos)
      (h : 0 ≤ fieldValue sss * 1000000 ∧ fieldValue sss * 1000000 ≤ 999999999),
      parseWith config (.S (.truncated 3)) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ (Bounded.LE.ofNat' (fieldValue sss * 1000000) h) ∧
      p'.Splits (pre ++ sss) rest := by
  obtain ⟨hdig, hlen⟩ := hsss
  obtain ⟨p', hpar, hsp⟩ := exactlyChars_digits_at p pre rest sss 3 hlen hdig.2 hsplit
  have hbound : 0 ≤ fieldValue sss * 1000000 ∧ fieldValue sss * 1000000 ≤ 999999999 :=
    ⟨Nat.zero_le _, by omega⟩
  have hfval : String.toNat! (rightPadAscii 9 '0' sss) = fieldValue sss * 1000000 := by
    unfold rightPadAscii
    rw [positions_length_eq]
    rw [hlen, show (9 : Nat) - 3 = 6 from rfl, toNat!_append_zeros sss hdig 6,
      show (10 : Nat) ^ 6 = 1000000 from by decide]
  refine ⟨p', hbound, ?_, hsp⟩
  show (parseNatToBounded (parseFractionNum 3 9)) ⟨s, p⟩ = _
  unfold parseNatToBounded parseFractionNum
  simp only [bind, Bind.bind]
  rw [parsec_bind_app, parsec_map_app, parsec_map_app, hpar]
  simp only []
  rw [hfval, dif_pos hbound]
  rfl

open Std.Time.GenericFormat

/-! ## `parseWithDate` single-step lemmas (position-general)

Each combines the `parseWithDate` `do`-block reduction with the corresponding `parseWith`/`pstring`
position-general lemma, producing the advanced builder and threaded position. -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- One `parseWithDate` step on the year modifier. -/
theorem step_year {s : String} (p : s.Pos) (pre rest year : String) (b : DateBuilder)
    (config : FormatConfig) (hy : IsFixedDigits 4 year) (hsplit : p.Splits pre (year ++ rest)) :
    ∃ p' : s.Pos,
      parseWithDate b config (.modifier (.y .fourDigit)) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ { b with y := some (Int.ofNat (fieldValue year)) } ∧
      p'.Splits (pre ++ year) rest := by
  obtain ⟨p', hpar, hsp⟩ := parseWith_year_at p pre rest year config hy hsplit
  refine ⟨p', ?_, hsp⟩
  unfold parseWithDate
  simp only [bind, Bind.bind, pure]
  rw [parsec_bind_app, hpar]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- One `parseWithDate` step on the month modifier. -/
theorem step_month {s : String} (p : s.Pos) (pre rest month : String) (b : DateBuilder)
    (config : FormatConfig) (hm : IsFixedDigits 2 month)
    (hbound : 1 ≤ fieldValue month ∧ fieldValue month ≤ 12)
    (hsplit : p.Splits pre (month ++ rest)) :
    ∃ (p' : s.Pos) (h : 1 ≤ fieldValue month ∧ fieldValue month ≤ 12),
      parseWithDate b config (.modifier (.M (.inl {padding := 2}))) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩
            { b with M := some (Bounded.LE.ofNat' (fieldValue month) h) } ∧
      p'.Splits (pre ++ month) rest := by
  obtain ⟨p', h, hpar, hsp⟩ := parseWith_month_at p pre rest month config hm hbound hsplit
  refine ⟨p', h, ?_, hsp⟩
  unfold parseWithDate
  simp only [bind, Bind.bind, pure]
  rw [parsec_bind_app, hpar]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- One `parseWithDate` step on the day modifier. -/
theorem step_day {s : String} (p : s.Pos) (pre rest day : String) (b : DateBuilder)
    (config : FormatConfig) (hd : IsFixedDigits 2 day)
    (hbound : 1 ≤ fieldValue day ∧ fieldValue day ≤ 31)
    (hsplit : p.Splits pre (day ++ rest)) :
    ∃ (p' : s.Pos) (h : 1 ≤ fieldValue day ∧ fieldValue day ≤ 31),
      parseWithDate b config (.modifier (.d {padding := 2})) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ { b with d := some (Bounded.LE.ofNat' (fieldValue day) h) } ∧
      p'.Splits (pre ++ day) rest := by
  obtain ⟨p', h, hpar, hsp⟩ := parseWith_day_at p pre rest day config hd hbound hsplit
  refine ⟨p', h, ?_, hsp⟩
  unfold parseWithDate
  simp only [bind, Bind.bind, pure]
  rw [parsec_bind_app, hpar]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- One `parseWithDate` step on a string-literal separator. -/
theorem step_sep {s : String} (p : s.Pos) (pre rest sep : String) (b : DateBuilder)
    (config : FormatConfig) (hsplit : p.Splits pre (sep ++ rest)) :
    ∃ p' : s.Pos,
      parseWithDate b config (.string sep) ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ b ∧
      p'.Splits (pre ++ sep) rest := by
  obtain ⟨p', hpar, hsp⟩ := pstring_at p pre rest sep hsplit
  refine ⟨p', ?_, hsp⟩
  unfold parseWithDate
  simp only [pure, SeqRight.seqRight]
  show (Std.Internal.Parsec.bind (pstring sep) (fun _ => Std.Internal.Parsec.pure b)) ⟨s, p⟩ = _
  rw [parsec_bind_app, hpar]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- One `parseWithDate` step on the hour modifier. -/
theorem step_hour {s : String} (p : s.Pos) (pre rest hh : String) (b : DateBuilder)
    (config : FormatConfig) (hh2 : IsFixedDigits 2 hh) (hbound : fieldValue hh ≤ 23)
    (hsplit : p.Splits pre (hh ++ rest)) :
    ∃ (p' : s.Pos) (h : 0 ≤ fieldValue hh ∧ fieldValue hh ≤ 23),
      parseWithDate b config (.modifier (.H {padding := 2})) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ { b with H := some (Bounded.LE.ofNat' (fieldValue hh) h) } ∧
      p'.Splits (pre ++ hh) rest := by
  obtain ⟨p', h, hpar, hsp⟩ := parseWith_hour_at p pre rest hh config hh2 hbound hsplit
  refine ⟨p', h, ?_, hsp⟩
  unfold parseWithDate
  simp only [bind, Bind.bind, pure]
  rw [parsec_bind_app, hpar]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- One `parseWithDate` step on the minute modifier. -/
theorem step_minute {s : String} (p : s.Pos) (pre rest mm : String) (b : DateBuilder)
    (config : FormatConfig) (hm2 : IsFixedDigits 2 mm) (hbound : fieldValue mm ≤ 59)
    (hsplit : p.Splits pre (mm ++ rest)) :
    ∃ (p' : s.Pos) (h : 0 ≤ fieldValue mm ∧ fieldValue mm ≤ 59),
      parseWithDate b config (.modifier (.m {padding := 2})) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ { b with m := some (Bounded.LE.ofNat' (fieldValue mm) h) } ∧
      p'.Splits (pre ++ mm) rest := by
  obtain ⟨p', h, hpar, hsp⟩ := parseWith_minute_at p pre rest mm config hm2 hbound hsplit
  refine ⟨p', h, ?_, hsp⟩
  unfold parseWithDate
  simp only [bind, Bind.bind, pure]
  rw [parsec_bind_app, hpar]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- One `parseWithDate` step on the second modifier. -/
theorem step_second {s : String} (p : s.Pos) (pre rest ss : String) (b : DateBuilder)
    (config : FormatConfig) (hcfg : config.allowLeapSeconds = false)
    (hs2 : IsFixedDigits 2 ss) (hbound : fieldValue ss ≤ 59)
    (hsplit : p.Splits pre (ss ++ rest)) :
    ∃ (p' : s.Pos) (h : 0 ≤ fieldValue ss ∧ fieldValue ss ≤ 59),
      parseWithDate b config (.modifier (.s {padding := 2})) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩
            { b with s := some ((Bounded.LE.ofNat' (fieldValue ss) h).expandTop (by decide)
                                : Bounded.LE 0 60) } ∧
      p'.Splits (pre ++ ss) rest := by
  obtain ⟨p', h, hpar, hsp⟩ := parseWith_second_at p pre rest ss config hcfg hs2 hbound hsplit
  refine ⟨p', h, ?_, hsp⟩
  unfold parseWithDate
  simp only [bind, Bind.bind, pure]
  rw [parsec_bind_app, hpar]
  rfl

open Std.Internal.Parsec Std.Time Std.Time.GenericFormat in
/-- Cons-application reduction for the tail-recursive `parser.go`: running it on `x :: xs` at `it`
    first runs `parseWithDate` for `x`, then continues with the advanced builder on `xs`. -/
theorem go_cons_app (config : FormatConfig) (aw : Awareness) (b : DateBuilder)
    (x : FormatPart) (xs : FormatString) (it : Σ s : String, s.Pos) :
    parser.go config aw b (x :: xs) it
      = (match parseWithDate b config x it with
         | .success rem a => parser.go config aw a xs rem
         | .error pos msg => .error pos msg) := by
  show (Std.Internal.Parsec.bind (parseWithDate b config x) (parser.go config aw · xs)) it = _
  rw [parsec_bind_app]
  cases parseWithDate b config x it <;> rfl

-- Execute the shared `yyyy-MM-dd'T'HH:mm:ss` prefix, leaving an arbitrary format suffix.
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal
  Std.Time.GenericFormat in
theorem parseWithDate_datetimePrefix {c : DatetimeComponents} (tp : TimePart) (tail : String)
    (config : FormatConfig) (hcfg : config.allowLeapSeconds = false)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp)
    (suf : FormatString) :
    ∃ (hm : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12)
      (hd : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31)
      (hh : 0 ≤ fieldValue tp.time.hours ∧ fieldValue tp.time.hours ≤ 23)
      (hmin : 0 ≤ fieldValue tp.time.minutes ∧ fieldValue tp.time.minutes ≤ 59)
      (hsec : 0 ≤ fieldValue tp.time.seconds ∧ fieldValue tp.time.seconds ≤ 59)
      (p : (c.date.asString ++ "T" ++ tp.time.asString ++ tail).Pos),
      parser.go config .any {}
          ([.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
            .string "-", .modifier (.d {padding := 2}), .string "T",
            .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
            .string ":", .modifier (.s {padding := 2})] ++ suf)
          ⟨c.date.asString ++ "T" ++ tp.time.asString ++ tail,
            (c.date.asString ++ "T" ++ tp.time.asString ++ tail).startPos⟩
        = parser.go config .any
            { ({} : DateBuilder) with
              y := some (Int.ofNat (fieldValue c.date.year)),
              M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
              d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
              H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
              m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
              s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop
                (by decide) : Bounded.LE 0 60) }
            suf ⟨c.date.asString ++ "T" ++ tp.time.asString ++ tail, p⟩ ∧
      p.Splits (c.date.asString ++ "T" ++ tp.time.asString) tail := by
  obtain ⟨hdatesyn, htimesyn⟩ := hsyn
  simp only [htime] at htimesyn
  obtain ⟨httime, _htmillis, _htzone⟩ := htimesyn
  obtain ⟨hhh, hmmi, hss⟩ := httime
  obtain ⟨hy, hmm, hdd⟩ := hdatesyn
  obtain ⟨hdatecon, htimecon⟩ := hcon
  simp only [htime] at htimecon
  obtain ⟨httimecon, _htzonecon⟩ := htimecon
  obtain ⟨hhbound, hminbound, hsecbound⟩ := httimecon
  obtain ⟨hm1, hm2, hd1, hd2⟩ := hdatecon
  have hmbound : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12 := ⟨hm1, hm2⟩
  have hdaysle : daysInMonth (fieldValue c.date.year) (fieldValue c.date.month) ≤ 31 := by
    unfold daysInMonth
    split
    · omega
    · split
      · split <;> omega
      · omega
  have hdbound : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31 :=
    ⟨hd1, Nat.le_trans hd2 hdaysle⟩
  have hassoc : c.date.asString ++ "T" ++ tp.time.asString ++ tail
      = c.date.year ++ ("-" ++ (c.date.month ++ ("-" ++ (c.date.day ++ ("T" ++
          (tp.time.hours ++ (":" ++ (tp.time.minutes ++ (":" ++
            (tp.time.seconds ++ tail)))))))))) := by
    simp only [DateComponents.asString, TimeComponents.asString, String.append_assoc]
  have hsplit0 : (c.date.asString ++ "T" ++ tp.time.asString ++ tail).startPos.Splits ""
      (c.date.year ++ ("-" ++ (c.date.month ++ ("-" ++ (c.date.day ++ ("T" ++
        (tp.time.hours ++ (":" ++ (tp.time.minutes ++ (":" ++
          (tp.time.seconds ++ tail))))))))))) := by
    rw [← hassoc]
    exact String.splits_startPos _
  obtain ⟨p1, hpar1, hsp1⟩ :=
    step_year (c.date.asString ++ "T" ++ tp.time.asString ++ tail).startPos ""
      ("-" ++ (c.date.month ++ ("-" ++ (c.date.day ++ ("T" ++
        (tp.time.hours ++ (":" ++ (tp.time.minutes ++ (":" ++
          (tp.time.seconds ++ tail))))))))))
      c.date.year ({} : DateBuilder) config hy hsplit0
  rw [String.empty_append] at hsp1
  obtain ⟨p2, hpar2, hsp2⟩ :=
    step_sep p1 c.date.year
      (c.date.month ++ ("-" ++ (c.date.day ++ ("T" ++
        (tp.time.hours ++ (":" ++ (tp.time.minutes ++ (":" ++
          (tp.time.seconds ++ tail)))))))))
      "-" { ({} : DateBuilder) with y := some (Int.ofNat (fieldValue c.date.year)) } config hsp1
  obtain ⟨p3, hm', hpar3, hsp3⟩ :=
    step_month p2 (c.date.year ++ "-")
      ("-" ++ (c.date.day ++ ("T" ++
        (tp.time.hours ++ (":" ++ (tp.time.minutes ++ (":" ++
          (tp.time.seconds ++ tail))))))))
      c.date.month { ({} : DateBuilder) with y := some (Int.ofNat (fieldValue c.date.year)) }
      config hmm hmbound hsp2
  let bYM : DateBuilder :=
    { ({} : DateBuilder) with y := some (Int.ofNat (fieldValue c.date.year)),
                              M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm') }
  obtain ⟨p4, hpar4, hsp4⟩ :=
    step_sep p3 (c.date.year ++ "-" ++ c.date.month)
      (c.date.day ++ ("T" ++
        (tp.time.hours ++ (":" ++ (tp.time.minutes ++ (":" ++ (tp.time.seconds ++ tail)))))))
      "-" bYM config hsp3
  obtain ⟨p5, hd', hpar5, hsp5⟩ :=
    step_day p4 (c.date.year ++ "-" ++ c.date.month ++ "-")
      ("T" ++ (tp.time.hours ++ (":" ++ (tp.time.minutes ++ (":" ++ (tp.time.seconds ++ tail))))))
      c.date.day bYM config hdd hdbound hsp4
  let bYMD : DateBuilder :=
    { bYM with d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd') }
  obtain ⟨p6, hpar6, hsp6⟩ :=
    step_sep p5 (c.date.year ++ "-" ++ c.date.month ++ "-" ++ c.date.day)
      (tp.time.hours ++ (":" ++ (tp.time.minutes ++ (":" ++ (tp.time.seconds ++ tail)))))
      "T" bYMD config hsp5
  obtain ⟨p7, hh', hpar7, hsp7⟩ :=
    step_hour p6 (c.date.year ++ "-" ++ c.date.month ++ "-" ++ c.date.day ++ "T")
      (":" ++ (tp.time.minutes ++ (":" ++ (tp.time.seconds ++ tail))))
      tp.time.hours bYMD config hhh hhbound hsp6
  let bYMDH : DateBuilder :=
    { bYMD with H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh') }
  obtain ⟨p8, hpar8, hsp8⟩ :=
    step_sep p7
      (c.date.year ++ "-" ++ c.date.month ++ "-" ++ c.date.day ++ "T" ++ tp.time.hours)
      (tp.time.minutes ++ (":" ++ (tp.time.seconds ++ tail)))
      ":" bYMDH config hsp7
  obtain ⟨p9, hmin', hpar9, hsp9⟩ :=
    step_minute p8
      (c.date.year ++ "-" ++ c.date.month ++ "-" ++ c.date.day ++ "T" ++ tp.time.hours ++ ":")
      (":" ++ (tp.time.seconds ++ tail))
      tp.time.minutes bYMDH config hmmi hminbound hsp8
  let bYMDHm : DateBuilder :=
    { bYMDH with m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin') }
  obtain ⟨p10, hpar10, hsp10⟩ :=
    step_sep p9
      (c.date.year ++ "-" ++ c.date.month ++ "-" ++ c.date.day ++ "T" ++ tp.time.hours ++ ":"
        ++ tp.time.minutes)
      (tp.time.seconds ++ tail) ":" bYMDHm config hsp9
  obtain ⟨p11, hsec', hpar11, hsp11⟩ :=
    step_second p10
      (c.date.year ++ "-" ++ c.date.month ++ "-" ++ c.date.day ++ "T" ++ tp.time.hours ++ ":"
        ++ tp.time.minutes ++ ":")
      tail tp.time.seconds bYMDHm config hcfg hss hsecbound hsp10
  refine ⟨hm', hd', hh', hmin', hsec', p11, ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, go_cons_app, hpar1, hpar2, hpar3, hpar4,
      hpar5, hpar6, hpar7, hpar8, hpar9, hpar10, hpar11, bYM, bYMD, bYMDH, bYMDHm]
  · have hfold : c.date.year ++ "-" ++ c.date.month ++ "-" ++ c.date.day ++ "T"
          ++ tp.time.hours ++ ":" ++ tp.time.minutes ++ ":" ++ tp.time.seconds =
        c.date.asString ++ "T" ++ tp.time.asString := by
      simp only [DateComponents.asString, TimeComponents.asString, String.append_assoc]
    rw [hfold] at hsp11
    exact hsp11

open Cedar.Spec.Ext in
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **Main result.** Running the DateOnly format's `parser.go` from the empty builder on the full
    rendering `d.year ++ "-" ++ d.month ++ "-" ++ d.day` of a well-formed date threads through all
    five `parseWithDate` steps and reaches the terminal `[]` case at the end of the string, with a
    builder whose `y`, `M`, `d` fields are set to the parsed field values and every other field
    left at its default `none`. Phrased as an equality to `parser.go` on `[]` at `full.endPos`, so
    both "the whole string is consumed" (the position is `endPos`) and "the builder is exactly the
    three-field record" are visible in the statement. -/
theorem parseWithDate_dateOnly {d : DateComponents} (config : FormatConfig)
    (hsyn : d.syntaxWf) (hcon : d.constraintsWf) :
    ∃ (hm : 1 ≤ fieldValue d.month ∧ fieldValue d.month ≤ 12)
      (hd : 1 ≤ fieldValue d.day ∧ fieldValue d.day ≤ 31),
      parser.go config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2})]
          ⟨d.asString, d.asString.startPos⟩
        = parser.go config .any
            { ({} : DateBuilder) with
              y := some (Int.ofNat (fieldValue d.year)),
              M := some (Bounded.LE.ofNat' (fieldValue d.month) hm),
              d := some (Bounded.LE.ofNat' (fieldValue d.day) hd) }
            [] ⟨d.asString, d.asString.endPos⟩ := by
  obtain ⟨hy, hmm, hdd⟩ := hsyn
  -- Numeric bounds from constraintsWf (day bound relaxed to ≤ 31 via daysInMonth ≤ 31).
  obtain ⟨hm1, hm2, hd1, hd2⟩ := hcon
  have hmbound : 1 ≤ fieldValue d.month ∧ fieldValue d.month ≤ 12 := ⟨hm1, hm2⟩
  have hdaysle : daysInMonth (fieldValue d.year) (fieldValue d.month) ≤ 31 := by
    unfold daysInMonth
    split
    · omega
    · split
      · split <;> omega
      · omega
  have hdbound : 1 ≤ fieldValue d.day ∧ fieldValue d.day ≤ 31 :=
    ⟨hd1, Nat.le_trans hd2 hdaysle⟩
  -- Re-associate `d.asString` so each field sits at the front of the remaining suffix.
  have hassoc : d.asString = d.year ++ ("-" ++ (d.month ++ ("-" ++ d.day))) := by
    unfold DateComponents.asString
    rw [String.append_assoc, String.append_assoc, String.append_assoc]
  -- Initial split at startPos.
  have hsplit0 : d.asString.startPos.Splits "" (d.year ++ ("-" ++ (d.month ++ ("-" ++ d.day)))) := by
    rw [← hassoc]; exact String.splits_startPos d.asString
  -- Step 1: year.
  obtain ⟨p1, hpar1, hsp1⟩ :=
    step_year d.asString.startPos "" ("-" ++ (d.month ++ ("-" ++ d.day))) d.year {} config hy
      hsplit0
  -- Step 2: separator "-".
  rw [String.empty_append] at hsp1
  obtain ⟨p2, hpar2, hsp2⟩ :=
    step_sep p1 d.year (d.month ++ ("-" ++ d.day)) "-"
      { ({} : DateBuilder) with y := some (Int.ofNat (fieldValue d.year)) } config hsp1
  -- Step 3: month.
  obtain ⟨p3, hm', hpar3, hsp3⟩ :=
    step_month p2 (d.year ++ "-") ("-" ++ d.day) d.month
      { ({} : DateBuilder) with y := some (Int.ofNat (fieldValue d.year)) } config hmm hmbound hsp2
  -- Builder after month is inserted (shared by steps 4 and 5).
  let bYM : DateBuilder :=
    { ({} : DateBuilder) with y := some (Int.ofNat (fieldValue d.year)),
                              M := some (Bounded.LE.ofNat' (fieldValue d.month) hm') }
  -- Step 4: separator "-".
  obtain ⟨p4, hpar4, hsp4⟩ :=
    step_sep p3 (d.year ++ "-" ++ d.month) d.day "-" bYM config hsp3
  -- Step 5: day.
  obtain ⟨p5, hd', hpar5, hsp5⟩ :=
    step_day p4 (d.year ++ "-" ++ d.month ++ "-") "" d.day bYM config hdd hdbound
      (by rw [String.append_empty]; exact hsp4)
  -- The final position p5 splits `d.asString` as `_ ++ ""`, i.e. it is `endPos`.
  have hp5end : p5 = d.asString.endPos := hsp5.eq_endPos_iff.mpr rfl
  refine ⟨hm', hd', ?_⟩
  -- Thread the five reductions through `go_cons_app`; `simp only` iota-reduces the `match` on each
  -- `.success` constructor between steps (which `rw` alone would not) and reduces the `bYM`
  -- projections on the final builder.
  simp only [go_cons_app, hpar1, hpar2, hpar3, hpar4, hpar5, hp5end, bYM]

open Cedar.Spec.Ext in
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **DateUTC sequence.** Running the DateUTC format's `parser.go` (`yyyy-MM-dd'T'HH:mm:ss'Z'`) from
    the empty builder on the rendering of a well-formed UTC-form datetime threads through all twelve
    `parseWithDate` steps to the terminal `[]` at end of string, with a builder whose
    `y`/`M`/`d`/`H`/`m`/`s` fields are set to the parsed field values. -/
theorem parseWithDate_dateUTC {c : DatetimeComponents} (tp : TimePart) (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = none) :
    ∃ (hm : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12)
      (hd : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31)
      (hh : 0 ≤ fieldValue tp.time.hours ∧ fieldValue tp.time.hours ≤ 23)
      (hmin : 0 ≤ fieldValue tp.time.minutes ∧ fieldValue tp.time.minutes ≤ 59)
      (hsec : 0 ≤ fieldValue tp.time.seconds ∧ fieldValue tp.time.seconds ≤ 59),
      parser.go config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2}), .string "T",
           .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
           .string ":", .modifier (.s {padding := 2}), .string "Z"]
          ⟨c.asString, c.asString.startPos⟩
        = parser.go config .any
            { ({} : DateBuilder) with
              y := some (Int.ofNat (fieldValue c.date.year)),
              M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
              d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
              H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
              m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
              s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                          : Bounded.LE 0 60) }
            [] ⟨c.asString, c.asString.endPos⟩ := by
  have hcstr : c.asString = c.date.asString ++ "T" ++ tp.time.asString ++ "Z" := by
    simp only [DatetimeComponents.asString, TimePart.asString, htime, hmillis, hutc,
      Zone.asString, String.append_empty, String.append_assoc]
  obtain ⟨hm, hd, hh, hmin, hsec, p, hgo, hsp⟩ :=
    parseWithDate_datetimePrefix tp "Z" config hcfg hsyn hcon htime [.string "Z"]
  let b : DateBuilder :=
    { ({} : DateBuilder) with
      y := some (Int.ofNat (fieldValue c.date.year)),
      M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
      d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
      H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
      m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
      s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop
        (by decide) : Bounded.LE 0 60) }
  obtain ⟨p', hpar, hsp'⟩ := step_sep p
    (c.date.asString ++ "T" ++ tp.time.asString) "" "Z" b config
    (by rw [String.append_empty]; exact hsp)
  have hp' : p' = (c.date.asString ++ "T" ++ tp.time.asString ++ "Z").endPos :=
    hsp'.eq_endPos_iff.mpr rfl
  refine ⟨hm, hd, hh, hmin, hsec, ?_⟩
  rw [hcstr]
  simpa only [List.cons_append, List.nil_append, go_cons_app, hpar, hp', b] using hgo

/-! ## `DateBuilder.build` value for the date-only form

With the `parseWithDate` sequence delivering a `DateBuilder` carrying the parsed `y`/`M`/`d`
fields, the remaining step is `build .any`: it discharges the `year.Valid month day` guard from the
grammar constraints, constructs a midnight-UTC `DateTime`, and its epoch-millisecond value is
`epochDays … × 86400000`. The helper lemmas below cover the integer `tdiv`/`tmod` recovery under the
`Duration` sign invariant, the `Std.Time` ↔ grammar validity bridges (`isLeap`/`days`), and the
midnight-timestamp arithmetic. -/

open Std.Time Std.Time.Internal in
/-- `(s·10⁹ + n).tdiv 10⁹ = s` when `s`, `n` are both nonnegative and `n < 10⁹`. -/
theorem tdiv_recover_nonneg (s n : Int) (h1 : 0 ≤ s) (h2 : 0 ≤ n) (h3 : n < 1000000000) :
    (s * 1000000000 + n).tdiv 1000000000 = s := by
  have hnonneg : 0 ≤ s * 1000000000 + n := by
    have : 0 ≤ s * 1000000000 := Int.mul_nonneg h1 (by decide); omega
  rw [Int.tdiv_eq_ediv_of_nonneg hnonneg, Int.mul_add_ediv_right _ _ (by decide),
    Int.ediv_eq_zero_of_lt h2 h3, Int.add_zero]

open Std.Time Std.Time.Internal in
/-- `(s·10⁹ + n).tmod 10⁹ = n` when `s`, `n` are both nonnegative and `n < 10⁹`. -/
theorem tmod_recover_nonneg (s n : Int) (h1 : 0 ≤ s) (h2 : 0 ≤ n) (h3 : n < 1000000000) :
    (s * 1000000000 + n).tmod 1000000000 = n := by
  have hnonneg : 0 ≤ s * 1000000000 + n := by
    have : 0 ≤ s * 1000000000 := Int.mul_nonneg h1 (by decide); omega
  rw [Int.tmod_eq_emod_of_nonneg hnonneg, Int.add_comm, Int.add_mul_emod_self_right,
    Int.emod_eq_of_lt h2 h3]

open Std.Time Std.Time.Internal in
/-- `(s·10⁹ + n).tdiv 10⁹ = s` when `|n| < 10⁹` and `s`, `n` share a sign (the `Duration`
    invariant). -/
theorem tdiv_recover (s n : Int) (hn2 : -1000000000 < n ∧ n < 1000000000)
    (hsign : (0 ≤ s ∧ 0 ≤ n) ∨ (s ≤ 0 ∧ n ≤ 0)) :
    (s * 1000000000 + n).tdiv 1000000000 = s := by
  rcases hsign with ⟨hs, hnn⟩ | ⟨hs, hnn⟩
  · exact tdiv_recover_nonneg s n hs hnn hn2.2
  · have hneg := tdiv_recover_nonneg (-s) (-n) (by omega) (by omega) (by omega)
    have he : ((-s) * 1000000000 + (-n)) = -(s * 1000000000 + n) := by
      rw [Int.neg_mul]; omega
    rw [he, Int.neg_tdiv] at hneg
    omega

open Std.Time Std.Time.Internal in
/-- `(s·10⁹ + n).tmod 10⁹ = n` when `|n| < 10⁹` and `s`, `n` share a sign. -/
theorem tmod_recover (s n : Int) (hn2 : -1000000000 < n ∧ n < 1000000000)
    (hsign : (0 ≤ s ∧ 0 ≤ n) ∨ (s ≤ 0 ∧ n ≤ 0)) :
    (s * 1000000000 + n).tmod 1000000000 = n := by
  rcases hsign with ⟨hs, hnn⟩ | ⟨hs, hnn⟩
  · exact tmod_recover_nonneg s n hs hnn hn2.2
  · have hneg := tmod_recover_nonneg (-s) (-n) (by omega) (by omega) (by omega)
    have he : ((-s) * 1000000000 + (-n)) = -(s * 1000000000 + n) := by
      rw [Int.neg_mul]; omega
    rw [he, Int.neg_tmod] at hneg
    omega

open Std.Time Std.Time.Internal in
/-- `Duration.ofNanoseconds` inverts `Duration.toNanoseconds`: the second/nanosecond split is
    recovered exactly, using the `Duration` sign invariant. -/
theorem dur_roundtrip (d : Std.Time.Duration) :
    Duration.ofNanoseconds (Duration.toNanoseconds d) = d := by
  have hnano := d.nano.property
  have hbound : -1000000000 < d.nano.val ∧ d.nano.val < 1000000000 := by omega
  have hsign : (0 ≤ d.second.val ∧ 0 ≤ d.nano.val) ∨ (d.second.val ≤ 0 ∧ d.nano.val ≤ 0) := by
    rcases d.proof with h|h
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ⟨h.1, h.2⟩
  have hval : (Duration.toNanoseconds d).val = d.second.val * 1000000000 + d.nano.val := by
    unfold Duration.toNanoseconds UnitVal.mul; rfl
  unfold Duration.ofNanoseconds
  apply Duration.ext
  · apply UnitVal.ext
    show ((Duration.toNanoseconds d).val).tdiv 1000000000 = d.second.val
    rw [hval, tdiv_recover d.second.val d.nano.val hbound hsign]
  · apply Subtype.ext
    show ((Duration.toNanoseconds d).val).tmod 1000000000 = d.nano.val
    rw [hval, tmod_recover d.second.val d.nano.val hbound hsign]

open Std.Time Std.Time.Internal in
/-- Subtracting a zero-valued `Second.Offset` from a `Timestamp` is the identity. -/
theorem subSeconds_zero (t : Timestamp) (s : Second.Offset) (hs : s.val = 0) :
    t.subSeconds s = t := by
  apply Timestamp.ext
  unfold Timestamp.subSeconds
  show t.val - Duration.ofSeconds s = t.val
  show Duration.subSeconds t.val s = t.val
  unfold Duration.subSeconds Duration.sub
  have hz : (Duration.ofSeconds s).neg = Duration.ofSeconds 0 := by
    apply Duration.ext
    · apply UnitVal.ext
      show -(Duration.ofSeconds s).second.val = (Duration.ofSeconds 0).second.val
      show -s.val = (0:Int)
      omega
    · rfl
  rw [hz]
  show Duration.ofNanoseconds (Duration.toNanoseconds t.val
      + Duration.toNanoseconds (Duration.ofSeconds 0)) = t.val
  have h0 : Duration.toNanoseconds (Duration.ofSeconds 0) = 0 := by rfl
  rw [h0]
  have hadd : t.val.toNanoseconds + (0 : Nanosecond.Offset) = t.val.toNanoseconds := by
    apply UnitVal.ext; show t.val.toNanoseconds.val + (0:Int) = t.val.toNanoseconds.val; omega
  rw [hadd, dur_roundtrip]

open Std.Time Std.Time.Internal in
/-- `Std.Time`'s leap-year test on a nonnegative year equals the grammar's `isLeapYear`. -/
theorem isLeap_ofNat (n : Nat) : Year.Offset.isLeap (Int.ofNat n) = isLeapYear n := by
  unfold Year.Offset.isLeap isLeapYear Year.Offset.toInt
  have h4 : (Int.ofNat n).tmod 4 = ((n % 4 : Nat) : Int) := by rw [Int.ofNat_tmod]; rfl
  have h100 : (Int.ofNat n).tmod 100 = ((n % 100 : Nat) : Int) := by rw [Int.ofNat_tmod]; rfl
  have h400 : (Int.ofNat n).tmod 400 = ((n % 400 : Nat) : Int) := by rw [Int.ofNat_tmod]; rfl
  rw [h4, h100, h400]
  simp only [Int.natCast_eq_zero, ne_eq]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]

open Std.Time Std.Time.Internal in
/-- `Std.Time`'s `Month.Ordinal.days` equals the grammar's `daysInMonth` for a coherent month
    ordinal and leap flag. -/
theorem days_eq_daysInMonth (yval mval : Nat) (Mo : Month.Ordinal) (leap : Bool)
    (hmv : Mo.val = (mval : Int)) (hleap : isLeapYear yval = leap)
    (hb : 1 ≤ mval ∧ mval ≤ 12) :
    daysInMonth yval mval = (Mo.days leap).val := by
  subst hleap
  obtain ⟨mv, hp⟩ := Mo
  simp only at hmv
  subst hmv
  have hmval : mval = 1 ∨ mval = 2 ∨ mval = 3 ∨ mval = 4 ∨ mval = 5 ∨ mval = 6 ∨ mval = 7 ∨
         mval = 8 ∨ mval = 9 ∨ mval = 10 ∨ mval = 11 ∨ mval = 12 := by omega
  rcases hmval with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
  case inr.inl =>
    cases hl : isLeapYear yval <;>
      · unfold daysInMonth Month.Ordinal.days
        simp only [hl]
        rfl
  all_goals rfl

open Std.Time Std.Time.Internal in
/-- Midnight `PlainTime` (all fields zero) has zero total seconds. -/
theorem midnight_toSeconds (hp : (0:Int) ≤ 0 ∧ (0:Int) ≤ 23) :
    (PlainTime.mk ⟨0, hp⟩ 0 0 0 : PlainTime).toSeconds.val = 0 := by
  show (Hour.Ordinal.toOffset ⟨0, hp⟩).toSeconds.val
      + (Minute.Ordinal.toOffset 0).toSeconds.val + (Second.Ordinal.toOffset 0).val = 0
  have e1 : (Hour.Ordinal.toOffset ⟨0, hp⟩).toSeconds.val = 0 := by
    unfold Hour.Ordinal.toOffset Hour.Offset.toSeconds UnitVal.cast UnitVal.mul; rfl
  have e2 : (Minute.Ordinal.toOffset 0).toSeconds.val = 0 := by decide
  have e3 : (Second.Ordinal.toOffset (0 : Second.Ordinal true)).val = 0 := by decide
  rw [e1, e2, e3]; rfl

/-- `Std.Time` compatibility: Std removed `PlainDateTime.toTimestampAssumingUTC` (the `DateTime`
    pipeline now routes through `PlainDateTime.toWallTime`, which wraps the SAME `Duration`).
    This replicates the v4.30 definition verbatim (`toDaysSinceUNIXEpoch` → `toEpochDay` is the
    same function renamed), so the timestamp-value lemmas below keep their original statements;
    definitionally `⟨dt.toWallTime.val⟩`. -/
private def _root_.Std.Time.PlainDateTime.toTimestampAssumingUTC (dt : Std.Time.PlainDateTime) :
    Std.Time.Timestamp :=
  let days := dt.date.toEpochDay
  let nanos := days.toSeconds + dt.time.toSeconds |>.mul 1000000000
  let nanos := nanos.val + dt.time.nanosecond.val
  Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch (Std.Time.Nanosecond.Offset.ofInt nanos)

open Std.Time Std.Time.Internal in
/-- The timestamp of a midnight `PlainDateTime` (assuming UTC) is `days-since-epoch × 86400 × 1e9`
    nanoseconds. -/
theorem midnight_toTimestampAssumingUTC (dt : PlainDate) (hp : (0:Int) ≤ 0 ∧ (0:Int) ≤ 23) :
    (PlainDateTime.toTimestampAssumingUTC { date := dt, time := PlainTime.mk ⟨0, hp⟩ 0 0 0 })
      = Timestamp.ofNanosecondsSinceUnixEpoch
          (Nanosecond.Offset.ofInt (dt.toEpochDay.val * 86400 * 1000000000)) := by
  unfold PlainDateTime.toTimestampAssumingUTC
  simp only []
  congr 1
  show Nanosecond.Offset.ofInt _ = Nanosecond.Offset.ofInt _
  congr 1
  have hts := midnight_toSeconds hp
  have hday : dt.toEpochDay.toSeconds.val = dt.toEpochDay.val * 86400 := by
    unfold Day.Offset.toSeconds UnitVal.cast UnitVal.mul; rfl
  show (UnitVal.mul (dt.toEpochDay.toSeconds
          + (PlainTime.mk ⟨0, hp⟩ 0 0 0 : PlainTime).toSeconds) 1000000000).val
        + (0 : Nanosecond.Ordinal).val = _
  unfold UnitVal.mul
  show (dt.toEpochDay.toSeconds.val
          + (PlainTime.mk ⟨0, hp⟩ 0 0 0 : PlainTime).toSeconds.val) * 1000000000
        + (0 : Nanosecond.Ordinal).val = _
  rw [hts, hday]
  show (dt.toEpochDay.val * 86400 + 0) * 1000000000 + (0:Int) = _
  omega

open Std.Time Std.Time.Internal in
/-- Milliseconds-since-epoch of a timestamp built from `secs × 10⁹` nanoseconds is `secs × 1000`. -/
theorem toMillis_ofSeconds (secs : Int) :
    UnitVal.toInt
      (Timestamp.toMillisecondsSinceUnixEpoch
        (Timestamp.ofNanosecondsSinceUnixEpoch (Nanosecond.Offset.ofInt (secs * 1000000000))))
      = secs * 1000 := by
  unfold Timestamp.toMillisecondsSinceUnixEpoch Timestamp.toNanosecondsSinceUnixEpoch
    Timestamp.ofNanosecondsSinceUnixEpoch Timestamp.toSecondsSinceUnixEpoch
    Nanosecond.Offset.toMilliseconds Duration.ofNanoseconds
  simp only [UnitVal.cast, UnitVal.tdiv, UnitVal.mul, UnitVal.div, UnitVal.toInt,
    Nanosecond.Offset.ofInt, Bounded.LE.byMod]
  show ((secs * 1000000000).tdiv 1000000000 * 1000000000
      + (secs * 1000000000).tmod 1000000000).tdiv 1000000 = secs * 1000
  rw [Int.mul_tdiv_cancel _ (by decide), Int.mul_tmod_left, Int.add_zero]
  rw [show (1000000000 : Int) = 1000 * 1000000 from by decide, ← Int.mul_assoc,
    Int.mul_tdiv_cancel _ (by decide)]

open Std.Time Std.Time.Internal in
/-- `DateTime.ofPlainDateTime` against the zone rules of a zero-offset timezone yields the
    plain UTC timestamp (empty transitions, zero offset ⇒ no adjustment). -/
theorem ofPlainDateTime_zero_timestamp (pdt : PlainDateTime) (tz0 : TimeZone)
    (hoff : tz0.offset = TimeZone.Offset.zero) :
    (ZonedDateTime.ofPlainDateTime pdt (TimeZone.ZoneRules.ofTimeZone tz0)).toTimestamp
      = pdt.toTimestampAssumingUTC := by
  -- `ofPlainDateTime` resolves through `toWallTime`/`findLocalTimeTypeForWallTime`; with
  -- `ofTimeZone`'s empty transition array the local-time type is the initial one, so the built
  -- timestamp is DEFINITIONALLY `toTimestampAssumingUTC.subSeconds tz0.offset.second`
  -- (`wall.val = toTimestampAssumingUTC.val`); the zero offset then cancels.
  show pdt.toTimestampAssumingUTC.subSeconds tz0.offset.second = pdt.toTimestampAssumingUTC
  apply subSeconds_zero
  rw [hoff]
  show TimeZone.Offset.zero.second.val = 0
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **`DateBuilder.build` value (date-only).** The empty `DateBuilder` with only `y`/`M`/`d` set
    from a well-formed date `build`s to `some zt`, and `zt`'s epoch-millisecond value is
    `epochDays … × 86400000` — the date-only form of `c.toMillis`. The `year.Valid month day` guard
    is discharged from the grammar constraints via `isLeap_ofNat`/`days_eq_daysInMonth`; the midnight
    timestamp collapses through the zero-offset zone. -/
theorem build_dateOnly_value {d : DateComponents}
    (_hsyn : d.syntaxWf) (hcon : d.constraintsWf)
    (hm : 1 ≤ fieldValue d.month ∧ fieldValue d.month ≤ 12)
    (hdd : 1 ≤ fieldValue d.day ∧ fieldValue d.day ≤ 31)
    (bld : Std.Time.GenericFormat.DateBuilder)
    (hbld : bld =
      { ({} : DateBuilder) with
        y := some (Int.ofNat (fieldValue d.year)),
        M := some (Bounded.LE.ofNat' (fieldValue d.month) hm),
        d := some (Bounded.LE.ofNat' (fieldValue d.day) hdd) }) :
    ∃ zt, bld.build .any = some zt ∧
      zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt =
        epochDays (fieldValue d.year) (fieldValue d.month) (fieldValue d.day) * 86400000 := by
  subst hbld
  -- Discharge the `year.Valid month day` guard from the grammar constraints.
  have hvalid : Year.Offset.Valid (Int.ofNat (fieldValue d.year))
      (Bounded.LE.ofNat' (fieldValue d.month) hm) (Bounded.LE.ofNat' (fieldValue d.day) hdd) := by
    show (Bounded.LE.ofNat' (fieldValue d.day) hdd : Day.Ordinal)
      ≤ Month.Ordinal.days (Year.Offset.isLeap (Int.ofNat (fieldValue d.year)))
          (Bounded.LE.ofNat' (fieldValue d.month) hm)
    show (Bounded.LE.ofNat' (fieldValue d.day) hdd : Day.Ordinal).val
      ≤ (Month.Ordinal.days (Year.Offset.isLeap (Int.ofNat (fieldValue d.year)))
          (Bounded.LE.ofNat' (fieldValue d.month) hm)).val
    obtain ⟨hm1, hm2, hd1, hd2⟩ := hcon
    have hbridge := days_eq_daysInMonth (fieldValue d.year) (fieldValue d.month)
      (Bounded.LE.ofNat' (fieldValue d.month) hm) (Year.Offset.isLeap (Int.ofNat (fieldValue d.year)))
      rfl (isLeap_ofNat (fieldValue d.year)).symm ⟨hm1, hm2⟩
    rw [← hbridge]
    show (fieldValue d.day : Int) ≤ (daysInMonth (fieldValue d.year) (fieldValue d.month) : Int)
    exact_mod_cast hd2
  letI : Decidable (Year.Offset.Valid (Int.ofNat (fieldValue d.year))
      (Bounded.LE.ofNat' (fieldValue d.month) hm)
      (Bounded.LE.ofNat' (fieldValue d.day) hdd)) := Day.instDecidableLeOrdinal
  -- Reduce `build .any` to the mapped `dite`, then take the `some` branch.
  have hbuild :
      ({ ({} : DateBuilder) with
          y := some (Int.ofNat (fieldValue d.year)),
          M := some (Bounded.LE.ofNat' (fieldValue d.month) hm),
          d := some (Bounded.LE.ofNat' (fieldValue d.day) hdd) }).build .any =
        (fun x => ZonedDateTime.ofPlainDateTime x
            (TimeZone.ZoneRules.ofTimeZone
              { offset := TimeZone.Offset.zero,
                name := (TimeZone.Offset.zero).toIsoString true,
                abbreviation := (TimeZone.Offset.zero).toIsoString true,
                isDST := false })) <$>
          (if h : Year.Offset.Valid (Int.ofNat (fieldValue d.year))
              (Bounded.LE.ofNat' (fieldValue d.month) hm)
              (Bounded.LE.ofNat' (fieldValue d.day) hdd) then
            some { date := { year := Int.ofNat (fieldValue d.year),
                             month := Bounded.LE.ofNat' (fieldValue d.month) hm,
                             day := Bounded.LE.ofNat' (fieldValue d.day) hdd, valid := h },
                   time := PlainTime.mk ⟨0, by decide⟩ 0 0 0 }
          else none) := by
    rfl
  rw [hbuild, dif_pos hvalid]
  refine ⟨_, rfl, ?_⟩
  -- Evaluate the timestamp of the resulting DateTime.
  rw [ofPlainDateTime_zero_timestamp _ _ rfl, midnight_toTimestampAssumingUTC, toMillis_ofSeconds]
  -- Bridge the day count to `epochDays`.
  have hday : (⟨Int.ofNat (fieldValue d.year), Bounded.LE.ofNat' (fieldValue d.month) hm,
        Bounded.LE.ofNat' (fieldValue d.day) hdd, hvalid⟩ : PlainDate).toEpochDay.val
      = epochDays (fieldValue d.year) (fieldValue d.month) (fieldValue d.day) :=
    (epochDays_eq (fieldValue d.year) (fieldValue d.month) (fieldValue d.day)
      ⟨Int.ofNat (fieldValue d.year), Bounded.LE.ofNat' (fieldValue d.month) hm,
        Bounded.LE.ofNat' (fieldValue d.day) hdd, hvalid⟩ rfl rfl rfl).symm
  rw [hday]
  omega

/-! ## General timestamp value: nonzero time and nonzero offset

The date-only build collapsed the timestamp through a zero-offset midnight zone. The time-bearing
forms need the general computation: a nonzero wall-clock time and an offset→UTC subtraction. These
lemmas generalize `midnight_toTimestampAssumingUTC`/`ofPlainDateTime_zero_timestamp`, culminating in
`zoned_value` — the epoch-millisecond value of a `DateTime` built from a plain date+time against
a fixed-offset zone. -/

open Std.Time Std.Time.Internal in
/-- `ofPlainDateTime` against the zone rules of a fixed-offset timezone yields the plain UTC
    timestamp minus the timezone's offset seconds. Generalizes `ofPlainDateTime_zero_timestamp`. -/
theorem ofPlainDateTime_timestamp (pdt : PlainDateTime) (tz : TimeZone) :
    (ZonedDateTime.ofPlainDateTime pdt (TimeZone.ZoneRules.ofTimeZone tz)).toTimestamp
      = pdt.toTimestampAssumingUTC.subSeconds tz.offset.second := by
  -- With `ofTimeZone`'s empty transition array, `findLocalTimeTypeForWallTime` returns
  -- the initial local-time type, whose timezone offset is `tz.offset`; the built timestamp is
  -- `wall − offset.second` with `wall.val = toTimestampAssumingUTC.val` definitionally.
  rfl

open Std.Time Std.Time.Internal in
/-- General `toTimestampAssumingUTC` for arbitrary time. Generalizes
    `midnight_toTimestampAssumingUTC` (nothing zeroes out). -/
theorem toTimestampAssumingUTC_value (dt : PlainDate) (t : PlainTime) :
    PlainDateTime.toTimestampAssumingUTC { date := dt, time := t }
      = Timestamp.ofNanosecondsSinceUnixEpoch
          (Nanosecond.Offset.ofInt
            ((dt.toEpochDay.val * 86400 + t.toSeconds.val) * 1000000000
              + t.nanosecond.val)) := by
  rfl

open Std.Time Std.Time.Internal in
/-- `Duration.ofNanoseconds` roundtrips its argument's `val` through `toNanoseconds` (the
    second/nanosecond split recombines exactly, for any value — no sign hypothesis, unlike
    `dur_roundtrip` which reconstructs the whole `Duration`). -/
theorem ofNanoseconds_toNanoseconds (ns : Nanosecond.Offset) :
    (Duration.ofNanoseconds ns).toNanoseconds.val = ns.val := by
  unfold Duration.ofNanoseconds Duration.toNanoseconds
  simp only [UnitVal.cast, UnitVal.mul, Bounded.LE.byMod]
  show (ns.val.tdiv 1000000000) * 1000000000 + ns.val.tmod 1000000000 = ns.val
  rw [Int.mul_comm, Int.mul_tdiv_add_tmod]

open Std.Time Std.Time.Internal in
/-- `toMillisecondsSinceUnixEpoch.toInt` of a timestamp is its total-nanosecond value truncated by
    `10⁶`. -/
theorem toMillis_eq (tm : Timestamp) :
    tm.toMillisecondsSinceUnixEpoch.toInt = tm.val.toNanoseconds.val.tdiv 1000000 := by
  unfold Timestamp.toMillisecondsSinceUnixEpoch Timestamp.toNanosecondsSinceUnixEpoch
    Timestamp.toSecondsSinceUnixEpoch Nanosecond.Offset.toMilliseconds Duration.toNanoseconds
  simp only [UnitVal.cast, UnitVal.div, UnitVal.mul, UnitVal.toInt]

open Std.Time Std.Time.Internal in
/-- `subSeconds s` subtracts `s·10⁹` from a timestamp's total-nanosecond value. -/
theorem subSeconds_toNanos (t : Timestamp) (s : Second.Offset) :
    (t.subSeconds s).val.toNanoseconds.val = t.val.toNanoseconds.val - s.val * 1000000000 := by
  show (Duration.subSeconds t.val s).toNanoseconds.val = _
  unfold Duration.subSeconds Duration.sub Duration.add
  rw [ofNanoseconds_toNanoseconds]
  have hneg : (Duration.ofSeconds s).neg.toNanoseconds.val = -(s.val * 1000000000) := by
    unfold Duration.ofSeconds Duration.neg Duration.toNanoseconds
    simp only [UnitVal.mul]
    show (-s.val) * 1000000000 + (0:Int) = -(s.val * 1000000000)
    omega
  show t.val.toNanoseconds.val + (Duration.ofSeconds s).neg.toNanoseconds.val = _
  rw [hneg]; omega

open Std.Time Std.Time.Internal in
/-- The total-nanosecond value of a timestamp built from `ofInt V` nanoseconds is `V`. -/
theorem ofNanos_ts_toNanos (V : Int) :
    (Timestamp.ofNanosecondsSinceUnixEpoch (Nanosecond.Offset.ofInt V)).val.toNanoseconds.val = V := by
  show (Duration.ofNanoseconds (Nanosecond.Offset.ofInt V)).toNanoseconds.val = V
  rw [ofNanoseconds_toNanoseconds]; rfl

open Std.Time Std.Time.Internal in
/-- **General zoned timestamp value.** The epoch-millisecond value of the `DateTime` built from
    a plain date + time against a fixed-offset timezone: `(days·86400 + wallSeconds − offsetSeconds)
    × 1000 + ms`. The subtracted offset and the sub-second `ms` both survive the single final
    truncation because, under `hnano : t.nanosecond.val = ms·10⁶`, the total nanoseconds are an exact
    multiple of `10⁶`, so `Int.mul_tdiv_cancel` applies without truncation loss. (The general
    `subSeconds`→millis identity is *false* for truncating division; the exact-multiple hypothesis is
    what makes this compose — the parsed `.SSS` millis field supplies it structurally.) -/
theorem zoned_value (dt : PlainDate) (t : PlainTime) (tz : TimeZone) (ms : Int)
    (hnano : t.nanosecond.val = ms * 1000000) :
    (ZonedDateTime.ofPlainDateTime { date := dt, time := t }
        (TimeZone.ZoneRules.ofTimeZone tz)).toTimestamp.toMillisecondsSinceUnixEpoch.toInt
      = (dt.toEpochDay.val * 86400 + t.toSeconds.val - tz.offset.second.val) * 1000
          + ms := by
  rw [ofPlainDateTime_timestamp, toMillis_eq, subSeconds_toNanos, toTimestampAssumingUTC_value,
    ofNanos_ts_toNanos, hnano]
  have hrw : (dt.toEpochDay.val * 86400 + t.toSeconds.val) * 1000000000 + ms * 1000000
        - tz.offset.second.val * 1000000000
      = ((dt.toEpochDay.val * 86400 + t.toSeconds.val - tz.offset.second.val) * 1000 + ms)
          * 1000000 := by omega
  rw [hrw, Int.mul_tdiv_cancel _ (by decide)]

/-! ## Date-only slice: `DateOnly.parse` value

Composing `parseWithDate_dateOnly` (the format-part sequence into a filled `DateBuilder`) and
`build_dateOnly_value` (the builder's epoch-ms value) through the `GenericFormat.parse` wrapper —
`parser.go`, the trailing `<* eof`, and `.run`/`.toOption` — gives the value of `DateOnly.parse` on
a well-formed date string. This closes the `c.time = none` case of `stdTime_alternation_value`. -/

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- Reduction of `<*` (`seqLeft`) on the string iterator: run `p`, then `q`, keeping `p`'s value.
    Analogous to `parsec_bind_app`/`parsec_map_app`. -/
theorem seqLeft_app {α β : Type} (p : Std.Internal.Parsec ParseIt α)
    (q : Std.Internal.Parsec ParseIt β) (it : ParseIt) :
    (p <* q) it = (match p it with
      | .success rem a => (match q rem with
          | .success rem' _ => .success rem' a
          | .error pos msg => .error pos msg)
      | .error pos msg => .error pos msg) := by
  show Std.Internal.Parsec.bind p
    (fun a => Std.Internal.Parsec.bind q (fun _ => Std.Internal.Parsec.pure a)) it = _
  rw [parsec_bind_app]
  cases p it with
  | success rem a =>
    simp only
    rw [parsec_bind_app]
    cases q rem <;> rfl
  | error pos msg => rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- `parser.go` on the empty format list with a builder that `build`s successfully: returns the
    built value at the unchanged position. -/
theorem go_nil_some (config : FormatConfig) (bld : DateBuilder) (it : ParseIt)
    (res : Std.Time.ZonedDateTime) (hb : bld.build .any = some res) :
    parser.go config .any bld [] it = ParseResult.success it res := by
  unfold parser.go; rw [hb]; rfl

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `eof` succeeds at the end position. -/
theorem eof_endPos (s : String) :
    eof (⟨s, s.endPos⟩ : ParseIt) = .success ⟨s, s.endPos⟩ () := by
  show (if Input.hasNext (⟨s, s.endPos⟩ : ParseIt) then _ else _) = _
  have hend : Input.hasNext (⟨s, s.endPos⟩ : ParseIt) = false := by
    show decide (¬ s.endPos.IsAtEnd) = false
    have hae : s.endPos.IsAtEnd := by rfl
    rw [hae]; simp only [not_true, decide_false]
  rw [hend]; rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
theorem parse_eq_ok_of_go (F : GenericFormat .any) (s : String) (fs : FormatString)
    (b : DateBuilder) (zt : ZonedDateTime)
    (hp : parser F.string F.config .any = parser.go F.config .any {} fs)
    (hgo : parser.go F.config .any {} fs ⟨s, s.startPos⟩ =
      parser.go F.config .any b [] ⟨s, s.endPos⟩)
    (hbuild : b.build .any = some zt) :
    F.parse s = .ok zt := by
  have happ : (parser F.string F.config .any <* eof) ⟨s, s.startPos⟩ =
      ParseResult.success ⟨s, s.endPos⟩ zt := by
    rw [seqLeft_app, hp, hgo, go_nil_some F.config _ _ zt hbuild]
    simp only []
    rw [eof_endPos]
  unfold GenericFormat.parse Parser.run
  rw [happ]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat
  Cedar.Spec.Ext.Datetime in
/-- `DateOnly.parse` succeeds on a well-formed date string, returning a `DateTime` whose
    epoch-ms value is `epochDays … × 86400000`. -/
theorem dateOnly_parse_eq_ok {d : DateComponents} (hsyn : d.syntaxWf) (hcon : d.constraintsWf) :
    ∃ zt, DateOnly.parse d.asString = .ok zt ∧
      zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt
        = epochDays (fieldValue d.year) (fieldValue d.month) (fieldValue d.day) * 86400000 := by
  obtain ⟨hm, hd, hgo⟩ := parseWithDate_dateOnly DateOnly.config hsyn hcon
  obtain ⟨zt, hbuild, hval⟩ := build_dateOnly_value hsyn hcon hm hd _ rfl
  refine ⟨zt, ?_, hval⟩
  exact parse_eq_ok_of_go DateOnly d.asString _ _ zt rfl hgo hbuild

open Cedar.Spec.Ext.Datetime in
/-- **Date-only slice of the alternation value.** `DateOnly.parse d.asString`, mapped to its
    epoch-ms value, is `epochDays … × 86400000` — the `c.time = none` case of the value bridge. -/
theorem dateOnly_parse_value {d : DateComponents} (hsyn : d.syntaxWf) (hcon : d.constraintsWf) :
    (DateOnly.parse d.asString).toOption.map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some (epochDays (fieldValue d.year) (fieldValue d.month) (fieldValue d.day) * 86400000) := by
  obtain ⟨zt, hparse, hval⟩ := dateOnly_parse_eq_ok hsyn hcon
  rw [hparse]
  show (some zt).map _ = _
  rw [Option.map_some, hval]

/-! ## DateUTC slice: `DateUTC.parse` value

The time-bearing analogue of the date-only slice, for the `yyyy-MM-dd'T'HH:mm:ss'Z'` form: the
filled builder (`y`/`M`/`d`/`H`/`m`/`s`) builds through the general `zoned_value` at a
zero-offset UTC zone, and `DateUTC.parse` yields `c.toMillis`. -/

open Std.Time Std.Time.Internal in
/-- Total seconds of a `PlainTime` built from explicit ordinals. -/
theorem toSeconds_mk (H : Hour.Ordinal) (M : Minute.Ordinal) (S : Second.Ordinal true)
    (n : Nanosecond.Ordinal) :
    (PlainTime.mk H M S n).toSeconds.val = H.val * 3600 + M.val * 60 + S.val := by
  show (Hour.Ordinal.toOffset H).toSeconds.val + (Minute.Ordinal.toOffset M).toSeconds.val
      + (Second.Ordinal.toOffset S).val = _
  unfold Hour.Ordinal.toOffset Hour.Offset.toSeconds Minute.Ordinal.toOffset Minute.Offset.toSeconds
    Second.Ordinal.toOffset UnitVal.cast UnitVal.mul
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **`DateBuilder.build` value (DateUTC).** The builder with `y`/`M`/`d`/`H`/`m`/`s` set from a
    well-formed UTC datetime builds to `some zt`, and `zt`'s epoch-millisecond value is `c.toMillis`.
    Uses the general `zoned_value` at a zero-offset zone with `ms = 0`. -/
theorem build_dateUTC_value {c : DatetimeComponents} (tp : TimePart)
    (_hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = none)
    (hm : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12)
    (hd : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31)
    (hh : 0 ≤ fieldValue tp.time.hours ∧ fieldValue tp.time.hours ≤ 23)
    (hmin : 0 ≤ fieldValue tp.time.minutes ∧ fieldValue tp.time.minutes ≤ 59)
    (hsec : 0 ≤ fieldValue tp.time.seconds ∧ fieldValue tp.time.seconds ≤ 59)
    (bld : DateBuilder)
    (hbld : bld =
      { ({} : DateBuilder) with
        y := some (Int.ofNat (fieldValue c.date.year)),
        M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
        d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
        H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
        m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
        s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                    : Bounded.LE 0 60) }) :
    ∃ zt, bld.build .any = some zt ∧
      zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = c.toMillis := by
  subst hbld
  obtain ⟨hdatecon, _⟩ := hcon
  have hvalid : Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Bounded.LE.ofNat' (fieldValue c.date.day) hd) := by
    show (Bounded.LE.ofNat' (fieldValue c.date.day) hd : Day.Ordinal).val
      ≤ (Month.Ordinal.days (Year.Offset.isLeap (Int.ofNat (fieldValue c.date.year)))
          (Bounded.LE.ofNat' (fieldValue c.date.month) hm)).val
    obtain ⟨hm1, hm2, hd1, hd2⟩ := hdatecon
    have hbridge := days_eq_daysInMonth (fieldValue c.date.year) (fieldValue c.date.month)
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Year.Offset.isLeap (Int.ofNat (fieldValue c.date.year)))
      rfl (isLeap_ofNat (fieldValue c.date.year)).symm ⟨hm1, hm2⟩
    rw [← hbridge]
    show (fieldValue c.date.day : Int) ≤ (daysInMonth (fieldValue c.date.year) (fieldValue c.date.month) : Int)
    exact_mod_cast hd2
  letI : Decidable (Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Bounded.LE.ofNat' (fieldValue c.date.day) hd)) := Day.instDecidableLeOrdinal
  have hbuild :
      ({ ({} : DateBuilder) with
          y := some (Int.ofNat (fieldValue c.date.year)),
          M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
          d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
          H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
          m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
          s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                      : Bounded.LE 0 60) }).build .any =
        (fun x => ZonedDateTime.ofPlainDateTime x
            (TimeZone.ZoneRules.ofTimeZone
              { offset := TimeZone.Offset.zero,
                name := (TimeZone.Offset.zero).toIsoString true,
                abbreviation := (TimeZone.Offset.zero).toIsoString true,
                isDST := false })) <$>
          (if h : Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
              (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
              (Bounded.LE.ofNat' (fieldValue c.date.day) hd) then
            some { date := { year := Int.ofNat (fieldValue c.date.year),
                             month := Bounded.LE.ofNat' (fieldValue c.date.month) hm,
                             day := Bounded.LE.ofNat' (fieldValue c.date.day) hd, valid := h },
                   time := PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
                             (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
                             ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop
                               (by decide))
                             0 }
          else none) := by
    rfl
  rw [hbuild, dif_pos hvalid]
  refine ⟨_, rfl, ?_⟩
  have hzv := zoned_value
    (⟨Int.ofNat (fieldValue c.date.year),
      Bounded.LE.ofNat' (fieldValue c.date.month) hm,
      Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ : PlainDate)
    (PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
       (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
       ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)) 0)
    { offset := TimeZone.Offset.zero,
      name := (TimeZone.Offset.zero).toIsoString true,
      abbreviation := (TimeZone.Offset.zero).toIsoString true,
      isDST := false }
    0 (by rfl)
  rw [hzv]
  have htsec : (PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
      (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
      ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)) 0
      : PlainTime).toSeconds.val
      = (fieldValue tp.time.hours : Int) * 3600 + (fieldValue tp.time.minutes : Int) * 60
          + (fieldValue tp.time.seconds : Int) :=
    toSeconds_mk _ _ _ _
  rw [htsec]
  have htz : ({ offset := TimeZone.Offset.zero,
                name := (TimeZone.Offset.zero).toIsoString true,
                abbreviation := (TimeZone.Offset.zero).toIsoString true,
                isDST := false } : TimeZone).offset.second.val = 0 := rfl
  rw [htz]
  have hday : (⟨Int.ofNat (fieldValue c.date.year),
        Bounded.LE.ofNat' (fieldValue c.date.month) hm,
        Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ : PlainDate).toEpochDay.val
      = epochDays (fieldValue c.date.year) (fieldValue c.date.month) (fieldValue c.date.day) :=
    (epochDays_eq (fieldValue c.date.year) (fieldValue c.date.month) (fieldValue c.date.day)
      ⟨Int.ofNat (fieldValue c.date.year),
        Bounded.LE.ofNat' (fieldValue c.date.month) hm,
        Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ rfl rfl rfl).symm
  rw [hday]
  simp only [DatetimeComponents.toMillis, DateComponents.toMillis, TimePart.toMillis,
    htime, hutc, hmillis, Zone.offsetSeconds]
  omega

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- `DateUTC.parse` succeeds on a well-formed UTC datetime string, returning a `DateTime`
    whose epoch-ms value is `c.toMillis`. -/
theorem dateUTC_parse_eq_ok {c : DatetimeComponents} (tp : TimePart)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = none) :
    ∃ zt, DateUTC.parse c.asString = .ok zt ∧
      zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = c.toMillis := by
  obtain ⟨hm, hd, hh, hmin, hsec, hgo⟩ :=
    parseWithDate_dateUTC tp DateUTC.config rfl hsyn hcon htime hutc hmillis
  obtain ⟨zt, hbuild, hval⟩ :=
    build_dateUTC_value tp hsyn hcon htime hutc hmillis hm hd hh hmin hsec _ rfl
  refine ⟨zt, ?_, hval⟩
  exact parse_eq_ok_of_go DateUTC c.asString _ _ zt rfl hgo hbuild

/-- **DateUTC slice of the alternation value.** `DateUTC.parse c.asString`, mapped to its epoch-ms
    value, is `c.toMillis` — the `c.time = some tp`, `tp.zone = utc`, `tp.millis = none` case. -/
theorem dateUTC_parse_value {c : DatetimeComponents} (tp : TimePart)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = none) :
    (DateUTC.parse c.asString).toOption.map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some c.toMillis := by
  obtain ⟨zt, hparse, hval⟩ := dateUTC_parse_eq_ok tp hsyn hcon htime hutc hmillis
  rw [hparse]
  show (some zt).map _ = _
  rw [Option.map_some, hval]

/-! ## DateUTCWithMillis slice: `DateUTCWithMillis.parse` value

The `.SSS` millisecond analogue of the DateUTC slice (`yyyy-MM-dd'T'HH:mm:ss.SSS'Z'`): adds the
fraction field before `Z`, with a nonzero `nano = fieldValue sss * 10⁶` fed to `zoned_value` as
`ms = fieldValue sss`. The `digit_le`/`fieldValue_le_999` helpers bound a 3-digit `SSS` field. -/

theorem digit_le (c : Char) (h : c.isDigit = true) : c.toNat - 48 ≤ 9 := by
  unfold Char.isDigit at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  obtain ⟨_, h2⟩ := h
  rw [UInt32.le_iff_toNat_le] at h2
  show c.val.toNat - 48 ≤ 9
  have h9 : ('9'.val.toNat) = 57 := by decide
  omega

theorem fieldValue_le_999 {sss : String} (h : IsFixedDigits 3 sss) : fieldValue sss ≤ 999 := by
  obtain ⟨hdig, hlen⟩ := h
  rw [fieldValue_isDigits sss hdig]
  have hl3 : sss.toList.length = 3 := by rw [String.length_toList]; exact hlen
  match hm : sss.toList, hl3 with
  | [a, b, c], _ =>
    have hab := digit_le a (hdig.2 a (by rw [hm]; simp))
    have hbb := digit_le b (hdig.2 b (by rw [hm]; simp))
    have hcb := digit_le c (hdig.2 c (by rw [hm]; simp))
    simp only [List.foldl]
    omega

/-- A two-digit field's value is at most `99`. -/
theorem fieldValue_le_99 {ss : String} (h : IsFixedDigits 2 ss) : fieldValue ss ≤ 99 := by
  obtain ⟨hdig, hlen⟩ := h
  rw [fieldValue_isDigits ss hdig]
  have hl2 : ss.toList.length = 2 := by rw [String.length_toList]; exact hlen
  match hm : ss.toList, hl2 with
  | [a, b], _ =>
    have hab := digit_le a (hdig.2 a (by rw [hm]; simp))
    have hbb := digit_le b (hdig.2 b (by rw [hm]; simp))
    simp only [List.foldl]
    omega

/-- A four-digit field's value is at most `9999`. -/
theorem fieldValue_le_9999 {yyyy : String} (h : IsFixedDigits 4 yyyy) : fieldValue yyyy ≤ 9999 := by
  obtain ⟨hdig, hlen⟩ := h
  rw [fieldValue_isDigits yyyy hdig]
  have hl4 : yyyy.toList.length = 4 := by rw [String.length_toList]; exact hlen
  match hm : yyyy.toList, hl4 with
  | [a, b, c, d], _ =>
    have hab := digit_le a (hdig.2 a (by rw [hm]; simp))
    have hbb := digit_le b (hdig.2 b (by rw [hm]; simp))
    have hcb := digit_le c (hdig.2 c (by rw [hm]; simp))
    have hdb := digit_le d (hdig.2 d (by rw [hm]; simp))
    simp only [List.foldl]
    omega

/-! ## STEP A: step_fraction -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
theorem step_fraction {s : String} (p : s.Pos) (pre rest sss : String) (b : DateBuilder)
    (config : FormatConfig) (hsss : IsFixedDigits 3 sss) (hb : fieldValue sss ≤ 999)
    (hsplit : p.Splits pre (sss ++ rest)) :
    ∃ (p' : s.Pos) (h : 0 ≤ fieldValue sss * 1000000 ∧ fieldValue sss * 1000000 ≤ 999999999),
      parseWithDate b config (.modifier (.S (.truncated 3))) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ { b with S := some (Bounded.LE.ofNat' (fieldValue sss * 1000000) h) } ∧
      p'.Splits (pre ++ sss) rest := by
  obtain ⟨p', h, hpar, hsp⟩ := parseWith_fraction_at p pre rest sss config hsss hb hsplit
  refine ⟨p', h, ?_, hsp⟩
  unfold parseWithDate
  simp only [bind, Bind.bind, pure]
  rw [parsec_bind_app, hpar]
  rfl

/-! ## STEP B: parseWithDate_dateUTCWithMillis (14-step sequence) -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
theorem parseWithDate_dateUTCWithMillis {c : DatetimeComponents} (tp : TimePart) (sss : String)
    (config : FormatConfig) (hcfg : config.allowLeapSeconds = false)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = some sss) :
    ∃ (hm : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12)
      (hd : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31)
      (hh : 0 ≤ fieldValue tp.time.hours ∧ fieldValue tp.time.hours ≤ 23)
      (hmin : 0 ≤ fieldValue tp.time.minutes ∧ fieldValue tp.time.minutes ≤ 59)
      (hsec : 0 ≤ fieldValue tp.time.seconds ∧ fieldValue tp.time.seconds ≤ 59)
      (hms : 0 ≤ fieldValue sss * 1000000 ∧ fieldValue sss * 1000000 ≤ 999999999),
      parser.go config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2}), .string "T",
           .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
           .string ":", .modifier (.s {padding := 2}), .string ".",
           .modifier (.S (.truncated 3)), .string "Z"]
          ⟨c.asString, c.asString.startPos⟩
        = parser.go config .any
            { ({} : DateBuilder) with
              y := some (Int.ofNat (fieldValue c.date.year)),
              M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
              d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
              H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
              m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
              s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                          : Bounded.LE 0 60),
              S := some (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms) }
            [] ⟨c.asString, c.asString.endPos⟩ := by
  have ⟨_, htimesyn⟩ := hsyn
  simp only [htime] at htimesyn
  obtain ⟨_, htmillis, _⟩ := htimesyn
  rw [hmillis] at htmillis
  let tail := "." ++ (sss ++ "Z")
  have hcstr : c.asString = c.date.asString ++ "T" ++ tp.time.asString ++ tail := by
    simp only [tail, DatetimeComponents.asString, TimePart.asString, htime, hmillis, hutc,
      Zone.asString, String.append_assoc]
  obtain ⟨hm, hd, hh, hmin, hsec, p, hgo, hsp⟩ :=
    parseWithDate_datetimePrefix tp tail config hcfg hsyn hcon htime
      [.string ".", .modifier (.S (.truncated 3)), .string "Z"]
  let b : DateBuilder :=
    { ({} : DateBuilder) with
      y := some (Int.ofNat (fieldValue c.date.year)),
      M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
      d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
      H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
      m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
      s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop
        (by decide) : Bounded.LE 0 60) }
  obtain ⟨p', hdot, hsp'⟩ := step_sep p
    (c.date.asString ++ "T" ++ tp.time.asString) (sss ++ "Z") "." b config hsp
  obtain ⟨p'', hms, hfrac, hsp''⟩ := step_fraction p'
    (c.date.asString ++ "T" ++ tp.time.asString ++ ".") "Z" sss b config htmillis
    (fieldValue_le_999 htmillis) hsp'
  let bS : DateBuilder :=
    { b with S := some (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms) }
  obtain ⟨p''', hz, hsp'''⟩ := step_sep p''
    (c.date.asString ++ "T" ++ tp.time.asString ++ "." ++ sss) "" "Z" bS config
    (by rw [String.append_empty]; exact hsp'')
  have hp : p''' = (c.date.asString ++ "T" ++ tp.time.asString ++ tail).endPos :=
    hsp'''.eq_endPos_iff.mpr rfl
  refine ⟨hm, hd, hh, hmin, hsec, hms, ?_⟩
  rw [hcstr]
  simpa only [List.cons_append, List.nil_append, go_cons_app, hdot, hfrac, hz, hp, b, bS,
    tail] using hgo

/-! ## STEP C: build_dateUTCWithMillis_value -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
theorem build_dateUTCWithMillis_value {c : DatetimeComponents} (tp : TimePart) (sss : String)
    (_hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = some sss)
    (hm : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12)
    (hd : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31)
    (hh : 0 ≤ fieldValue tp.time.hours ∧ fieldValue tp.time.hours ≤ 23)
    (hmin : 0 ≤ fieldValue tp.time.minutes ∧ fieldValue tp.time.minutes ≤ 59)
    (hsec : 0 ≤ fieldValue tp.time.seconds ∧ fieldValue tp.time.seconds ≤ 59)
    (hms : 0 ≤ fieldValue sss * 1000000 ∧ fieldValue sss * 1000000 ≤ 999999999)
    (bld : DateBuilder)
    (hbld : bld =
      { ({} : DateBuilder) with
        y := some (Int.ofNat (fieldValue c.date.year)),
        M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
        d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
        H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
        m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
        s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                    : Bounded.LE 0 60),
        S := some (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms) }) :
    ∃ zt, bld.build .any = some zt ∧
      zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = c.toMillis := by
  subst hbld
  obtain ⟨hdatecon, _⟩ := hcon
  have hvalid : Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Bounded.LE.ofNat' (fieldValue c.date.day) hd) := by
    show (Bounded.LE.ofNat' (fieldValue c.date.day) hd : Day.Ordinal).val
      ≤ (Month.Ordinal.days (Year.Offset.isLeap (Int.ofNat (fieldValue c.date.year)))
          (Bounded.LE.ofNat' (fieldValue c.date.month) hm)).val
    obtain ⟨hm1, hm2, hd1, hd2⟩ := hdatecon
    have hbridge := days_eq_daysInMonth (fieldValue c.date.year) (fieldValue c.date.month)
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Year.Offset.isLeap (Int.ofNat (fieldValue c.date.year)))
      rfl (isLeap_ofNat (fieldValue c.date.year)).symm ⟨hm1, hm2⟩
    rw [← hbridge]
    show (fieldValue c.date.day : Int) ≤ (daysInMonth (fieldValue c.date.year) (fieldValue c.date.month) : Int)
    exact_mod_cast hd2
  letI : Decidable (Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Bounded.LE.ofNat' (fieldValue c.date.day) hd)) := Day.instDecidableLeOrdinal
  have hbuild :
      ({ ({} : DateBuilder) with
          y := some (Int.ofNat (fieldValue c.date.year)),
          M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
          d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
          H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
          m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
          s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                      : Bounded.LE 0 60),
          S := some (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms) }).build .any =
        (fun x => ZonedDateTime.ofPlainDateTime x
            (TimeZone.ZoneRules.ofTimeZone
              { offset := TimeZone.Offset.zero,
                name := (TimeZone.Offset.zero).toIsoString true,
                abbreviation := (TimeZone.Offset.zero).toIsoString true,
                isDST := false })) <$>
          (if h : Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
              (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
              (Bounded.LE.ofNat' (fieldValue c.date.day) hd) then
            some { date := { year := Int.ofNat (fieldValue c.date.year),
                             month := Bounded.LE.ofNat' (fieldValue c.date.month) hm,
                             day := Bounded.LE.ofNat' (fieldValue c.date.day) hd, valid := h },
                   time := PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
                             (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
                             ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop
                               (by decide))
                             (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms) }
          else none) := by
    rfl
  rw [hbuild, dif_pos hvalid]
  refine ⟨_, rfl, ?_⟩
  have hzv := zoned_value
    (⟨Int.ofNat (fieldValue c.date.year),
      Bounded.LE.ofNat' (fieldValue c.date.month) hm,
      Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ : PlainDate)
    (PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
       (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
       ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide))
       (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms))
    { offset := TimeZone.Offset.zero,
      name := (TimeZone.Offset.zero).toIsoString true,
      abbreviation := (TimeZone.Offset.zero).toIsoString true,
      isDST := false }
    (fieldValue sss) (by rfl)
  rw [hzv]
  have htsec : (PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
      (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
      ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide))
      (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms)
      : PlainTime).toSeconds.val
      = (fieldValue tp.time.hours : Int) * 3600 + (fieldValue tp.time.minutes : Int) * 60
          + (fieldValue tp.time.seconds : Int) :=
    toSeconds_mk _ _ _ _
  rw [htsec]
  have htz : ({ offset := TimeZone.Offset.zero,
                name := (TimeZone.Offset.zero).toIsoString true,
                abbreviation := (TimeZone.Offset.zero).toIsoString true,
                isDST := false } : TimeZone).offset.second.val = 0 := rfl
  rw [htz]
  have hday : (⟨Int.ofNat (fieldValue c.date.year),
        Bounded.LE.ofNat' (fieldValue c.date.month) hm,
        Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ : PlainDate).toEpochDay.val
      = epochDays (fieldValue c.date.year) (fieldValue c.date.month) (fieldValue c.date.day) :=
    (epochDays_eq (fieldValue c.date.year) (fieldValue c.date.month) (fieldValue c.date.day)
      ⟨Int.ofNat (fieldValue c.date.year),
        Bounded.LE.ofNat' (fieldValue c.date.month) hm,
        Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ rfl rfl rfl).symm
  rw [hday]
  simp only [DatetimeComponents.toMillis, DateComponents.toMillis, TimePart.toMillis,
    htime, hutc, hmillis, Zone.offsetSeconds]
  omega

/-! ## STEP D: dateUTCWithMillis_parse value -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
theorem dateUTCWithMillis_parse_eq_ok {c : DatetimeComponents} (tp : TimePart) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = some sss) :
    ∃ zt, DateUTCWithMillis.parse c.asString = .ok zt ∧
      zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = c.toMillis := by
  obtain ⟨hm, hd, hh, hmin, hsec, hms, hgo⟩ :=
    parseWithDate_dateUTCWithMillis tp sss DateUTCWithMillis.config rfl hsyn hcon htime hutc hmillis
  obtain ⟨zt, hbuild, hval⟩ :=
    build_dateUTCWithMillis_value tp sss hsyn hcon htime hutc hmillis hm hd hh hmin hsec hms _ rfl
  refine ⟨zt, ?_, hval⟩
  exact parse_eq_ok_of_go DateUTCWithMillis c.asString _ _ zt rfl hgo hbuild

/-- **DateUTCWithMillis slice of the alternation value.** -/
theorem dateUTCWithMillis_parse_value {c : DatetimeComponents} (tp : TimePart) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = some sss) :
    (DateUTCWithMillis.parse c.asString).toOption.map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some c.toMillis := by
  obtain ⟨zt, hparse, hval⟩ := dateUTCWithMillis_parse_eq_ok tp sss hsyn hcon htime hutc hmillis
  rw [hparse]
  show (some zt).map _ = _
  rw [Option.map_some, hval]


/-! ## DateWithOffset slice: `DateWithOffset.parse` value

The offset-bearing analogue of the DateUTC slice, for the `yyyy-MM-dd'T'HH:mm:ssxx` form: the final
format part is the `±hhmm` offset (via `step_offset`) instead of the `Z` literal, and the built
zone has a *nonzero* offset, exercising `zoned_value`'s offset→UTC subtraction. -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- One `parseWithDate` step on the offset modifier `.x .hourMinute` (`±hhmm`). -/
theorem step_offset {s} (p : s.Pos) (pre rest hh mm : String) (neg : Bool) (b : DateBuilder)
    (config : FormatConfig) (hhh : IsFixedDigits 2 hh) (hmm : IsFixedDigits 2 mm)
    (hhb : fieldValue hh ≤ 23) (hmb : fieldValue mm ≤ 59)
    (hsplit : p.Splits pre (String.singleton (if neg then '-' else '+') ++ (hh ++ (mm ++ rest)))) :
    ∃ p' : s.Pos,
      parseWithDate b config (.modifier (.x .hourMinute)) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩
            { b with x := some (TimeZone.Offset.ofSeconds
              ⟨((fieldValue hh : Int) * 3600 + (fieldValue mm : Int) * 60)
                * (if neg then -1 else 1)⟩) } ∧
      p'.Splits (pre ++ String.singleton (if neg then '-' else '+') ++ hh ++ mm) rest := by
  obtain ⟨p', hpar, hsp⟩ :=
    parseWith_hourMinute_at p pre rest hh mm neg config hhh hmm hhb hmb hsplit
  refine ⟨p', ?_, hsp⟩
  unfold parseWithDate
  simp only [bind, Bind.bind, pure]
  rw [parsec_bind_app, hpar]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **`DateBuilder.build` value (DateWithOffset).** The builder with `y`/`M`/`d`/`H`/`m`/`s`/`x`
    set from a well-formed offset datetime builds to `some zt`, and `zt`'s epoch-ms value is
    `c.toMillis`. Uses the general `zoned_value` at the *nonzero* offset zone (`ms = 0`). -/
theorem build_dateWithOffset_value {c : DatetimeComponents} (tp : TimePart) (o : OffsetComponents)
    (_hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = none)
    (hm : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12)
    (hd : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31)
    (hh : 0 ≤ fieldValue tp.time.hours ∧ fieldValue tp.time.hours ≤ 23)
    (hmin : 0 ≤ fieldValue tp.time.minutes ∧ fieldValue tp.time.minutes ≤ 59)
    (hsec : 0 ≤ fieldValue tp.time.seconds ∧ fieldValue tp.time.seconds ≤ 59)
    (bld : DateBuilder)
    (hbld : bld =
      { ({} : DateBuilder) with
        y := some (Int.ofNat (fieldValue c.date.year)),
        M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
        d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
        H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
        m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
        s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                    : Bounded.LE 0 60),
        x := some (TimeZone.Offset.ofSeconds
              ⟨((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
                * (if o.negative then -1 else 1)⟩) }) :
    ∃ zt, bld.build .any = some zt ∧
      zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = c.toMillis := by
  subst hbld
  obtain ⟨hdatecon, _⟩ := hcon
  let off : TimeZone.Offset := TimeZone.Offset.ofSeconds
    ⟨((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
      * (if o.negative then -1 else 1)⟩
  have hvalid : Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Bounded.LE.ofNat' (fieldValue c.date.day) hd) := by
    show (Bounded.LE.ofNat' (fieldValue c.date.day) hd : Day.Ordinal).val
      ≤ (Month.Ordinal.days (Year.Offset.isLeap (Int.ofNat (fieldValue c.date.year)))
          (Bounded.LE.ofNat' (fieldValue c.date.month) hm)).val
    obtain ⟨hm1, hm2, hd1, hd2⟩ := hdatecon
    have hbridge := days_eq_daysInMonth (fieldValue c.date.year) (fieldValue c.date.month)
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Year.Offset.isLeap (Int.ofNat (fieldValue c.date.year)))
      rfl (isLeap_ofNat (fieldValue c.date.year)).symm ⟨hm1, hm2⟩
    rw [← hbridge]
    show (fieldValue c.date.day : Int) ≤ (daysInMonth (fieldValue c.date.year) (fieldValue c.date.month) : Int)
    exact_mod_cast hd2
  letI : Decidable (Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Bounded.LE.ofNat' (fieldValue c.date.day) hd)) := Day.instDecidableLeOrdinal
  have hbuild :
      ({ ({} : DateBuilder) with
          y := some (Int.ofNat (fieldValue c.date.year)),
          M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
          d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
          H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
          m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
          s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                      : Bounded.LE 0 60),
          x := some off }).build .any =
        (fun x => ZonedDateTime.ofPlainDateTime x
            (TimeZone.ZoneRules.ofTimeZone
              { offset := off,
                name := off.toIsoString true,
                abbreviation := off.toIsoString true,
                isDST := false })) <$>
          (if h : Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
              (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
              (Bounded.LE.ofNat' (fieldValue c.date.day) hd) then
            some { date := { year := Int.ofNat (fieldValue c.date.year),
                             month := Bounded.LE.ofNat' (fieldValue c.date.month) hm,
                             day := Bounded.LE.ofNat' (fieldValue c.date.day) hd, valid := h },
                   time := PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
                             (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
                             ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop
                               (by decide))
                             0 }
          else none) := by
    rfl
  rw [hbuild, dif_pos hvalid]
  refine ⟨_, rfl, ?_⟩
  have hzv := zoned_value
    (⟨Int.ofNat (fieldValue c.date.year),
      Bounded.LE.ofNat' (fieldValue c.date.month) hm,
      Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ : PlainDate)
    (PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
       (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
       ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)) 0)
    { offset := off,
      name := off.toIsoString true,
      abbreviation := off.toIsoString true,
      isDST := false }
    0 (by rfl)
  rw [hzv]
  have htsec : (PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
      (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
      ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)) 0
      : PlainTime).toSeconds.val
      = (fieldValue tp.time.hours : Int) * 3600 + (fieldValue tp.time.minutes : Int) * 60
          + (fieldValue tp.time.seconds : Int) :=
    toSeconds_mk _ _ _ _
  rw [htsec]
  have htz : ({ offset := off,
                name := off.toIsoString true,
                abbreviation := off.toIsoString true,
                isDST := false } : TimeZone).offset.second.val
      = ((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
          * (if o.negative then -1 else 1) := rfl
  rw [htz]
  have hday : (⟨Int.ofNat (fieldValue c.date.year),
        Bounded.LE.ofNat' (fieldValue c.date.month) hm,
        Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ : PlainDate).toEpochDay.val
      = epochDays (fieldValue c.date.year) (fieldValue c.date.month) (fieldValue c.date.day) :=
    (epochDays_eq (fieldValue c.date.year) (fieldValue c.date.month) (fieldValue c.date.day)
      ⟨Int.ofNat (fieldValue c.date.year),
        Bounded.LE.ofNat' (fieldValue c.date.month) hm,
        Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ rfl rfl rfl).symm
  rw [hday]
  simp only [DatetimeComponents.toMillis, DateComponents.toMillis, TimePart.toMillis,
    htime, hzone, hmillis, Zone.offsetSeconds, OffsetComponents.seconds]
  cases o.negative <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

open Cedar.Spec.Ext in
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **DateWithOffset sequence.** Running the DateWithOffset format's `parser.go`
    (`yyyy-MM-dd'T'HH:mm:ssxx`) from the empty builder on the rendering of a well-formed
    offset-form datetime threads through all twelve `parseWithDate` steps to the terminal `[]` at end
    of string, with a builder whose `y`/`M`/`d`/`H`/`m`/`s`/`x` fields are set. -/
theorem parseWithDate_dateWithOffset {c : DatetimeComponents} (tp : TimePart) (o : OffsetComponents)
    (config : FormatConfig) (hcfg : config.allowLeapSeconds = false)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = none) :
    ∃ (hm : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12)
      (hd : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31)
      (hh : 0 ≤ fieldValue tp.time.hours ∧ fieldValue tp.time.hours ≤ 23)
      (hmin : 0 ≤ fieldValue tp.time.minutes ∧ fieldValue tp.time.minutes ≤ 59)
      (hsec : 0 ≤ fieldValue tp.time.seconds ∧ fieldValue tp.time.seconds ≤ 59),
      parser.go config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2}), .string "T",
           .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
           .string ":", .modifier (.s {padding := 2}), .modifier (.x .hourMinute)]
          ⟨c.asString, c.asString.startPos⟩
        = parser.go config .any
            { ({} : DateBuilder) with
              y := some (Int.ofNat (fieldValue c.date.year)),
              M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
              d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
              H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
              m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
              s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                          : Bounded.LE 0 60),
              x := some (TimeZone.Offset.ofSeconds
                    ⟨((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
                      * (if o.negative then -1 else 1)⟩) }
            [] ⟨c.asString, c.asString.endPos⟩ := by
  have ⟨_, htimesyn⟩ := hsyn
  simp only [htime] at htimesyn
  obtain ⟨_, _, htzone⟩ := htimesyn
  have ⟨_, htimecon⟩ := hcon
  simp only [htime] at htimecon
  obtain ⟨_, htzonecon⟩ := htimecon
  rw [hzone] at htzone htzonecon
  obtain ⟨hoh, hom⟩ := htzone
  obtain ⟨hohb, homb⟩ := htzonecon
  have hsign : (if o.negative then "-" else "+")
      = String.singleton (if o.negative then '-' else '+') := by
    cases o.negative <;> rfl
  let osfx :=
    String.singleton (if o.negative then '-' else '+') ++ (o.hours ++ (o.minutes ++ ""))
  have hcstr : c.asString = c.date.asString ++ "T" ++ tp.time.asString ++ osfx := by
    simp only [osfx, DatetimeComponents.asString, TimePart.asString, htime, hmillis, hzone,
      Zone.asString, OffsetComponents.asString, hsign, String.append_empty, String.append_assoc]
  obtain ⟨hm, hd, hh, hmin, hsec, p, hgo, hsp⟩ :=
    parseWithDate_datetimePrefix tp osfx config hcfg hsyn hcon htime
      [.modifier (.x .hourMinute)]
  let b : DateBuilder :=
    { ({} : DateBuilder) with
      y := some (Int.ofNat (fieldValue c.date.year)),
      M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
      d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
      H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
      m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
      s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop
        (by decide) : Bounded.LE 0 60) }
  obtain ⟨p', hoff, hsp'⟩ := step_offset p
    (c.date.asString ++ "T" ++ tp.time.asString) "" o.hours o.minutes o.negative b config
    hoh hom hohb homb hsp
  have hp : p' = (c.date.asString ++ "T" ++ tp.time.asString ++ osfx).endPos :=
    hsp'.eq_endPos_iff.mpr rfl
  refine ⟨hm, hd, hh, hmin, hsec, ?_⟩
  rw [hcstr]
  simpa only [List.cons_append, List.nil_append, go_cons_app, hoff, hp, b] using hgo

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- `DateWithOffset.parse` succeeds on a well-formed offset datetime string, returning a
    `DateTime` whose epoch-ms value is `c.toMillis`. -/
theorem dateWithOffset_parse_eq_ok {c : DatetimeComponents} (tp : TimePart) (o : OffsetComponents)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = none) :
    ∃ zt, DateWithOffset.parse c.asString = .ok zt ∧
      zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = c.toMillis := by
  obtain ⟨hm, hd, hh, hmin, hsec, hgo⟩ :=
    parseWithDate_dateWithOffset tp o DateWithOffset.config rfl hsyn hcon htime hzone hmillis
  obtain ⟨zt, hbuild, hval⟩ :=
    build_dateWithOffset_value tp o hsyn hcon htime hzone hmillis hm hd hh hmin hsec _ rfl
  refine ⟨zt, ?_, hval⟩
  exact parse_eq_ok_of_go DateWithOffset c.asString _ _ zt rfl hgo hbuild

/-- **DateWithOffset slice of the alternation value.** `DateWithOffset.parse c.asString`, mapped to
    its epoch-ms value, is `c.toMillis` — the `c.time = some tp`, `tp.zone = offset o`,
    `tp.millis = none` case. -/
theorem dateWithOffset_parse_value {c : DatetimeComponents} (tp : TimePart) (o : OffsetComponents)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = none) :
    (DateWithOffset.parse c.asString).toOption.map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some c.toMillis := by
  obtain ⟨zt, hparse, hval⟩ := dateWithOffset_parse_eq_ok tp o hsyn hcon htime hzone hmillis
  rw [hparse]
  show (some zt).map _ = _
  rw [Option.map_some, hval]

/-! ## DateWithOffsetAndMillis slice: `DateWithOffsetAndMillis.parse` value

The last form (`yyyy-MM-dd'T'HH:mm:ss.SSSxx`) — the union of the `.SSS` and offset wrinkles: it
merges the DateUTCWithMillis and DateWithOffset slices (fraction field + nonzero-offset zone). -/

/-! ## DateWithOffsetAndMillis: parseWithDate sequence (14 steps, ending in step_offset) -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
theorem parseWithDate_dateWithOffsetAndMillis {c : DatetimeComponents} (tp : TimePart)
    (o : OffsetComponents) (sss : String)
    (config : FormatConfig) (hcfg : config.allowLeapSeconds = false)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = some sss) :
    ∃ (hm : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12)
      (hd : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31)
      (hh : 0 ≤ fieldValue tp.time.hours ∧ fieldValue tp.time.hours ≤ 23)
      (hmin : 0 ≤ fieldValue tp.time.minutes ∧ fieldValue tp.time.minutes ≤ 59)
      (hsec : 0 ≤ fieldValue tp.time.seconds ∧ fieldValue tp.time.seconds ≤ 59)
      (hms : 0 ≤ fieldValue sss * 1000000 ∧ fieldValue sss * 1000000 ≤ 999999999),
      parser.go config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2}), .string "T",
           .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
           .string ":", .modifier (.s {padding := 2}), .string ".",
           .modifier (.S (.truncated 3)), .modifier (.x .hourMinute)]
          ⟨c.asString, c.asString.startPos⟩
        = parser.go config .any
            { ({} : DateBuilder) with
              y := some (Int.ofNat (fieldValue c.date.year)),
              M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
              d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
              H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
              m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
              s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                          : Bounded.LE 0 60),
              S := some (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms),
              x := some (TimeZone.Offset.ofSeconds
                    ⟨((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
                      * (if o.negative then -1 else 1)⟩) }
            [] ⟨c.asString, c.asString.endPos⟩ := by
  have ⟨_, htimesyn⟩ := hsyn
  simp only [htime] at htimesyn
  obtain ⟨_, htmillis, htzone⟩ := htimesyn
  rw [hmillis] at htmillis
  rw [hzone] at htzone
  have ⟨_, htimecon⟩ := hcon
  simp only [htime] at htimecon
  obtain ⟨_, htzonecon⟩ := htimecon
  rw [hzone] at htzonecon
  obtain ⟨hoh, hom⟩ := htzone
  obtain ⟨hohb, homb⟩ := htzonecon
  have hsign : (if o.negative then "-" else "+")
      = String.singleton (if o.negative then '-' else '+') := by
    cases o.negative <;> rfl
  let osfx :=
    String.singleton (if o.negative then '-' else '+') ++ (o.hours ++ (o.minutes ++ ""))
  let tail := "." ++ (sss ++ osfx)
  have hcstr : c.asString = c.date.asString ++ "T" ++ tp.time.asString ++ tail := by
    simp only [tail, osfx, DatetimeComponents.asString, TimePart.asString, htime, hmillis,
      hzone, Zone.asString, OffsetComponents.asString, hsign, String.append_empty,
      String.append_assoc]
  obtain ⟨hm, hd, hh, hmin, hsec, p, hgo, hsp⟩ :=
    parseWithDate_datetimePrefix tp tail config hcfg hsyn hcon htime
      [.string ".", .modifier (.S (.truncated 3)), .modifier (.x .hourMinute)]
  let b : DateBuilder :=
    { ({} : DateBuilder) with
      y := some (Int.ofNat (fieldValue c.date.year)),
      M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
      d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
      H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
      m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
      s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop
        (by decide) : Bounded.LE 0 60) }
  obtain ⟨p', hdot, hsp'⟩ := step_sep p
    (c.date.asString ++ "T" ++ tp.time.asString) (sss ++ osfx) "." b config hsp
  obtain ⟨p'', hms, hfrac, hsp''⟩ := step_fraction p'
    (c.date.asString ++ "T" ++ tp.time.asString ++ ".") osfx sss b config htmillis
    (fieldValue_le_999 htmillis) hsp'
  let bS : DateBuilder :=
    { b with S := some (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms) }
  obtain ⟨p''', hoff, hsp'''⟩ := step_offset p''
    (c.date.asString ++ "T" ++ tp.time.asString ++ "." ++ sss) ""
    o.hours o.minutes o.negative bS config hoh hom hohb homb hsp''
  have hp : p''' = (c.date.asString ++ "T" ++ tp.time.asString ++ tail).endPos :=
    hsp'''.eq_endPos_iff.mpr rfl
  refine ⟨hm, hd, hh, hmin, hsec, hms, ?_⟩
  rw [hcstr]
  simpa only [List.cons_append, List.nil_append, go_cons_app, hdot, hfrac, hoff, hp, b, bS,
    tail] using hgo

/-! ## DateWithOffsetAndMillis: build value (nonzero millis AND nonzero offset) -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
theorem build_dateWithOffsetAndMillis_value {c : DatetimeComponents} (tp : TimePart)
    (o : OffsetComponents) (sss : String)
    (_hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = some sss)
    (hm : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12)
    (hd : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31)
    (hh : 0 ≤ fieldValue tp.time.hours ∧ fieldValue tp.time.hours ≤ 23)
    (hmin : 0 ≤ fieldValue tp.time.minutes ∧ fieldValue tp.time.minutes ≤ 59)
    (hsec : 0 ≤ fieldValue tp.time.seconds ∧ fieldValue tp.time.seconds ≤ 59)
    (hms : 0 ≤ fieldValue sss * 1000000 ∧ fieldValue sss * 1000000 ≤ 999999999)
    (bld : DateBuilder)
    (hbld : bld =
      { ({} : DateBuilder) with
        y := some (Int.ofNat (fieldValue c.date.year)),
        M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
        d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
        H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
        m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
        s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                    : Bounded.LE 0 60),
        S := some (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms),
        x := some (TimeZone.Offset.ofSeconds
              ⟨((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
                * (if o.negative then -1 else 1)⟩) }) :
    ∃ zt, bld.build .any = some zt ∧
      zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = c.toMillis := by
  subst hbld
  obtain ⟨hdatecon, _⟩ := hcon
  let off : TimeZone.Offset := TimeZone.Offset.ofSeconds
    ⟨((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
      * (if o.negative then -1 else 1)⟩
  have hvalid : Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Bounded.LE.ofNat' (fieldValue c.date.day) hd) := by
    show (Bounded.LE.ofNat' (fieldValue c.date.day) hd : Day.Ordinal).val
      ≤ (Month.Ordinal.days (Year.Offset.isLeap (Int.ofNat (fieldValue c.date.year)))
          (Bounded.LE.ofNat' (fieldValue c.date.month) hm)).val
    obtain ⟨hm1, hm2, hd1, hd2⟩ := hdatecon
    have hbridge := days_eq_daysInMonth (fieldValue c.date.year) (fieldValue c.date.month)
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Year.Offset.isLeap (Int.ofNat (fieldValue c.date.year)))
      rfl (isLeap_ofNat (fieldValue c.date.year)).symm ⟨hm1, hm2⟩
    rw [← hbridge]
    show (fieldValue c.date.day : Int) ≤ (daysInMonth (fieldValue c.date.year) (fieldValue c.date.month) : Int)
    exact_mod_cast hd2
  letI : Decidable (Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
      (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
      (Bounded.LE.ofNat' (fieldValue c.date.day) hd)) := Day.instDecidableLeOrdinal
  have hbuild :
      ({ ({} : DateBuilder) with
          y := some (Int.ofNat (fieldValue c.date.year)),
          M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
          d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
          H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
          m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
          s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                      : Bounded.LE 0 60),
          S := some (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms),
          x := some off }).build .any =
        (fun x => ZonedDateTime.ofPlainDateTime x
            (TimeZone.ZoneRules.ofTimeZone
              { offset := off,
                name := off.toIsoString true,
                abbreviation := off.toIsoString true,
                isDST := false })) <$>
          (if h : Year.Offset.Valid (Int.ofNat (fieldValue c.date.year))
              (Bounded.LE.ofNat' (fieldValue c.date.month) hm)
              (Bounded.LE.ofNat' (fieldValue c.date.day) hd) then
            some { date := { year := Int.ofNat (fieldValue c.date.year),
                             month := Bounded.LE.ofNat' (fieldValue c.date.month) hm,
                             day := Bounded.LE.ofNat' (fieldValue c.date.day) hd, valid := h },
                   time := PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
                             (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
                             ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop
                               (by decide))
                             (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms) }
          else none) := by
    rfl
  rw [hbuild, dif_pos hvalid]
  refine ⟨_, rfl, ?_⟩
  have hzv := zoned_value
    (⟨Int.ofNat (fieldValue c.date.year),
      Bounded.LE.ofNat' (fieldValue c.date.month) hm,
      Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ : PlainDate)
    (PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
       (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
       ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide))
       (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms))
    { offset := off,
      name := off.toIsoString true,
      abbreviation := off.toIsoString true,
      isDST := false }
    (fieldValue sss) (by rfl)
  rw [hzv]
  have htsec : (PlainTime.mk (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh)
      (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin)
      ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide))
      (Bounded.LE.ofNat' (fieldValue sss * 1000000) hms)
      : PlainTime).toSeconds.val
      = (fieldValue tp.time.hours : Int) * 3600 + (fieldValue tp.time.minutes : Int) * 60
          + (fieldValue tp.time.seconds : Int) :=
    toSeconds_mk _ _ _ _
  rw [htsec]
  have htz : ({ offset := off,
                name := off.toIsoString true,
                abbreviation := off.toIsoString true,
                isDST := false } : TimeZone).offset.second.val
      = ((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
          * (if o.negative then -1 else 1) := rfl
  rw [htz]
  have hday : (⟨Int.ofNat (fieldValue c.date.year),
        Bounded.LE.ofNat' (fieldValue c.date.month) hm,
        Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ : PlainDate).toEpochDay.val
      = epochDays (fieldValue c.date.year) (fieldValue c.date.month) (fieldValue c.date.day) :=
    (epochDays_eq (fieldValue c.date.year) (fieldValue c.date.month) (fieldValue c.date.day)
      ⟨Int.ofNat (fieldValue c.date.year),
        Bounded.LE.ofNat' (fieldValue c.date.month) hm,
        Bounded.LE.ofNat' (fieldValue c.date.day) hd, hvalid⟩ rfl rfl rfl).symm
  rw [hday]
  simp only [DatetimeComponents.toMillis, DateComponents.toMillis, TimePart.toMillis,
    htime, hzone, hmillis, Zone.offsetSeconds, OffsetComponents.seconds]
  cases o.negative <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-! ## DateWithOffsetAndMillis: parse value -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
theorem dateWithOffsetAndMillis_parse_eq_ok {c : DatetimeComponents} (tp : TimePart)
    (o : OffsetComponents) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = some sss) :
    ∃ zt, DateWithOffsetAndMillis.parse c.asString = .ok zt ∧
      zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = c.toMillis := by
  obtain ⟨hm, hd, hh, hmin, hsec, hms, hgo⟩ :=
    parseWithDate_dateWithOffsetAndMillis tp o sss DateWithOffsetAndMillis.config rfl hsyn hcon
      htime hzone hmillis
  obtain ⟨zt, hbuild, hval⟩ :=
    build_dateWithOffsetAndMillis_value tp o sss hsyn hcon htime hzone hmillis hm hd hh hmin hsec
      hms _ rfl
  refine ⟨zt, ?_, hval⟩
  exact parse_eq_ok_of_go DateWithOffsetAndMillis c.asString _ _ zt rfl hgo hbuild

/-- **DateWithOffsetAndMillis slice of the alternation value.** -/
theorem dateWithOffsetAndMillis_parse_value {c : DatetimeComponents} (tp : TimePart)
    (o : OffsetComponents) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = some sss) :
    (DateWithOffsetAndMillis.parse c.asString).toOption.map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some c.toMillis := by
  obtain ⟨zt, hparse, hval⟩ :=
    dateWithOffsetAndMillis_parse_eq_ok tp o sss hsyn hcon htime hzone hmillis
  rw [hparse]
  show (some zt).map _ = _
  rw [Option.map_some, hval]


/-! ## Bridge to `Std.Time`: `Datetime.parse` ↔ `computeValue`

The lemmas above (roundtrip + `Parsec` foundations) are the parser-independent half — they relate
`IsWfDatetime`, `computeValue`, the structural `parseComponents`, and the primitive `Parsec`
combinators, all of which we control. The lemmas below are the missing half: they relate the
*actual* `Datetime.parse` (which delegates to `Std.Time.GenericFormat.parse`) to those definitions.
Each is a self-contained obligation about `Std.Time`'s behavior on the five fixed datetime formats;
discharging them requires symbolically evaluating `Std.Time`'s well-founded-recursion parsers — the
`Parsec` foundations above are the first rung of that ladder (see the note in the aggregator).

The decomposition mirrors the structure of `Datetime.parse`:
1. three Boolean guards (`dateContainsLeapSeconds`, `checkOffsetLen`, `tzOffsetMinsLt60`);
2. the five-way format alternation `DateOnly.parse <|> … <|> DateWithOffsetAndMillis.parse`;
3. the offset-range check `< MAX_OFFSET_SECONDS` and the final `datetime?` (i.e. `Int64.ofInt?`). -/

/-- If `datetime? v = some d` then `d.val.toInt = v` (the `Int64.ofInt?` roundtrip on the datetime
    encoding). Mirror of `Cedar.Thm.Duration.duration?_some_toInt`. -/
theorem datetime?_some_toInt (v : Int) (d : Datetime) (h : datetime? v = some d) :
    d.val.toInt = v := by
  unfold datetime? at h
  cases hv : Int64.ofInt? v with
  | none => simp [hv] at h
  | some i =>
    simp only [hv, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    exact Int64.ofInt?_some_toInt hv

/-- **Structural decomposition of a successful parse.** Reading `Datetime.parse str = some d`
    backwards through its `do`-block: the three Boolean guards must have passed, the `Std.Time`
    format alternation must have produced some `zt`, its offset must have satisfied the
    `< MAX_OFFSET_SECONDS` range check, and the final `datetime?` (`Int64.ofInt?`) of `zt`'s
    epoch-millisecond value must have returned `d`. This is pure `Option`-monad reasoning about the
    shape of `Datetime.parse` — no `Std.Time` internals — so it is fully proven, and it is what lets
    `parse_sound` reduce to the genuine `Std.Time` obligations. -/
theorem parse_some_decompose {str : String} {d : Datetime} (h : Datetime.parse str = some d) :
    dateContainsLeapSeconds str = false ∧ checkOffsetLen str = true ∧
    tzOffsetMinsLt60 str = true ∧
    ∃ zt, (DateOnly.parse str <|> DateUTC.parse str <|> DateUTCWithMillis.parse str <|>
             DateWithOffset.parse str <|> DateWithOffsetAndMillis.parse str).toOption = some zt ∧
          zt.timezone.offset.second.val.natAbs < MAX_OFFSET_SECONDS ∧
          datetime? zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt = some d := by
  unfold Datetime.parse at h
  cases hleap : dateContainsLeapSeconds str <;> rw [hleap] at h <;> simp only [reduceIte] at h
  case true => simp [bind, Option.bind] at h
  case false =>
  cases hlen : checkOffsetLen str <;> rw [hlen] at h <;>
    simp only [Bool.not_false, Bool.not_true, reduceIte] at h
  case false => simp [bind, Option.bind] at h
  case true =>
  cases htz : tzOffsetMinsLt60 str <;> rw [htz] at h <;>
    simp only [Bool.not_false, Bool.not_true, reduceIte] at h
  case false => simp [bind, Option.bind] at h
  case true =>
  refine ⟨rfl, rfl, rfl, ?_⟩
  cases halt : (DateOnly.parse str <|> DateUTC.parse str <|> DateUTCWithMillis.parse str <|>
             DateWithOffset.parse str <|> DateWithOffsetAndMillis.parse str).toOption with
  | none => rw [halt] at h; simp [bind, Option.bind] at h
  | some zt =>
    rw [halt] at h; simp only [bind, Option.bind] at h
    refine ⟨zt, rfl, ?_, ?_⟩
    · by_contra hrange
      simp only [hrange, reduceIte] at h
      exact absurd h (by simp)
    · by_cases hrange : zt.timezone.offset.second.val.natAbs < MAX_OFFSET_SECONDS
      · simp only [hrange, reduceIte] at h; exact h
      · simp only [hrange, reduceIte] at h; exact absurd h (by simp)

section WfOfParse
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat Cedar.Spec.Ext.Datetime


/-- **`exactlyChars.go` success-inversion.** If the digit-consuming loop succeeds from position `p`
    (splitting the string as `pre ++ suf`) advancing to `p'` returning `result`, then `result` is
    `acc` followed by an `out` segment of exactly `size - count` digit characters, `suf` begins with
    `out`, and `p'` sits just past `out`. This is the converse of `exactlyChars_go_digits`. -/
theorem exactlyChars_go_inv {s : String} :
    ∀ (k size count : Nat) (acc pre suf : String) (p p' : s.Pos) (result : String),
      size - count = k →
      p.Splits pre suf →
      exactlyChars.go (satisfy Char.isDigit) size acc count ⟨s, p⟩
          = ParseResult.success ⟨s, p'⟩ result →
      ∃ out rest : String,
        result = acc ++ out ∧
        suf = out ++ rest ∧
        out.length = size - count ∧
        (∀ c ∈ out.toList, c.isDigit = true) ∧
        p'.Splits (pre ++ out) rest := by
  intro k
  induction k with
  | zero =>
    intro size count acc pre suf p p' result hk hsplit hgo
    have hge : count ≥ size := by omega
    rw [exactlyChars_go_eq, if_pos hge] at hgo
    -- go returns `pure acc`
    simp only [Std.Internal.Parsec.pure, ParseResult.success.injEq, Sigma.mk.injEq,
      heq_eq_eq, true_and] at hgo
    obtain ⟨hp, hres⟩ := hgo
    subst hres
    refine ⟨"", suf, by simp, by simp, by simp [hk], by simp, ?_⟩
    rw [String.append_empty, ← hp]
    exact hsplit
  | succ k ih =>
    intro size count acc pre suf p p' result hk hsplit hgo
    have hlt : ¬ count ≥ size := by omega
    rw [exactlyChars_go_eq, if_neg hlt, parsec_bind_app] at hgo
    -- satisfy must succeed: hasNext and current char is a digit
    by_cases hn : Input.hasNext (⟨s, p⟩ : ParseIt) = true
    · rw [satisfy_eq] at hgo
      simp only [hn, dif_pos] at hgo
      by_cases hd : Char.isDigit (Input.curr' (⟨s, p⟩ : ParseIt) hn) = true
      · simp only [hd, if_pos] at hgo
        have hp : p ≠ s.endPos := (hasNext_iff s p).mp hn
        rw [next'_eq, curr'_eq] at hgo
        -- Abbreviate the consumed character.
        have hcdig : (p.get ((hasNext_iff s p).mp hn)).isDigit = true := by
          rw [← curr'_eq]; exact hd
        -- input split: suf = singleton c ++ suf'
        obtain ⟨suf', hsuf'⟩ := hsplit.exists_eq_singleton_append hp
        -- `p.get hp` and `p.get ((hasNext_iff ..).mp hn)` are equal by proof irrelevance.
        have hsplit_next : (p.next ((hasNext_iff s p).mp hn)).Splits
            (pre ++ String.singleton (p.get hp)) suf' := by
          have : p.Splits pre (String.singleton (p.get hp) ++ suf') := by
            rw [← hsuf']; exact hsplit
          exact this.next
        obtain ⟨out', rest, hres', hsuf'', hlen', hdig', hsp'⟩ :=
          ih size count.succ (acc.push (p.get ((hasNext_iff s p).mp hn)))
            (pre ++ String.singleton (p.get hp)) suf'
            (p.next ((hasNext_iff s p).mp hn)) p' result (by omega) hsplit_next hgo
        refine ⟨String.singleton (p.get hp) ++ out', rest, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hres', String.push_eq_append, String.append_assoc]
        · rw [hsuf', hsuf'', String.append_assoc]
        · rw [String.length_append, String.length_singleton, hlen']; omega
        · intro ch hch
          rw [String.toList_append] at hch
          simp only [List.mem_append] at hch
          rcases hch with hch | hch
          · have : ch = p.get hp := by
              rw [String.toList_singleton] at hch; simpa using hch
            rw [this]
            -- proof irrelevance: `p.get hp = p.get ((hasNext_iff ..).mp hn)`
            exact hcdig
          · exact hdig' ch hch
        · rw [String.append_assoc] at hsp'; exact hsp'
      · exfalso
        simp only [Bool.not_eq_true] at hd
        rw [hd, if_neg (by simp)] at hgo
        simp at hgo
    · exfalso
      rw [satisfy_eq] at hgo
      simp only [hn, dif_neg, Bool.not_eq_true] at hgo
      simp at hgo



/-- **`exactlyChars` success-inversion (position-general).** If `exactlyChars (satisfy isDigit) n`
    succeeds at position `p` (splitting `s` as `pre ++ suf`) advancing to `p'` returning `out`, then
    `out` is exactly `n` digit characters, `suf` begins with `out`, and `p'` splits `s` as
    `pre ++ out | rest`. Converse of `exactlyChars_digits_at`. -/
theorem exactlyChars_inv_at {s : String} (p p' : s.Pos) (pre suf out : String) (n : Nat)
    (hn : 0 < n) (hsplit : p.Splits pre suf)
    (hpar : exactlyChars (satisfy Char.isDigit) n ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ out) :
    ∃ rest : String,
      IsFixedDigits n out ∧ suf = out ++ rest ∧ p'.Splits (pre ++ out) rest := by
  have hgo0 : exactlyChars (satisfy Char.isDigit) n
      = exactlyChars.go (satisfy Char.isDigit) n "" 0 := rfl
  rw [hgo0] at hpar
  obtain ⟨o, rest, hres, hsuf, hlen, hdig, hsp⟩ :=
    exactlyChars_go_inv n n 0 "" pre suf p p' out (by omega) hsplit hpar
  rw [String.empty_append] at hres
  subst hres
  have hlen' : out.length = n := by omega
  refine ⟨rest, ⟨⟨?_, hdig⟩, hlen'⟩, hsuf, hsp⟩
  omega



/-- **`parseNum` success-inversion.** If `parseNum n` succeeds at `p` returning value `v`, then the
    consumed segment is a fixed `n`-digit string `out` with `v = fieldValue out`. -/
theorem parseNum_inv_at {s : String} (p p' : s.Pos) (pre suf : String) (n : Nat) (hn : 0 < n)
    (v : Nat) (hsplit : p.Splits pre suf)
    (hpar : parseNum n ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ v) :
    ∃ out rest : String,
      IsFixedDigits n out ∧ v = fieldValue out ∧ suf = out ++ rest ∧
      p'.Splits (pre ++ out) rest := by
  unfold parseNum at hpar
  rw [parsec_map_app] at hpar
  -- The inner exactlyChars must have succeeded.
  cases hec : exactlyChars (satisfy Char.isDigit) n ⟨s, p⟩ with
  | error pos msg => rw [hec] at hpar; simp at hpar
  | success rem out =>
    rw [hec] at hpar
    -- rem must be ⟨s, p'⟩ and v = toNat! out
    obtain ⟨sr, pr⟩ := rem
    simp only [ParseResult.success.injEq, Sigma.mk.injEq] at hpar
    obtain ⟨⟨hsr, hpr⟩, hv⟩ := hpar
    subst hsr
    -- hpr : pr ≍ p'   (HEq since types match after subst)
    simp only [heq_eq_eq] at hpr
    subst hpr
    obtain ⟨rest, hfd, hsuf, hsp⟩ := exactlyChars_inv_at p pr pre suf out n hn hsplit hec
    refine ⟨out, rest, hfd, ?_, hsuf, hsp⟩
    rw [← hv, toNat!_eq_fieldValue out hfd.1]



/-- **`pstring` success-inversion.** If `pstring sep` succeeds at `p` (splitting `s` as `pre ++ suf`)
    advancing to `p'`, then `sep` is a prefix of `suf` (`suf = sep ++ rest`) and `p'` splits `s` as
    `pre ++ sep | rest`. -/
theorem pstring_inv_at {s : String} (p p' : s.Pos) (pre suf sep : String) (out : String)
    (hsplit : p.Splits pre suf)
    (hpar : pstring sep ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ out) :
    ∃ rest : String, out = sep ∧ suf = sep ++ rest ∧ p'.Splits (pre ++ sep) rest := by
  -- The guard must have held, so `sep` is a prefix of `suf`.
  have hg : (s.sliceFrom p).startsWith sep = true := by
    by_contra hg
    simp only [Bool.not_eq_true] at hg
    unfold pstring at hpar
    rw [hg] at hpar; simp at hpar
  rw [String.Slice.startsWith_string_iff, hsplit.copy_sliceFrom_eq] at hg
  obtain ⟨restL, hrest⟩ := hg
  -- `suf = sep ++ ofList restL`.
  have hsuf : suf = sep ++ String.ofList restL := by
    rw [← String.ofList_toList (s := suf), ← hrest, String.ofList_append, String.ofList_toList]
  -- Reuse the forward lemma at the same position; `pstring` is a function, so results coincide.
  rw [hsuf] at hsplit
  obtain ⟨p'', hpar'', hsp''⟩ := pstring_at p pre (String.ofList restL) sep hsplit
  rw [hpar] at hpar''
  simp only [ParseResult.success.injEq, Sigma.mk.injEq, heq_eq_eq] at hpar''
  obtain ⟨⟨_, hpp⟩, hout⟩ := hpar''
  subst hpp
  exact ⟨String.ofList restL, hout, hsuf, hsp''⟩



/-- **`parseNatToBounded (parseFlexibleNum 2)` success-inversion.** Success at `p` forces a fixed
    2-digit segment `out`, the bound `n ≤ fieldValue out ≤ m`, and the value `ofNat' (fieldValue out)`. -/
theorem parseNatToBounded_two_inv_at {s : String} (p p' : s.Pos) (pre suf : String)
    {n m : Nat} (v : Bounded.LE n m) (hsplit : p.Splits pre suf)
    (hpar : (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE n m)) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ v) :
    ∃ out rest : String,
      IsFixedDigits 2 out ∧ (n ≤ fieldValue out ∧ fieldValue out ≤ m) ∧
      v.val = fieldValue out ∧ suf = out ++ rest ∧ p'.Splits (pre ++ out) rest := by
  unfold parseNatToBounded parseFlexibleNum at hpar
  simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind] at hpar
  rw [parsec_bind_app] at hpar
  cases hpn : parseNum 2 ⟨s, p⟩ with
  | error pos msg => rw [hpn] at hpar; simp at hpar
  | success rem w =>
    rw [hpn] at hpar
    obtain ⟨sr, pr⟩ := rem
    simp only [] at hpar
    by_cases hb : n ≤ w ∧ w ≤ m
    · rw [dif_pos hb] at hpar
      rw [show ((Pure.pure (Bounded.LE.ofNat' w hb) : Parser (Bounded.LE n m)) (⟨sr, pr⟩ : ParseIt))
        = ParseResult.success (⟨sr, pr⟩ : ParseIt) (Bounded.LE.ofNat' w hb) from rfl] at hpar
      simp only [ParseResult.success.injEq, Sigma.mk.injEq] at hpar
      obtain ⟨⟨hsr, hpr⟩, hv⟩ := hpar
      subst hsr; subst hpr
      obtain ⟨out, rest, hfd, hval, hsuf, hsp⟩ := parseNum_inv_at p pr pre suf 2 (by omega) w hsplit hpn
      refine ⟨out, rest, hfd, ?_, ?_, hsuf, hsp⟩
      · rw [← hval]; exact hb
      · rw [← hv]; simp only [Bounded.LE.ofNat']; rw [← hval]; rfl
    · rw [dif_neg hb] at hpar
      rw [Std.Internal.Parsec.fail] at hpar
      simp at hpar



/-- **`parseWith (.y .fourDigit)` success-inversion.** -/
theorem parseWith_year_inv_at {s : String} (p p' : s.Pos) (pre suf : String) (config : FormatConfig)
    (v : Int) (hsplit : p.Splits pre suf)
    (hpar : parseWith config (.y .fourDigit) ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ v) :
    ∃ out rest : String,
      IsFixedDigits 4 out ∧ v = Int.ofNat (fieldValue out) ∧ suf = out ++ rest ∧
      p'.Splits (pre ++ out) rest := by
  -- parseWith config (.y .fourDigit) = Int.ofNat <$> parseNum 4
  rw [show parseWith config (.y .fourDigit) = (Int.ofNat <$> parseNum 4) from rfl] at hpar
  rw [parsec_map_app] at hpar
  cases hpn : parseNum 4 ⟨s, p⟩ with
  | error pos msg => rw [hpn] at hpar; simp at hpar
  | success rem w =>
    rw [hpn] at hpar
    obtain ⟨sr, pr⟩ := rem
    injection hpar with hit hv
    injection hit with hsr hpr
    subst hsr
    simp only [heq_eq_eq] at hpr
    subst hpr
    obtain ⟨out, rest, hfd, hval, hsuf, hsp⟩ := parseNum_inv_at p pr pre suf 4 (by omega) w hsplit hpn
    exact ⟨out, rest, hfd, by rw [← hv, hval], hsuf, hsp⟩



/-- Bridge: `parseWith config (.M (.inl {padding:=2}))` is `parseNatToBounded (parseFlexibleNum 2)`
    at `Bounded.LE 1 12`. Month inversion. -/
theorem parseWith_month_inv_at {s : String} (p p' : s.Pos) (pre suf : String)
    (config : FormatConfig) (v : Month.Ordinal) (hsplit : p.Splits pre suf)
    (hpar : parseWith config (.M (.inl {padding := 2})) ⟨s, p⟩
        = ParseResult.success ⟨s, p'⟩ v) :
    ∃ out rest : String,
      IsFixedDigits 2 out ∧ (1 ≤ fieldValue out ∧ fieldValue out ≤ 12) ∧
      (v.val = fieldValue out) ∧
      suf = out ++ rest ∧ p'.Splits (pre ++ out) rest := by
  rw [show parseWith config (.M (.inl {padding := 2}))
        = (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE 1 12)) from rfl] at hpar
  obtain ⟨out, rest, hfd, hb, hval, hsuf, hsp⟩ :=
    parseNatToBounded_two_inv_at p p' pre suf v hsplit hpar
  exact ⟨out, rest, hfd, hb, hval, hsuf, hsp⟩

/-- Day inversion (`Bounded.LE 1 31`). -/
theorem parseWith_day_inv_at {s : String} (p p' : s.Pos) (pre suf : String)
    (config : FormatConfig) (v : Day.Ordinal) (hsplit : p.Splits pre suf)
    (hpar : parseWith config (.d {padding := 2}) ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ v) :
    ∃ out rest : String,
      IsFixedDigits 2 out ∧ (1 ≤ fieldValue out ∧ fieldValue out ≤ 31) ∧
      (v.val = fieldValue out) ∧
      suf = out ++ rest ∧ p'.Splits (pre ++ out) rest := by
  rw [show parseWith config (.d {padding := 2})
        = (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE 1 31)) from rfl] at hpar
  obtain ⟨out, rest, hfd, hb, hval, hsuf, hsp⟩ :=
    parseNatToBounded_two_inv_at p p' pre suf v hsplit hpar
  exact ⟨out, rest, hfd, hb, hval, hsuf, hsp⟩

/-- Hour inversion (`Bounded.LE 0 23`). -/
theorem parseWith_hour_inv_at {s : String} (p p' : s.Pos) (pre suf : String)
    (config : FormatConfig) (v : Hour.Ordinal) (hsplit : p.Splits pre suf)
    (hpar : parseWith config (.H {padding := 2}) ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ v) :
    ∃ out rest : String,
      IsFixedDigits 2 out ∧ fieldValue out ≤ 23 ∧
      suf = out ++ rest ∧ p'.Splits (pre ++ out) rest := by
  rw [show parseWith config (.H {padding := 2})
        = (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE 0 23)) from rfl] at hpar
  obtain ⟨out, rest, hfd, hb, _, hsuf, hsp⟩ :=
    parseNatToBounded_two_inv_at p p' pre suf v hsplit hpar
  exact ⟨out, rest, hfd, hb.2, hsuf, hsp⟩

/-- Minute inversion (`Bounded.LE 0 59`). -/
theorem parseWith_minute_inv_at {s : String} (p p' : s.Pos) (pre suf : String)
    (config : FormatConfig) (v : Minute.Ordinal) (hsplit : p.Splits pre suf)
    (hpar : parseWith config (.m {padding := 2}) ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ v) :
    ∃ out rest : String,
      IsFixedDigits 2 out ∧ fieldValue out ≤ 59 ∧
      suf = out ++ rest ∧ p'.Splits (pre ++ out) rest := by
  rw [show parseWith config (.m {padding := 2})
        = (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE 0 59)) from rfl] at hpar
  obtain ⟨out, rest, hfd, hb, _, hsuf, hsp⟩ :=
    parseNatToBounded_two_inv_at p p' pre suf v hsplit hpar
  exact ⟨out, rest, hfd, hb.2, hsuf, hsp⟩

/-- `.s` field inversion: a successful second-parse consumed exactly 2 digit chars with value ≤ 59.
    Handles the `allowLeapSeconds = false` else-branch (parse to `Bounded.LE 0 59` then `expandTop`).-/
theorem parseWith_second_inv_at {s : String} (p p' : s.Pos) (pre suf : String)
    (config : FormatConfig) (hcfg : config.allowLeapSeconds = false) (v : Second.Ordinal true)
    (hsplit : p.Splits pre suf)
    (hpar : parseWith config (.s {padding := 2}) ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ v) :
    ∃ out rest : String,
      IsFixedDigits 2 out ∧ fieldValue out ≤ 59 ∧
      suf = out ++ rest ∧ p'.Splits (pre ++ out) rest := by
  rw [show parseWith config (.s {padding := 2})
        = (if config.allowLeapSeconds then parseNatToBounded (parseFlexibleNum 2)
           else (do let res : Bounded.LE 0 59 ← parseNatToBounded (parseFlexibleNum 2)
                    return res.expandTop (by decide))) from rfl] at hpar
  rw [hcfg] at hpar
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Bind.bind] at hpar
  rw [parsec_bind_app] at hpar
  cases hinner : (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE 0 59)) ⟨s, p⟩ with
  | error pos msg => rw [hinner] at hpar; simp at hpar
  | success rem res =>
    rw [hinner] at hpar
    obtain ⟨sr, pr⟩ := rem
    replace hpar : ParseResult.success (⟨sr, pr⟩ : ParseIt)
        (res.expandTop (by decide) : Bounded.LE 0 60) = ParseResult.success ⟨s, p'⟩ v := hpar
    injection hpar with hit _
    injection hit with hsr hpr; subst sr
    simp only [heq_eq_eq] at hpr; subst pr
    obtain ⟨out, rest, hfd, hb, _, hsuf, hsp⟩ :=
      parseNatToBounded_two_inv_at p p' pre suf res hsplit hinner
    exact ⟨out, rest, hfd, hb.2, hsuf, hsp⟩

/-- `.S (.truncated 3)` field inversion: a successful fraction-parse consumed exactly 3 digit
    chars. Mirrors `parseWith_second_inv_at`; only the 3-digit segment + position matter. -/
theorem parseWith_fraction_inv_at {s : String} (p p' : s.Pos) (pre suf : String)
    (config : FormatConfig) (v : Nanosecond.Ordinal) (hsplit : p.Splits pre suf)
    (hpar : parseWith config (.S (.truncated 3)) ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ v) :
    ∃ out rest : String, IsFixedDigits 3 out ∧ suf = out ++ rest ∧ p'.Splits (pre ++ out) rest := by
  rw [show parseWith config (.S (.truncated 3))
        = (parseNatToBounded (parseFractionNum 3 9) : Parser (Bounded.LE 0 999999999)) from rfl] at hpar
  unfold parseNatToBounded parseFractionNum at hpar
  simp only [bind, Bind.bind] at hpar
  rw [parsec_bind_app] at hpar
  cases hinner : (String.toNat! <$> rightPadAscii 9 '0' <$> exactlyChars (satisfy Char.isDigit) 3) ⟨s, p⟩ with
  | error pos msg => rw [hinner] at hpar; simp at hpar
  | success rem w =>
    rw [hinner] at hpar
    obtain ⟨sr, pr⟩ := rem
    replace hpar : (if h : 0 ≤ w ∧ w ≤ 999999999 then
          (pure (Bounded.LE.ofNat' w h) : Parser (Bounded.LE 0 999999999))
        else fail s!"need a natural number in the interval of {0} to {999999999}") ⟨sr, pr⟩
        = ParseResult.success ⟨s, p'⟩ v := hpar
    by_cases hb : 0 ≤ w ∧ w ≤ 999999999
    · rw [dif_pos hb] at hpar
      replace hpar : ParseResult.success (⟨sr, pr⟩ : ParseIt) (Bounded.LE.ofNat' w hb)
        = ParseResult.success ⟨s, p'⟩ v := hpar
      injection hpar with hit _; injection hit with hsr hpr
      subst sr
      simp only [heq_eq_eq] at hpr; subst pr
      rw [parsec_map_app, parsec_map_app] at hinner
      cases hec : exactlyChars (satisfy Char.isDigit) 3 ⟨s, p⟩ with
      | error pos msg => rw [hec] at hinner; simp at hinner
      | success rem2 out =>
        rw [hec] at hinner
        obtain ⟨s2, p2⟩ := rem2
        simp only [ParseResult.success.injEq, Sigma.mk.injEq] at hinner
        obtain ⟨⟨hs2, hp2⟩, _⟩ := hinner
        subst hs2
        simp only [heq_eq_eq] at hp2; subst p2
        obtain ⟨rest, hfd, hsuf, hsp⟩ := exactlyChars_inv_at p p' pre suf out 3 (by omega) hsplit hec
        exact ⟨out, rest, hfd, hsuf, hsp⟩
    · rw [dif_neg hb, Std.Internal.Parsec.fail] at hpar; simp at hpar

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- **`pchar` success-inversion.** A successful `pchar c` at `p` (splitting `s` as `pre ++ suf`)
    forces the string unchanged, the consumed char `c` at the head of `suf`, and advances to a `p'`
    splitting `s` as `pre ++ singleton c | rest`. -/
theorem pchar_success_inv_at {s : String} (p : s.Pos) (pre suf : String) (c : Char) (rem : ParseIt)
    (out : Char) (hsplit : p.Splits pre suf)
    (hpar : pchar c ⟨s, p⟩ = ParseResult.success rem out) :
    ∃ (p' : s.Pos) (rest : String),
      rem = ⟨s, p'⟩ ∧ out = c ∧ suf = String.singleton c ++ rest ∧
      p'.Splits (pre ++ String.singleton c) rest := by
  rw [pchar_eq] at hpar
  by_cases hn : Input.hasNext (⟨s, p⟩ : ParseIt) = true
  · simp only [hn, dif_pos] at hpar
    rw [curr'_eq, next'_eq] at hpar
    by_cases hc : p.get ((hasNext_iff s p).mp hn) = c
    · simp only [hc, if_pos] at hpar
      injection hpar with hit hout
      obtain ⟨sr, pr⟩ := rem
      simp only [Sigma.mk.injEq] at hit
      obtain ⟨hsr, hpr⟩ := hit; subst hsr
      simp only [heq_eq_eq] at hpr; subst hpr
      have hp : p ≠ s.endPos := (hasNext_iff s p).mp hn
      obtain ⟨rest, hrest⟩ := hsplit.exists_eq_singleton_append hp
      rw [hc] at hrest
      refine ⟨p.next hp, rest, rfl, hout.symm, hrest, ?_⟩
      have hsplit' : p.Splits pre (String.singleton c ++ rest) := hrest ▸ hsplit
      have := hsplit'.next
      simpa using this
    · simp only [hc, if_neg, not_false_iff] at hpar; simp at hpar
  · simp only [hn] at hpar; simp at hpar

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- **Sign-alternation success-inversion.** A successful `(pchar '+' *> pure 1) <|>
    (pchar '-' *> pure (-1))` consumed exactly one sign character (`+`→`neg=false`, `-`→`neg=true`),
    leaving the string unchanged and advancing past that character. -/
theorem sign_inv_at {s : String} (p : s.Pos) (pre suf : String) (rem : ParseIt) (a : Int)
    (hsplit : p.Splits pre suf)
    (hpar : ((pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1)) : Parser Int) ⟨s, p⟩
        = ParseResult.success rem a) :
    ∃ (neg : Bool) (p1 : s.Pos) (rest : String),
      rem = ⟨s, p1⟩ ∧
      suf = String.singleton (if neg then '-' else '+') ++ rest ∧
      p1.Splits (pre ++ String.singleton (if neg then '-' else '+')) rest := by
  cases hplus : pchar '+' (⟨s, p⟩ : ParseIt) with
  | success remp cp =>
    obtain ⟨p1, rest, hrem, _, hsuf, hsp⟩ :=
      pchar_success_inv_at p pre suf '+' remp cp hsplit hplus
    subst hrem
    have hsign : ((pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1)) : Parser Int) ⟨s, p⟩
        = ParseResult.success (⟨s, p1⟩ : ParseIt) 1 := by
      rw [orElse_app, seqRight_app, hplus]; rfl
    rw [hsign] at hpar
    injection hpar with hit _
    exact ⟨false, p1, rest, hit.symm, by simpa using hsuf, by simpa using hsp⟩
  | error remp errp =>
    have hpos : remp = (⟨s, p⟩ : ParseIt) := by
      rw [pchar_eq] at hplus
      by_cases hn : Input.hasNext (⟨s, p⟩ : ParseIt) = true
      · simp only [hn, dif_pos] at hplus
        by_cases hc : Input.curr' (⟨s, p⟩ : ParseIt) hn = '+'
        · simp only [hc, if_pos] at hplus; simp at hplus
        · simp only [hc, if_neg, not_false_iff] at hplus; injection hplus with h1 _; exact h1.symm
      · simp only [hn] at hplus; injection hplus with h1 _; exact h1.symm
    subst hpos
    rw [orElse_app, seqRight_app, hplus] at hpar
    simp only [Input.pos, ↓reduceIte] at hpar
    rw [seqRight_app] at hpar
    cases hminus : pchar '-' (⟨s, p⟩ : ParseIt) with
    | error pos msg => rw [hminus] at hpar; simp at hpar
    | success remm cm =>
      rw [hminus] at hpar
      obtain ⟨p1, rest, hrem, _, hsuf, hsp⟩ :=
        pchar_success_inv_at p pre suf '-' remm cm hsplit hminus
      subst hrem
      replace hpar : ParseResult.success (⟨s, p1⟩ : ParseIt) (-1 : Int)
        = ParseResult.success rem a := hpar
      injection hpar with hit _
      exact ⟨true, p1, rest, hit.symm, by simpa using hsuf, by simpa using hsp⟩

/-- `parseWithDate` on a `.modifier` reduces to running `parseWith` then inserting. -/
theorem parseWithDate_modifier_app (b : DateBuilder) (config : FormatConfig) (m : Modifier)
    (it : ParseIt) :
    parseWithDate b config (.modifier m) it
      = (match parseWith config m it with
         | .success rem a => ParseResult.success rem (b.insert m a)
         | .error pos msg => .error pos msg) := by
  unfold parseWithDate
  simp only [bind, Bind.bind, pure]
  rw [parsec_bind_app]
  cases parseWith config m it <;> rfl

/-- `parseWithDate` on a `.string` reduces to running `pstring` then keeping the builder. -/
theorem parseWithDate_string_app (b : DateBuilder) (config : FormatConfig) (sep : String)
    (it : ParseIt) :
    parseWithDate b config (.string sep) it
      = (match pstring sep it with
         | .success rem _ => ParseResult.success rem b
         | .error pos msg => .error pos msg) := by
  unfold parseWithDate
  simp only [pure, SeqRight.seqRight]
  show (Std.Internal.Parsec.bind (pstring sep) (fun _ => Std.Internal.Parsec.pure b)) it = _
  rw [parsec_bind_app]
  cases pstring sep it <;> rfl



/-- `parser.go` at `[]` succeeding forces `build` to have succeeded with the same value/position. -/
theorem go_nil_inv {s : String} (config : FormatConfig) (b : DateBuilder) (p p' : s.Pos)
    (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any b [] ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ zt) :
    b.build .any = some zt ∧ p = p' := by
  unfold parser.go at hgo
  cases hb : b.build .any with
  | none => rw [hb] at hgo; simp [Std.Internal.Parsec.fail] at hgo
  | some res =>
    rw [hb] at hgo
    replace hgo : ParseResult.success (⟨s, p⟩ : ParseIt) res = ParseResult.success ⟨s, p'⟩ zt := hgo
    injection hgo with hit hres
    injection hit with _ hp
    exact ⟨congrArg some hres, hp⟩



-- A successful terminal `parser.go` keeps the original string component.
theorem go_nil_preserves {s : String} (config : FormatConfig) (b : DateBuilder) (p : s.Pos)
    (rem : ParseIt) (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any b [] ⟨s, p⟩ = ParseResult.success rem zt) :
    rem.1 = s := by
  obtain ⟨sf, pf⟩ := rem
  unfold parser.go at hgo
  cases hb : b.build .any with
  | none =>
    rw [hb] at hgo
    simp [Std.Internal.Parsec.fail] at hgo
  | some res =>
    rw [hb] at hgo
    replace hgo : ParseResult.success (⟨s, p⟩ : ParseIt) res =
      ParseResult.success ⟨sf, pf⟩ zt := hgo
    injection hgo with hit _
    injection hit with hsf _
    exact hsf.symm

/-- `exactlyChars.go` preserves the string component of the iterator. -/
theorem exactlyChars_go_preserves {s : String} :
    ∀ (size count : Nat) (acc : String) (p : s.Pos) (rem : ParseIt) (out : String),
      exactlyChars.go (satisfy Char.isDigit) size acc count ⟨s, p⟩
          = ParseResult.success rem out → rem.1 = s := by
  intro size
  -- Induct on the fuel `size - count`.
  suffices h : ∀ (k count : Nat) (acc : String) (p : s.Pos) (rem : ParseIt) (out : String),
      size - count = k →
      exactlyChars.go (satisfy Char.isDigit) size acc count ⟨s, p⟩
          = ParseResult.success rem out → rem.1 = s by
    intro count acc p rem out h'; exact h _ count acc p rem out rfl h'
  intro k
  induction k with
  | zero =>
    intro count acc p rem out hk hgo
    rw [exactlyChars_go_eq, if_pos (by omega)] at hgo
    replace hgo : ParseResult.success (⟨s, p⟩ : ParseIt) acc = ParseResult.success rem out := hgo
    injection hgo with hit _; rw [← hit]
  | succ k ih =>
    intro count acc p rem out hk hgo
    rw [exactlyChars_go_eq, if_neg (by omega), parsec_bind_app] at hgo
    cases hsat : satisfy Char.isDigit (⟨s, p⟩ : ParseIt) with
    | error pos msg => rw [hsat] at hgo; simp at hgo
    | success rem' c =>
      rw [hsat] at hgo
      -- satisfy preserves string: rem'.1 = s
      rw [satisfy_eq] at hsat
      by_cases hn : Input.hasNext (⟨s, p⟩ : ParseIt) = true
      · simp only [hn, dif_pos] at hsat
        by_cases hd : Char.isDigit (Input.curr' (⟨s, p⟩ : ParseIt) hn) = true
        · simp only [hd, if_pos, next'_eq] at hsat
          replace hsat : ParseResult.success
              (⟨s, p.next ((hasNext_iff s p).mp hn)⟩ : ParseIt) _ = ParseResult.success rem' c := hsat
          injection hsat with hit _
          obtain ⟨sr, pr⟩ := rem'
          simp only [Sigma.mk.injEq] at hit
          obtain ⟨hsr, _⟩ := hit; subst hsr
          exact ih count.succ (acc.push c) pr rem out (by omega) hgo
        · simp only [hd, Bool.false_eq_true, if_neg, not_false_iff] at hsat; simp at hsat
      · simp only [hn] at hsat; simp at hsat



/-- `parseWith` (for the modifiers used by the datetime formats) preserves the string component.
    Proven for the specific modifiers via their `exactlyChars`/`parseNum` cores. This is stated for
    an arbitrary modifier by falling back to: if a `parseWith` succeeds we can always read off the
    string, but here we only need the datetime ones. We give the generic `parseNum`-based fields. -/
theorem parseNum_preserves {s : String} (n : Nat) (p : s.Pos) (rem : ParseIt) (v : Nat)
    (hpar : parseNum n ⟨s, p⟩ = ParseResult.success rem v) : rem.1 = s := by
  unfold parseNum at hpar
  rw [parsec_map_app] at hpar
  cases hec : exactlyChars (satisfy Char.isDigit) n ⟨s, p⟩ with
  | error pos msg => rw [hec] at hpar; simp at hpar
  | success rem' out =>
    rw [hec] at hpar
    replace hpar : ParseResult.success rem' (String.toNat! out) = ParseResult.success rem v := hpar
    injection hpar with hit _; rw [← hit]
    exact exactlyChars_go_preserves n 0 "" p rem' out hec

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `satisfy Char.isDigit` preserves the string component on success. -/
theorem satisfy_digit_preserves {s : String} (p : s.Pos) (rem : ParseIt) (c : Char)
    (hpar : (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ = ParseResult.success rem c) :
    rem.1 = s := by
  rw [satisfy_eq] at hpar
  by_cases hn : Input.hasNext (⟨s, p⟩ : ParseIt) = true
  · simp only [hn, dif_pos] at hpar
    by_cases hd : Char.isDigit (Input.curr' (⟨s, p⟩ : ParseIt) hn) = true
    · simp only [hd, if_pos, next'_eq] at hpar
      replace hpar : ParseResult.success
          (⟨s, p.next ((hasNext_iff s p).mp hn)⟩ : ParseIt) _ =
            ParseResult.success rem c := hpar
      injection hpar with hit _
      rw [← hit]
    · simp only [hd, Bool.false_eq_true, if_neg, not_false_iff] at hpar
      simp at hpar
  · simp only [hn] at hpar
    simp at hpar

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `optional (satisfy Char.isDigit)` preserves the string component on success. -/
theorem optional_satisfy_digit_preserves {s : String} (p : s.Pos) (rem : ParseIt)
    (c : Option Char)
    (hpar : optional (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ =
      ParseResult.success rem c) : rem.1 = s := by
  unfold optional at hpar
  change Std.Internal.Parsec.orElse
    (some <$> (satisfy Char.isDigit : Parser Char)) (fun _ => pure none)
      (⟨s, p⟩ : ParseIt) = _ at hpar
  unfold Std.Internal.Parsec.orElse Std.Internal.Parsec.tryCatch at hpar
  rw [parsec_map_app, satisfy_eq] at hpar
  by_cases hn : Input.hasNext (⟨s, p⟩ : ParseIt) = true
  · simp only [hn, dif_pos] at hpar
    by_cases hd : Char.isDigit (Input.curr' (⟨s, p⟩ : ParseIt) hn) = true
    · simp only [hd, if_pos, next'_eq] at hpar
      replace hpar : ParseResult.success
          (⟨s, p.next ((hasNext_iff s p).mp hn)⟩ : ParseIt) _ =
            ParseResult.success rem c := hpar
      injection hpar with hit _
      rw [← hit]
    · simp only [hd, Bool.false_eq_true, if_neg, not_false_iff, Input.pos] at hpar
      replace hpar : ParseResult.success (⟨s, p⟩ : ParseIt) none =
        ParseResult.success rem c := hpar
      injection hpar with hit _
      rw [← hit]
  · have hnfalse : Input.hasNext (⟨s, p⟩ : ParseIt) = false := by
      cases hx : Input.hasNext (⟨s, p⟩ : ParseIt) with
      | false => rfl
      | true => exact (hn hx).elim
    simp [hnfalse, Input.pos] at hpar
    replace hpar : ParseResult.success (⟨s, p⟩ : ParseIt) none =
      ParseResult.success rem c := hpar
    injection hpar with hit _
    rw [← hit]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- `parseOneOrTwoNum` preserves the string component on success. -/
theorem parseOneOrTwoNum_preserves {s : String} (p : s.Pos) (rem : ParseIt) (v : Nat)
    (hpar : parseOneOrTwoNum ⟨s, p⟩ = ParseResult.success rem v) : rem.1 = s := by
  unfold parseOneOrTwoNum at hpar
  simp only [bind, Bind.bind] at hpar
  rw [parsec_bind_app] at hpar
  cases hfirst : (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ with
  | error pos msg =>
    rw [hfirst] at hpar
    simp at hpar
  | success rem₁ c₁ =>
    rw [hfirst] at hpar
    obtain ⟨s₁, p₁⟩ := rem₁
    have hs₁ : s₁ = s := satisfy_digit_preserves p ⟨s₁, p₁⟩ c₁ hfirst
    subst s₁
    simp only [] at hpar
    rw [parsec_bind_app] at hpar
    cases hsecond : optional (satisfy Char.isDigit : Parser Char) ⟨s, p₁⟩ with
    | error pos msg =>
      rw [hsecond] at hpar
      simp at hpar
    | success rem₂ c₂ =>
      rw [hsecond] at hpar
      obtain ⟨s₂, p₂⟩ := rem₂
      have hs₂ : s₂ = s := optional_satisfy_digit_preserves p₁ ⟨s₂, p₂⟩ c₂ hsecond
      subst s₂
      cases c₂ <;> injection hpar with hit _ <;> rw [← hit]

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- A successful digit `satisfy` consumes exactly the returned character. -/
theorem satisfy_digit_success_inv_at {s : String} (p : s.Pos) (pre suf : String)
    (rem : ParseIt) (out : Char) (hsplit : p.Splits pre suf)
    (hpar : (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ = ParseResult.success rem out) :
    ∃ (p' : s.Pos) (rest : String),
      rem = ⟨s, p'⟩ ∧ out.isDigit = true ∧
      suf = String.singleton out ++ rest ∧
      p'.Splits (pre ++ String.singleton out) rest := by
  rw [satisfy_eq] at hpar
  by_cases hn : Input.hasNext (⟨s, p⟩ : ParseIt) = true
  · simp only [hn, dif_pos] at hpar
    rw [curr'_eq, next'_eq] at hpar
    by_cases hd : (p.get ((hasNext_iff s p).mp hn)).isDigit = true
    · simp only [hd, if_pos] at hpar
      injection hpar with hit hout
      obtain ⟨sr, pr⟩ := rem
      simp only [Sigma.mk.injEq] at hit
      obtain ⟨hsr, hpr⟩ := hit
      subst hsr
      simp only [heq_eq_eq] at hpr
      subst hpr
      have hp : p ≠ s.endPos := (hasNext_iff s p).mp hn
      obtain ⟨rest, hrest⟩ := hsplit.exists_eq_singleton_append hp
      refine ⟨p.next hp, rest, rfl, ?_, ?_, ?_⟩
      · rw [← hout]
        exact hd
      · rw [← hout]
        exact hrest
      · have hsplit' :
            p.Splits pre (String.singleton (p.get hp) ++ rest) := hrest ▸ hsplit
        have hnext := hsplit'.next
        simpa [hout] using hnext
    · simp only [hd, Bool.false_eq_true, if_neg, not_false_iff] at hpar
      simp at hpar
  · simp only [hn] at hpar
    simp at hpar

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- A failed digit `satisfy` reports the unchanged iterator. -/
theorem satisfy_digit_error_pos_eq {s : String} (p : s.Pos) (pos : ParseIt)
    (msg : Error)
    (hpar : (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ = ParseResult.error pos msg) :
    pos = ⟨s, p⟩ := by
  rw [satisfy_eq] at hpar
  by_cases hn : Input.hasNext (⟨s, p⟩ : ParseIt) = true
  · simp only [hn, dif_pos] at hpar
    by_cases hd : Char.isDigit (Input.curr' (⟨s, p⟩ : ParseIt) hn) = true
    · simp only [hd, if_pos] at hpar
      simp at hpar
    · simp only [hd, Bool.false_eq_true, if_neg, not_false_iff] at hpar
      injection hpar with hit _
      exact hit.symm
  · simp only [hn] at hpar
    injection hpar with hit _
    exact hit.symm

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- Returning `none` from the optional second digit leaves the iterator unchanged. -/
theorem optional_satisfy_digit_none_eq {s : String} (p : s.Pos) (rem : ParseIt)
    (hpar : optional (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ =
      ParseResult.success rem none) :
    rem = ⟨s, p⟩ := by
  unfold optional at hpar
  change Std.Internal.Parsec.orElse
    (some <$> (satisfy Char.isDigit : Parser Char)) (fun _ => pure none)
      (⟨s, p⟩ : ParseIt) = _ at hpar
  unfold Std.Internal.Parsec.orElse Std.Internal.Parsec.tryCatch at hpar
  rw [parsec_map_app] at hpar
  cases hsat : (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ with
  | success rem' c =>
    rw [hsat] at hpar
    change ParseResult.success rem' (some c) = ParseResult.success rem none at hpar
    simp at hpar
  | error pos msg =>
    rw [hsat] at hpar
    have hpos := satisfy_digit_error_pos_eq p pos msg hsat
    subst hpos
    simp only [Input.pos, ↓reduceIte] at hpar
    change ParseResult.success (⟨s, p⟩ : ParseIt) none =
      ParseResult.success rem none at hpar
    injection hpar with hit _
    exact hit.symm

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- Returning `some c` from the optional second digit consumes exactly that digit. -/
theorem optional_satisfy_digit_some_inv_at {s : String} (p : s.Pos) (pre suf : String)
    (rem : ParseIt) (out : Char) (hsplit : p.Splits pre suf)
    (hpar : optional (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ =
      ParseResult.success rem (some out)) :
    ∃ (p' : s.Pos) (rest : String),
      rem = ⟨s, p'⟩ ∧ out.isDigit = true ∧
      suf = String.singleton out ++ rest ∧
      p'.Splits (pre ++ String.singleton out) rest := by
  unfold optional at hpar
  change Std.Internal.Parsec.orElse
    (some <$> (satisfy Char.isDigit : Parser Char)) (fun _ => pure none)
      (⟨s, p⟩ : ParseIt) = _ at hpar
  unfold Std.Internal.Parsec.orElse Std.Internal.Parsec.tryCatch at hpar
  rw [parsec_map_app] at hpar
  cases hsat : (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ with
  | success rem' c =>
    rw [hsat] at hpar
    change ParseResult.success rem' (some c) =
      ParseResult.success rem (some out) at hpar
    injection hpar with hrem hout
    obtain ⟨p', rest, hrem', hdig, hsuf, hsp⟩ :=
      satisfy_digit_success_inv_at p pre suf rem' c hsplit hsat
    subst hrem
    have hc : c = out := Option.some.inj hout
    subst hc
    exact ⟨p', rest, hrem', hdig, hsuf, hsp⟩
  | error pos msg =>
    rw [hsat] at hpar
    have hpos := satisfy_digit_error_pos_eq p pos msg hsat
    subst hpos
    simp [Input.pos] at hpar
    change ParseResult.success (⟨s, p⟩ : ParseIt) none =
      ParseResult.success rem (some out) at hpar
    simp at hpar

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- A successful `parseOneOrTwoNum` consumes one or two digits and returns their value. -/
theorem parseOneOrTwoNum_inv_at {s : String} (p p' : s.Pos) (pre suf : String)
    (v : Nat) (hsplit : p.Splits pre suf)
    (hpar : parseOneOrTwoNum ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ v) :
    ∃ out rest : String,
      IsDigitsUpTo 2 out ∧ v = fieldValue out ∧ suf = out ++ rest ∧
      p'.Splits (pre ++ out) rest := by
  unfold parseOneOrTwoNum at hpar
  simp only [bind, Bind.bind] at hpar
  rw [parsec_bind_app] at hpar
  cases hfirst : (satisfy Char.isDigit : Parser Char) ⟨s, p⟩ with
  | error pos msg =>
    rw [hfirst] at hpar
    simp at hpar
  | success rem₁ c₁ =>
    rw [hfirst] at hpar
    obtain ⟨p₁, rest₁, hrem₁, hc₁, hsuf₁, hsp₁⟩ :=
      satisfy_digit_success_inv_at p pre suf rem₁ c₁ hsplit hfirst
    subst hrem₁
    simp only [] at hpar
    rw [parsec_bind_app] at hpar
    cases hsecond : optional (satisfy Char.isDigit : Parser Char) ⟨s, p₁⟩ with
    | error pos msg =>
      rw [hsecond] at hpar
      simp at hpar
    | success rem₂ c₂ =>
      rw [hsecond] at hpar
      cases c₂ with
      | none =>
        have hrem₂ := optional_satisfy_digit_none_eq p₁ rem₂ hsecond
        subst hrem₂
        replace hpar : ParseResult.success (⟨s, p₁⟩ : ParseIt) (c₁.toNat - 48) =
            ParseResult.success ⟨s, p'⟩ v := hpar
        injection hpar with hit hv
        injection hit with _ hp₁
        subst hp₁
        let out := String.singleton c₁
        have hdig : IsDigits out := by
          refine ⟨by simp [out], ?_⟩
          intro c hc
          simp [out] at hc
          subst c
          exact hc₁
        refine ⟨out, rest₁, ⟨hdig, by simp [out]⟩, ?_, ?_, ?_⟩
        · rw [← hv, fieldValue_isDigits out hdig]
          simp [out]
        · simpa [out] using hsuf₁
        · simpa [out] using hsp₁
      | some c₂ =>
        obtain ⟨p₂, rest₂, hrem₂, hc₂, hsuf₂, hsp₂⟩ :=
          optional_satisfy_digit_some_inv_at p₁
            (pre ++ String.singleton c₁) rest₁ rem₂ c₂ hsp₁ hsecond
        subst hrem₂
        replace hpar :
            ParseResult.success (⟨s, p₂⟩ : ParseIt)
                ((c₁.toNat - 48) * 10 + (c₂.toNat - 48)) =
              ParseResult.success ⟨s, p'⟩ v := hpar
        injection hpar with hit hv
        injection hit with _ hp₂
        subst hp₂
        let out := String.singleton c₁ ++ String.singleton c₂
        have hdig : IsDigits out := by
          refine ⟨by simp [out], ?_⟩
          intro c hc
          simp [out] at hc
          rcases hc with hc | hc
          · subst c
            exact hc₁
          · subst c
            exact hc₂
        refine ⟨out, rest₂, ⟨hdig, by simp [out]⟩, ?_, ?_, ?_⟩
        · rw [← hv, fieldValue_isDigits out hdig]
          simp [out]
        · rw [hsuf₁, hsuf₂]
          change String.singleton c₁ ++ (String.singleton c₂ ++ rest₂) =
            (String.singleton c₁ ++ String.singleton c₂) ++ rest₂
          rw [String.append_assoc]
        · change p₂.Splits
            (pre ++ (String.singleton c₁ ++ String.singleton c₂)) rest₂
          simpa only [String.append_assoc] using hsp₂

theorem no_beq_of_isDigits {s : String} (hs : IsDigits s) (sep : Char)
    (hsep : sep.isDigit = false) :
    ∀ c ∈ s.toList, (c == sep) = false := by
  intro c hc
  have h := not_mem_of_isDigits hs hsep c hc
  simpa using h

theorem no_sign_of_isDigits {s : String} (hs : IsDigits s) :
    ∀ c ∈ s.toList, (c == '+' || c == '-') = false := by
  intro c hc
  rw [Bool.or_eq_false_iff]
  exact ⟨no_beq_of_isDigits hs '+' (by decide) c hc,
    no_beq_of_isDigits hs '-' (by decide) c hc⟩

theorem three_fields_no_pred (a b c : String) (sep : Char) (pred : Char → Bool)
    (ha : ∀ ch ∈ a.toList, pred ch = false)
    (hb : ∀ ch ∈ b.toList, pred ch = false)
    (hc : ∀ ch ∈ c.toList, pred ch = false)
    (hsep : pred sep = false) :
    ∀ ch ∈ (a ++ String.singleton sep ++ b ++ String.singleton sep ++ c).toList,
      pred ch = false := by
  intro ch hmem
  simp only [String.toList_append, String.toList_singleton, List.mem_append,
    List.mem_singleton] at hmem
  rcases hmem with (((hmem | hmem) | hmem) | hmem) | hmem
  · exact ha ch hmem
  · subst ch
    exact hsep
  · exact hb ch hmem
  · subst ch
    exact hsep
  · exact hc ch hmem

theorem append_sep_no_pred (a b : String) (sep : Char) (pred : Char → Bool)
    (ha : ∀ ch ∈ a.toList, pred ch = false)
    (hb : ∀ ch ∈ b.toList, pred ch = false)
    (hsep : pred sep = false) :
    ∀ ch ∈ (a ++ String.singleton sep ++ b).toList, pred ch = false := by
  intro ch hmem
  simp only [String.toList_append, String.toList_singleton, List.mem_append,
    List.mem_singleton] at hmem
  rcases hmem with (hmem | hmem) | hmem
  · exact ha ch hmem
  · subst ch
    exact hsep
  · exact hb ch hmem

/-- Cedar's offset-length guard strengthens the two raw one-or-two-digit fields to two digits. -/
theorem checkOffsetLen_offset_fields {date time hh mm : String} (neg : Bool)
    (hdateT : ∀ ch ∈ date.toList, (ch == 'T') = false)
    (htimeT : ∀ ch ∈ time.toList, (ch == 'T') = false)
    (htimeSign : ∀ ch ∈ time.toList, (ch == '+' || ch == '-') = false)
    (hhh : IsDigitsUpTo 2 hh) (hmm : IsDigitsUpTo 2 mm)
    (hcheck : checkOffsetLen
      (date ++ String.singleton 'T' ++ time ++
        String.singleton (if neg then '-' else '+') ++ hh ++ mm) = true) :
    IsFixedDigits 2 hh ∧ IsFixedDigits 2 mm := by
  let sign := if neg then '-' else '+'
  let signPred := fun c : Char => c == '+' || c == '-'
  have hsignT : (sign == 'T') = false := by
    simp only [sign]
    cases neg <;> decide
  have hhhT := no_beq_of_isDigits hhh.1 'T' (by decide)
  have hmmT := no_beq_of_isDigits hmm.1 'T' (by decide)
  have htailT :
      ∀ ch ∈ (time ++ String.singleton sign ++ (hh ++ mm)).toList,
        (ch == 'T') = false := by
    intro ch hmem
    simp only [String.toList_append, String.toList_singleton, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with (hmem | hmem) | hmem
    · exact htimeT ch hmem
    · subst ch
      exact hsignT
    · rcases hmem with hmem | hmem
      · exact hhhT ch hmem
      · exact hmmT ch hmem
  have hsignPred : signPred sign = true := by
    simp only [signPred, sign]
    cases neg <;> decide
  have hbodySign : ∀ ch ∈ (hh ++ mm).toList, signPred ch = false := by
    intro ch hmem
    simp only [String.toList_append, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact no_sign_of_isDigits hhh.1 ch hmem
    · exact no_sign_of_isDigits hmm.1 ch hmem
  have hnormalized :
      date ++ String.singleton 'T' ++ time ++ String.singleton sign ++ hh ++ mm =
        date ++ String.singleton 'T' ++
          (time ++ String.singleton sign ++ (hh ++ mm)) := by
    simp only [String.append_assoc]
  simp only [sign] at hnormalized
  rw [hnormalized] at hcheck
  unfold checkOffsetLen at hcheck
  rw [splitToList_eq date (time ++ String.singleton sign ++ (hh ++ mm))
    (· == 'T') 'T' (by simp) hdateT htailT] at hcheck
  change (match (time ++ String.singleton sign ++ (hh ++ mm)).splitToList signPred with
    | [_] => true
    | [_, offset] => offset.length == 4 && offset.all Char.isDigit
    | _ => false) = true at hcheck
  rw [splitToList_eq time (hh ++ mm) signPred sign hsignPred htimeSign hbodySign] at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
  have hlen : hh.length + mm.length = 4 := by
    simpa using hcheck.1
  have hhpos : 0 < hh.length := hhh.1.1
  have hhmx : hh.length ≤ 2 := hhh.2
  have hmpos : 0 < mm.length := hmm.1.1
  have hmmx : mm.length ≤ 2 := hmm.2
  exact ⟨⟨hhh.1, by omega⟩, ⟨hmm.1, by omega⟩⟩

set_option backward.isDefEq.respectTransparency false in
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **`.x .hourMinute` (offset) field inversion.** A successful offset parse consumes a sign and
    one-or-two-digit hour/minute fields within bounds. Cedar's `checkOffsetLen` guard later
    strengthens both fields to exactly two digits. -/
theorem parseWith_offset_inv_at {s : String} (p p' : s.Pos) (pre suf : String)
    (config : FormatConfig) (v : Std.Time.TimeZone.Offset)
    (hsplit : p.Splits pre suf)
    (hpar : parseWith config (.x .hourMinute) ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ v) :
    ∃ (neg : Bool) (hh mm rest : String),
      IsDigitsUpTo 2 hh ∧ IsDigitsUpTo 2 mm ∧
      fieldValue hh ≤ 23 ∧ fieldValue mm ≤ 59 ∧
      suf = String.singleton (if neg then '-' else '+') ++ (hh ++ (mm ++ rest)) ∧
      p'.Splits (pre ++ String.singleton (if neg then '-' else '+') ++ hh ++ mm) rest := by
  rw [show parseWith config (.x .hourMinute) = Std.Time.parseOffset .yes .no false from rfl] at hpar
  unfold Std.Time.parseOffset at hpar
  simp only [bind, Bind.bind] at hpar
  rw [parsec_bind_app] at hpar
  -- Stage 1: the sign alternation.
  cases hsign : ((pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1)) : Parser Int) ⟨s, p⟩ with
  | error pos msg => rw [hsign] at hpar; simp at hpar
  | success rem1 a1 =>
    rw [hsign] at hpar
    obtain ⟨neg, p1, rest1, hrem1, hsuf1, hsp1⟩ := sign_inv_at p pre suf rem1 a1 hsplit hsign
    subst hrem1
    simp only [] at hpar
    -- Stage 2: hours = UnitVal.ofInt <$> parseOneOrTwoNum.
    rw [parsec_bind_app] at hpar
    split at hpar
    case h_2 pos msg heq => simp at hpar
    case h_1 rem2 vhoff heq =>
      rw [parsec_map_app, parsec_bind_app] at heq
      cases hph : parseOneOrTwoNum (⟨s, p1⟩ : ParseIt) with
      | error pos msg => rw [hph] at heq; simp at heq
      | success rem2' vh =>
      rw [hph] at heq
      obtain ⟨s2, p2⟩ := rem2'
      have hs2 : s2 = s := parseOneOrTwoNum_preserves p1 ⟨s2, p2⟩ vh hph
      subst s2
      replace heq : ParseResult.success (⟨s, p2⟩ : ParseIt)
          (UnitVal.ofInt (vh : Int) : Hour.Offset)
          = ParseResult.success rem2 vhoff := heq
      injection heq with hit hvoff
      subst rem2; subst vhoff
      simp only [] at hpar
      obtain ⟨hh, rest2, hhdig, hhval, hhsuf, hhsp⟩ :=
        parseOneOrTwoNum_inv_at p1 p2
          (pre ++ String.singleton (if neg then '-' else '+')) rest1 vh hsp1 hph
      -- Hours guard: success forces ¬(vh < 0 ∨ vh > 23).
      by_cases hg : ((vh : Int) < 0 ∨ (vh : Int) > 23)
      · rw [if_pos hg] at hpar; simp [Std.Internal.Parsec.fail, Std.Internal.Parsec.bind] at hpar
      · rw [if_neg hg] at hpar
        have hhb : fieldValue hh ≤ 23 := by
          simp only [not_or, Int.not_lt] at hg
          have : (vh : Int) ≤ 23 := by omega
          rw [← hhval]; exact_mod_cast this
        -- Stage 3: colon = pure ':' (consumes nothing), then minutes = parseOneOrTwoNum.
        rw [parsec_bind_app] at hpar
        -- minutes = some <$> (pure ':' *> UnitVal.ofInt <$> parseOneOrTwoNum)
        split at hpar
        case h_2 pos msg heqm => simp at hpar
        case h_1 rem3 vmopt heqm =>
          simp only [Bool.false_eq_true, if_false, parsec_map_app, seqRight_app] at heqm
          rw [show (Pure.pure ':' : Parser Char) (⟨s, p2⟩ : ParseIt)
              = ParseResult.success (⟨s, p2⟩ : ParseIt) ':' from rfl] at heqm
          simp only [] at heqm
          simp only [Std.Internal.Parsec.bind] at heqm
          cases hpm : parseOneOrTwoNum (⟨s, p2⟩ : ParseIt) with
          | error pos msg => rw [hpm] at heqm; simp at heqm
          | success rem3' vm =>
          rw [hpm] at heqm
          obtain ⟨s3, p3⟩ := rem3'
          have hs3 : s3 = s := parseOneOrTwoNum_preserves p2 ⟨s3, p3⟩ vm hpm
          subst s3
          replace heqm : ParseResult.success (⟨s, p3⟩ : ParseIt)
              (some (UnitVal.ofInt (vm : Int) : Minute.Offset)) =
                ParseResult.success rem3 vmopt := heqm
          injection heqm with hit hvmopt
          subst rem3; subst vmopt
          simp only [] at hpar
          obtain ⟨mm, rest3, hmdig, hmval, hmsuf, hmsp⟩ :=
            parseOneOrTwoNum_inv_at p2 p3
              (pre ++ String.singleton (if neg then '-' else '+') ++ hh)
              rest2 vm hhsp hpm
          -- Minutes guard: success forces ¬(vm > 59).
          by_cases hgm : ((vm : Int) > 59)
          · rw [if_pos hgm] at hpar; simp [Std.Internal.Parsec.fail, Std.Internal.Parsec.bind] at hpar
          · rw [if_neg hgm] at hpar
            have hmb : fieldValue mm ≤ 59 := by
              simp only [Int.not_lt] at hgm
              have : (vm : Int) ≤ 59 := by omega
              rw [← hmval]; exact_mod_cast this
            -- Stage 4: seconds = pure none, then final return. Identify p'.
            replace hpar : ParseResult.success (⟨s, p3⟩ : ParseIt) _
              = ParseResult.success ⟨s, p'⟩ v := hpar
            injection hpar with hit _
            injection hit with _ hp3
            subst hp3
            refine ⟨neg, hh, mm, rest3, hhdig, hmdig, hhb, hmb, ?_, ?_⟩
            · rw [hsuf1, hhsuf, hmsuf]
            · have := hmsp
              rwa [String.append_assoc, String.append_assoc, ← String.append_assoc,
                ← String.append_assoc] at this ⊢

/-- `pstring` preserves the string component. -/
theorem pstring_preserves {s : String} (sep : String) (p : s.Pos) (rem : ParseIt) (out : String)
    (hpar : pstring sep ⟨s, p⟩ = ParseResult.success rem out) : rem.1 = s := by
  unfold pstring at hpar
  by_cases hg : (s.sliceFrom p).startsWith sep = true
  · simp only [hg, ↓reduceIte] at hpar
    replace hpar : ParseResult.success (⟨s, p.nextn sep.length⟩ : ParseIt) sep
      = ParseResult.success rem out := hpar
    injection hpar with hit _
    rw [← hit]
  · simp only [Bool.not_eq_true] at hg; rw [hg] at hpar; simp at hpar


/-! ### Packaged walk steps

Every `*_full_inv` / `*_go_preserves` walk repeats the same ~20-line block per format item:
`go_cons_app`, case the `parseWithDate`, thread string-preservation, expose the underlying
`parseWith`/`pstring`, and `injection` the positions. These two lemmas package one step each
(modifier / string separator), so a walk step becomes a single
`obtain ⟨p', v, hstep, hgo⟩ := go_step_modifier … hpres hgo`. The modifier version takes the
field's string-preservation fact as a hypothesis (each field has its own `*_preserves` lemma). -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- One `.modifier m` step of a `parser.go` walk: success through `.modifier m :: xs` yields a
    same-string success of the underlying `parseWith m` and the continuation on the inserted
    builder. `hpres` is the field's `parseWithDate`-level string-preservation fact — the level
    every existing `*_preserves` lemma is stated at (`parseWithDate_dateFields_preserves`,
    `parseWithDate_hour_preserves`, …). -/
theorem go_step_modifier {s : String} (config : FormatConfig) (aw : Awareness)
    (b : DateBuilder) (m : Modifier) (xs : FormatString) (p : s.Pos)
    (out : ParseIt) (zt : aw.type)
    (hpres : ∀ (rem : ParseIt) (b' : DateBuilder),
      parseWithDate b config (.modifier m) ⟨s, p⟩ = ParseResult.success rem b' → rem.1 = s)
    (hgo : parser.go config aw b (.modifier m :: xs) ⟨s, p⟩ = ParseResult.success out zt) :
    ∃ (p' : s.Pos) (v : TypeFormat m),
      parseWith config m ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ v ∧
      parser.go config aw (b.insert m v) xs ⟨s, p'⟩ = ParseResult.success out zt := by
  rw [go_cons_app] at hgo
  cases hstep : parseWithDate b config (.modifier m) ⟨s, p⟩ with
  | error pos msg => rw [hstep] at hgo; simp at hgo
  | success rem b' =>
    obtain ⟨sr, pr⟩ := rem
    have hsr : sr = s := hpres ⟨sr, pr⟩ b' hstep
    subst sr
    rw [hstep] at hgo; simp only [] at hgo
    rw [parseWithDate_modifier_app] at hstep
    cases hm : parseWith config m ⟨s, p⟩ with
    | error pos msg => rw [hm] at hstep; simp at hstep
    | success remm vm =>
      rw [hm] at hstep
      replace hstep : ParseResult.success remm (b.insert m vm)
        = ParseResult.success ⟨s, pr⟩ b' := hstep
      obtain ⟨sm, pm⟩ := remm
      injection hstep with hit hb'; injection hit with hsm hpm; subst hsm
      simp only [heq_eq_eq] at hpm; subst hpm; subst hb'
      exact ⟨pm, vm, rfl, hgo⟩

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- One `.string sep` step of a `parser.go` walk (builder unchanged; `pstring` always
    preserves the string component). -/
theorem go_step_string {s : String} (config : FormatConfig) (aw : Awareness)
    (b : DateBuilder) (sep : String) (xs : FormatString) (p : s.Pos)
    (out : ParseIt) (zt : aw.type)
    (hgo : parser.go config aw b (.string sep :: xs) ⟨s, p⟩ = ParseResult.success out zt) :
    ∃ (p' : s.Pos) (o : String),
      pstring sep ⟨s, p⟩ = ParseResult.success ⟨s, p'⟩ o ∧
      parser.go config aw b xs ⟨s, p'⟩ = ParseResult.success out zt := by
  rw [go_cons_app] at hgo
  cases hstep : parseWithDate b config (.string sep) ⟨s, p⟩ with
  | error pos msg => rw [hstep] at hgo; simp at hgo
  | success rem b' =>
    rw [hstep] at hgo; simp only [] at hgo
    rw [parseWithDate_string_app] at hstep
    cases hps : pstring sep (⟨s, p⟩ : ParseIt) with
    | error pos msg => rw [hps] at hstep; simp at hstep
    | success remo o =>
      obtain ⟨so, po⟩ := remo
      have hso : so = s := pstring_preserves sep p ⟨so, po⟩ o hps
      subst so
      rw [hps] at hstep
      replace hstep : ParseResult.success (⟨s, po⟩ : ParseIt) b = ParseResult.success rem b' := hstep
      obtain ⟨sr, pr⟩ := rem
      injection hstep with hit hb'; injection hit with hsr hpr; subst hsr
      simp only [heq_eq_eq] at hpr; subst hpr; subst hb'
      exact ⟨po, o, rfl, hgo⟩


/-- `parseNatToBounded (parseFlexibleNum 2)` preserves the string component. -/
theorem parseNatToBounded_two_preserves {s : String} {n m : Nat} (p : s.Pos) (rem : ParseIt)
    (v : Bounded.LE n m)
    (hpar : (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE n m)) ⟨s, p⟩
        = ParseResult.success rem v) : rem.1 = s := by
  unfold parseNatToBounded parseFlexibleNum at hpar
  simp only [Nat.reduceEqDiff, ↓reduceIte, bind, Bind.bind] at hpar
  rw [parsec_bind_app] at hpar
  cases hpn : parseNum 2 ⟨s, p⟩ with
  | error pos msg => rw [hpn] at hpar; simp at hpar
  | success rem' w =>
    rw [hpn] at hpar
    obtain ⟨sr, pr⟩ := rem'
    have hsr : sr = s := parseNum_preserves 2 p ⟨sr, pr⟩ w hpn
    subst hsr
    simp only [] at hpar
    by_cases hb : n ≤ w ∧ w ≤ m
    · rw [dif_pos hb] at hpar
      replace hpar : ParseResult.success (⟨sr, pr⟩ : ParseIt) (Bounded.LE.ofNat' w hb)
        = ParseResult.success rem v := hpar
      injection hpar with hit _
      rw [← hit]
    · rw [dif_neg hb, Std.Internal.Parsec.fail] at hpar; simp at hpar



/-- Each DateOnly/DateUTC field step of `parseWithDate` preserves the string component. Covers the
    modifiers `.y .fourDigit`, `.M (.inl _)`, `.d _`, `.H _`, `.m _`, and any `.string`. -/
theorem parseWithDate_dateFields_preserves {s : String} (b : DateBuilder) (config : FormatConfig)
    (mod : FormatPart) (p : s.Pos) (rem : ParseIt) (b' : DateBuilder)
    (hmod : mod = .modifier (.y .fourDigit) ∨ mod = .modifier (.M (.inl {padding := 2})) ∨
            mod = .modifier (.d {padding := 2}) ∨ (∃ sep, mod = .string sep))
    (hpar : parseWithDate b config mod ⟨s, p⟩ = ParseResult.success rem b') : rem.1 = s := by
  rcases hmod with h | h | h | ⟨sep, h⟩ <;> subst h
  · -- year
    rw [parseWithDate_modifier_app] at hpar
    cases hy : parseWith config (.y .fourDigit) ⟨s, p⟩ with
    | error pos msg => rw [hy] at hpar; simp at hpar
    | success rem' v =>
      rw [hy] at hpar
      replace hpar : ParseResult.success rem' (b.insert (.y .fourDigit) v)
        = ParseResult.success rem b' := hpar
      injection hpar with hit _; rw [← hit]
      rw [show parseWith config (.y .fourDigit) = (Int.ofNat <$> parseNum 4) from rfl,
        parsec_map_app] at hy
      cases hpn : parseNum 4 ⟨s, p⟩ with
      | error pos msg => rw [hpn] at hy; simp at hy
      | success rem'' w =>
        rw [hpn] at hy
        replace hy : ParseResult.success rem'' (Int.ofNat w) = ParseResult.success rem' v := hy
        injection hy with hit2 _; rw [← hit2]; exact parseNum_preserves 4 p rem'' w hpn
  · -- month
    rw [parseWithDate_modifier_app] at hpar
    cases hm : parseWith config (.M (.inl {padding := 2})) ⟨s, p⟩ with
    | error pos msg => rw [hm] at hpar; simp at hpar
    | success rem' v =>
      rw [hm] at hpar
      replace hpar : ParseResult.success rem' (b.insert (.M (.inl {padding := 2})) v)
        = ParseResult.success rem b' := hpar
      injection hpar with hit _; rw [← hit]
      exact parseNatToBounded_two_preserves p rem' v
        (by rw [show parseWith config (.M (.inl {padding := 2}))
              = (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE 1 12)) from rfl] at hm;
            exact hm)
  · -- day
    rw [parseWithDate_modifier_app] at hpar
    cases hd : parseWith config (.d {padding := 2}) ⟨s, p⟩ with
    | error pos msg => rw [hd] at hpar; simp at hpar
    | success rem' v =>
      rw [hd] at hpar
      replace hpar : ParseResult.success rem' (b.insert (.d {padding := 2}) v)
        = ParseResult.success rem b' := hpar
      injection hpar with hit _; rw [← hit]
      exact parseNatToBounded_two_preserves p rem' v
        (by rw [show parseWith config (.d {padding := 2})
              = (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE 1 31)) from rfl] at hd;
            exact hd)
  · -- string separator
    rw [parseWithDate_string_app] at hpar
    cases hs : pstring sep ⟨s, p⟩ with
    | error pos msg => rw [hs] at hpar; simp at hpar
    | success rem' o =>
      rw [hs] at hpar
      replace hpar : ParseResult.success rem' b = ParseResult.success rem b' := hpar
      injection hpar with hit _; rw [← hit]; exact pstring_preserves sep p rem' o hs



open Std.Time.GenericFormat in
/-- **DateOnly full parse inversion.** If the DateOnly format's `parser.go` succeeds from the empty
    builder over the whole string `s`, ending at `endPos` with value `zt`, then `s` decomposes as the
    rendering of a well-formed date, and `build` succeeds on the corresponding filled builder. -/
theorem dateOnly_full_inv {s : String} (config : FormatConfig) (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2})]
        ⟨s, s.startPos⟩ = ParseResult.success ⟨s, s.endPos⟩ zt) :
    ∃ (year month day : String)
      (hm : 1 ≤ fieldValue month ∧ fieldValue month ≤ 12)
      (hd : 1 ≤ fieldValue day ∧ fieldValue day ≤ 31),
      IsFixedDigits 4 year ∧ IsFixedDigits 2 month ∧ IsFixedDigits 2 day ∧
      s = year ++ "-" ++ month ++ "-" ++ day ∧
      ({ ({} : DateBuilder) with
              y := some (Int.ofNat (fieldValue year)),
              M := some (Bounded.LE.ofNat' (fieldValue month) hm),
              d := some (Bounded.LE.ofNat' (fieldValue day) hd) }).build .any = some zt := by
  have hsplit0 : s.startPos.Splits "" s := String.splits_startPos s
  -- Step 1: year modifier.
  rw [go_cons_app] at hgo
  cases hstep1 : parseWithDate ({} : DateBuilder) config (.modifier (.y .fourDigit)) ⟨s, s.startPos⟩
    with
  | error pos msg => rw [hstep1] at hgo; simp at hgo
  | success rem1 b1 =>
    obtain ⟨s1, p1⟩ := rem1
    have hs1 : s1 = s :=
      parseWithDate_dateFields_preserves _ config _ s.startPos ⟨s1, p1⟩ b1 (Or.inl rfl) hstep1
    subst s1
    rw [hstep1] at hgo; simp only [] at hgo
    -- Recover the year segment.
    rw [parseWithDate_modifier_app] at hstep1
    cases hy : parseWith config (.y .fourDigit) ⟨s, s.startPos⟩ with
    | error pos msg => rw [hy] at hstep1; simp at hstep1
    | success remy vy =>
      -- b1 = insert; the position is p1.
      rw [hy] at hstep1
      obtain ⟨sy, py⟩ := remy
      replace hstep1 : ParseResult.success (⟨sy, py⟩ : ParseIt)
        (({} : DateBuilder).insert (.y .fourDigit) vy) = ParseResult.success ⟨s, p1⟩ b1 := hstep1
      injection hstep1 with hit hb1
      injection hit with hsy hpy; subst sy
      simp only [heq_eq_eq] at hpy; subst py
      obtain ⟨year, rest1, hyfd, hyval, hysuf, hysp⟩ :=
        parseWith_year_inv_at s.startPos p1 "" s config vy hsplit0 hy
      rw [String.empty_append] at hysp
      -- Step 2: separator.
      rw [go_cons_app] at hgo
      cases hstep2 : parseWithDate b1 config (.string "-") ⟨s, p1⟩ with
      | error pos msg => rw [hstep2] at hgo; simp at hgo
      | success rem2 b2 =>
        obtain ⟨s2, p2⟩ := rem2
        have hs2 : s2 = s :=
          parseWithDate_dateFields_preserves _ config _ p1 ⟨s2, p2⟩ b2 (Or.inr (Or.inr (Or.inr ⟨"-", rfl⟩))) hstep2
        subst s2
        rw [hstep2] at hgo; simp only [] at hgo
        rw [parseWithDate_string_app] at hstep2
        cases hsep : pstring "-" (⟨s, p1⟩ : ParseIt) with
        | error pos msg => rw [hsep] at hstep2; simp at hstep2
        | success remsep osep =>
          rw [hsep] at hstep2
          obtain ⟨ss, ps⟩ := remsep
          replace hstep2 : ParseResult.success (⟨ss, ps⟩ : ParseIt) b1
            = ParseResult.success ⟨s, p2⟩ b2 := hstep2
          injection hstep2 with hit hb2; injection hit with hss hps; subst ss
          simp only [heq_eq_eq] at hps; subst ps
          obtain ⟨rest2, _, hsepsuf, hsepsp⟩ := pstring_inv_at p1 p2 year rest1 "-" osep hysp hsep
          -- Step 3: month.
          rw [go_cons_app] at hgo
          cases hstep3 : parseWithDate b2 config (.modifier (.M (.inl {padding := 2}))) ⟨s, p2⟩ with
          | error pos msg => rw [hstep3] at hgo; simp at hgo
          | success rem3 b3 =>
            obtain ⟨s3, p3⟩ := rem3
            have hs3 : s3 = s :=
              parseWithDate_dateFields_preserves _ config _ p2 ⟨s3, p3⟩ b3 (Or.inr (Or.inl rfl)) hstep3
            subst s3
            rw [hstep3] at hgo; simp only [] at hgo
            rw [parseWithDate_modifier_app] at hstep3
            cases hm : parseWith config (.M (.inl {padding := 2})) (⟨s, p2⟩ : ParseIt) with
            | error pos msg => rw [hm] at hstep3; simp at hstep3
            | success remm vm =>
              rw [hm] at hstep3
              obtain ⟨sm, pm⟩ := remm
              replace hstep3 : ParseResult.success (⟨sm, pm⟩ : ParseIt)
                (b2.insert (.M (.inl {padding := 2})) vm) = ParseResult.success ⟨s, p3⟩ b3 := hstep3
              injection hstep3 with hit hb3; injection hit with hsm hpm; subst sm
              simp only [heq_eq_eq] at hpm; subst pm
              obtain ⟨month, rest3, hmfd, hmb, hmval, hmsuf, hmsp⟩ :=
                parseWith_month_inv_at p2 p3 (year ++ "-") rest2 config vm hsepsp hm
              -- Step 4: separator.
              rw [go_cons_app] at hgo
              cases hstep4 : parseWithDate b3 config (.string "-") ⟨s, p3⟩ with
              | error pos msg => rw [hstep4] at hgo; simp at hgo
              | success rem4 b4 =>
                obtain ⟨s4, p4⟩ := rem4
                have hs4 : s4 = s :=
                  parseWithDate_dateFields_preserves _ config _ p3 ⟨s4, p4⟩ b4 (Or.inr (Or.inr (Or.inr ⟨"-", rfl⟩))) hstep4
                subst s4
                rw [hstep4] at hgo; simp only [] at hgo
                rw [parseWithDate_string_app] at hstep4
                cases hsep2 : pstring "-" (⟨s, p3⟩ : ParseIt) with
                | error pos msg => rw [hsep2] at hstep4; simp at hstep4
                | success remsep2 osep2 =>
                  rw [hsep2] at hstep4
                  obtain ⟨ss2, ps2⟩ := remsep2
                  replace hstep4 : ParseResult.success (⟨ss2, ps2⟩ : ParseIt) b3
                    = ParseResult.success ⟨s, p4⟩ b4 := hstep4
                  injection hstep4 with hit hb4; injection hit with hss2 hps2; subst ss2
                  simp only [heq_eq_eq] at hps2; subst ps2
                  obtain ⟨rest4, _, hsep2suf, hsep2sp⟩ :=
                    pstring_inv_at p3 p4 (year ++ "-" ++ month) rest3 "-" osep2 hmsp hsep2
                  -- Step 5: day.
                  rw [go_cons_app] at hgo
                  cases hstep5 : parseWithDate b4 config (.modifier (.d {padding := 2})) ⟨s, p4⟩ with
                  | error pos msg => rw [hstep5] at hgo; simp at hgo
                  | success rem5 b5 =>
                    obtain ⟨s5, p5⟩ := rem5
                    have hs5 : s5 = s :=
                      parseWithDate_dateFields_preserves _ config _ p4 ⟨s5, p5⟩ b5 (Or.inr (Or.inr (Or.inl rfl))) hstep5
                    subst s5
                    rw [hstep5] at hgo; simp only [] at hgo
                    rw [parseWithDate_modifier_app] at hstep5
                    cases hd : parseWith config (.d {padding := 2}) (⟨s, p4⟩ : ParseIt) with
                    | error pos msg => rw [hd] at hstep5; simp at hstep5
                    | success remd vd =>
                      rw [hd] at hstep5
                      obtain ⟨sd, pd⟩ := remd
                      replace hstep5 : ParseResult.success (⟨sd, pd⟩ : ParseIt)
                        (b4.insert (.d {padding := 2}) vd) = ParseResult.success ⟨s, p5⟩ b5 := hstep5
                      injection hstep5 with hit hb5; injection hit with hsd hpd; subst sd
                      simp only [heq_eq_eq] at hpd; subst pd
                      obtain ⟨day, rest5, hdfd, hdb, hdval, hdsuf, hdsp⟩ :=
                        parseWith_day_inv_at p4 p5 (year ++ "-" ++ month ++ "-") rest4 config vd
                          hsep2sp hd
                      -- Step 6: nil / build.
                      obtain ⟨hbuild, hp5⟩ := go_nil_inv config b5 p5 s.endPos zt hgo
                      have hrest5 : rest5 = "" := by
                        rw [hp5] at hdsp; exact hdsp.eq_endPos_iff.mp rfl
                      subst hrest5
                      rw [String.append_empty] at hdsuf
                      have hstr : s = year ++ "-" ++ month ++ "-" ++ day := by
                        rw [hysuf, hsepsuf, hmsuf, hsep2suf, hdsuf]
                        simp only [String.append_assoc]
                      refine ⟨year, month, day, hmb, hdb, hyfd, hmfd, hdfd, hstr, ?_⟩
                      -- The builder b5 equals the assembled record; reconstruct from the inserts.
                      rw [← hbuild, ← hb5, ← hb4, ← hb3, ← hb2, ← hb1]
                      -- Rewrite the parsed values into the grammar's field values.
                      subst hyval
                      have hvm : vm = Bounded.LE.ofNat' (fieldValue month) hmb :=
                        Subtype.ext (by rw [hmval]; rfl)
                      have hvd : vd = Bounded.LE.ofNat' (fieldValue day) hdb :=
                        Subtype.ext (by rw [hdval]; rfl)
                      rw [hvm, hvd]
                      rfl



open Std.Time Std.Time.Internal Std.Time.GenericFormat in
-- Calendar validity is independent of the optional time, fraction, and offset fields.
theorem build_datetime_inv {yr mo dy : Nat}
    (H : Option Hour.Ordinal) (m : Option Minute.Ordinal) (sec : Option (Second.Ordinal true))
    (S : Option Nanosecond.Ordinal) (off : Option Std.Time.TimeZone.Offset)
    (hm : 1 ≤ mo ∧ mo ≤ 12) (hd : 1 ≤ dy ∧ dy ≤ 31)
    (zt : Std.Time.ZonedDateTime)
    (hbuild : ({ ({} : DateBuilder) with
        y := some (Int.ofNat yr),
        M := some (Bounded.LE.ofNat' mo hm),
        d := some (Bounded.LE.ofNat' dy hd),
        H := H, m := m, s := sec, S := S, x := off }).build .any = some zt) :
    dy ≤ daysInMonth yr mo := by
  let offset := off.getD TimeZone.Offset.zero
  letI : Decidable (Year.Offset.Valid (Int.ofNat yr)
      (Bounded.LE.ofNat' mo hm) (Bounded.LE.ofNat' dy hd)) := Day.instDecidableLeOrdinal
  have hbuild_eq :
      ({ ({} : DateBuilder) with
          y := some (Int.ofNat yr),
          M := some (Bounded.LE.ofNat' mo hm),
          d := some (Bounded.LE.ofNat' dy hd),
          H := H, m := m, s := sec, S := S, x := off }).build .any =
        (fun x => ZonedDateTime.ofPlainDateTime x
            (TimeZone.ZoneRules.ofTimeZone
              { offset,
                name := offset.toIsoString true,
                abbreviation := offset.toIsoString true,
                isDST := false })) <$>
          (if h : Year.Offset.Valid (Int.ofNat yr)
              (Bounded.LE.ofNat' mo hm) (Bounded.LE.ofNat' dy hd) then
            some { date := { year := Int.ofNat yr, month := Bounded.LE.ofNat' mo hm,
                             day := Bounded.LE.ofNat' dy hd, valid := h },
                   time := PlainTime.mk (H.getD ⟨0, by decide⟩) (m.getD 0)
                     (sec.getD 0) (S.getD 0) }
          else none) := by
    cases H <;> cases m <;> cases sec <;> cases S <;> cases off <;> rfl
  rw [hbuild_eq] at hbuild
  by_cases hvalid : Year.Offset.Valid (Int.ofNat yr) (Bounded.LE.ofNat' mo hm)
      (Bounded.LE.ofNat' dy hd)
  · have hb : (Bounded.LE.ofNat' dy hd : Day.Ordinal).val
        ≤ (Month.Ordinal.days (Year.Offset.isLeap (Int.ofNat yr))
            (Bounded.LE.ofNat' mo hm)).val := hvalid
    have hbridge := days_eq_daysInMonth yr mo (Bounded.LE.ofNat' mo hm)
      (Year.Offset.isLeap (Int.ofNat yr)) rfl (isLeap_ofNat yr).symm hm
    rw [← hbridge] at hb
    have : (dy : Int) ≤ (daysInMonth yr mo : Int) := hb
    exact_mod_cast this
  · rw [dif_neg hvalid] at hbuild
    simp at hbuild

open Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **`build` inversion (date-only).** If the DateOnly builder (with `y`/`M`/`d` set from
    nonnegative year/month/day fields) `build`s successfully, then the day satisfies the exact
    grammar bound `day ≤ daysInMonth year month`. This is where `constraintsWf`'s day bound comes
    from — the `year.Valid` guard inside `build`, bridged to `daysInMonth` via `days_eq_daysInMonth`
    and `isLeap_ofNat`. -/
theorem build_dateOnly_inv {yr mo dy : Nat}
    (hm : 1 ≤ mo ∧ mo ≤ 12) (hd : 1 ≤ dy ∧ dy ≤ 31)
    (zt : Std.Time.ZonedDateTime)
    (hbuild : ({ ({} : DateBuilder) with
        y := some (Int.ofNat yr),
        M := some (Bounded.LE.ofNat' mo hm),
        d := some (Bounded.LE.ofNat' dy hd) }).build .any = some zt) :
    dy ≤ daysInMonth yr mo :=
  build_datetime_inv none none none none none hm hd zt hbuild




open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- The DateOnly `parser.go` preserves the string component of the iterator on success. -/
theorem dateOnly_go_preserves {s : String} (config : FormatConfig) (p : s.Pos) (rem : ParseIt)
    (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2})]
        ⟨s, p⟩ = ParseResult.success rem zt) : rem.1 = s := by
  -- Thread the 5 steps via the packaged walk-step lemmas, tracking only string preservation.
  obtain ⟨p1, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p _ zt
    (fun r b' h => parseWithDate_dateFields_preserves _ config _ p r b' (Or.inl rfl) h) hgo
  obtain ⟨p2, _, _, hgo⟩ := go_step_string config .any _ "-" _ p1 _ zt hgo
  obtain ⟨p3, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p2 _ zt
    (fun r b' h => parseWithDate_dateFields_preserves _ config _ p2 r b' (Or.inr (Or.inl rfl)) h)
    hgo
  obtain ⟨p4, _, _, hgo⟩ := go_step_string config .any _ "-" _ p3 _ zt hgo
  obtain ⟨p5, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p4 _ zt
    (fun r b' h => parseWithDate_dateFields_preserves _ config _ p4 r b'
      (Or.inr (Or.inr (Or.inl rfl))) h) hgo
  exact go_nil_preserves config _ p5 rem zt hgo

-- Invert the `Parser.run`/`<* eof` wrapper once the inner parser is known to preserve its string.
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
theorem parse_ok_inv_of_preserves (F : GenericFormat .any) (str : String)
    (zt : Std.Time.ZonedDateTime) (parts : List FormatPart)
    (hparser : parser F.string F.config .any = parser.go F.config .any {} parts)
    (hpreserves : ∀ rem a,
      parser.go F.config .any {} parts ⟨str, str.startPos⟩ = ParseResult.success rem a →
      rem.1 = str)
    (h : F.parse str = .ok zt) :
    parser.go F.config .any {} parts ⟨str, str.startPos⟩ =
      ParseResult.success ⟨str, str.endPos⟩ zt := by
  unfold GenericFormat.parse Std.Internal.Parsec.String.Parser.run at h
  rw [seqLeft_app] at h
  cases hp : parser.go F.config .any {} parts ⟨str, str.startPos⟩ with
  | error pos msg =>
    rw [hparser, hp] at h
    simp at h
  | success rem a =>
    rw [hparser] at h
    have hsf : rem.1 = str := hpreserves rem a hp
    obtain ⟨sf, pf⟩ := rem
    simp only [] at hsf
    subst sf
    rw [hp] at h
    simp only [] at h
    cases heof : eof (⟨str, pf⟩ : ParseIt) with
    | error pos msg =>
      rw [heof] at h
      simp at h
    | success rem' u =>
      rw [heof] at h
      replace h : Except.ok a = Except.ok zt := h
      injection h with ha
      subst ha
      have hpf : pf = str.endPos := by
        unfold eof at heof
        by_cases hn : Input.hasNext (⟨str, pf⟩ : ParseIt) = true
        · exfalso
          rw [hn] at heof
          replace heof : ParseResult.error (⟨str, pf⟩ : ParseIt)
              (.other "expected end of input") = ParseResult.success rem' u := heof
          simp at heof
        · simp only [Bool.not_eq_true] at hn
          by_contra hpne
          exact absurd ((hasNext_iff str pf).mpr hpne) (by rw [hn]; simp)
      subst hpf
      rfl



open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- **DateOnly `parse` success-inversion.** If `DateOnly.parse str = .ok zt`, the inner `parser.go`
    succeeded consuming the whole string (ending at `endPos`). Combines `<* eof` inversion with the
    DateOnly string-preservation lemma. -/
theorem dateOnly_parse_ok_inv (str : String) (zt : Std.Time.ZonedDateTime)
    (h : DateOnly.parse str = .ok zt) :
    parser.go DateOnly.config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2})]
        ⟨str, str.startPos⟩ = ParseResult.success ⟨str, str.endPos⟩ zt :=
  parse_ok_inv_of_preserves DateOnly str zt _ rfl
    (fun rem a hp => dateOnly_go_preserves DateOnly.config str.startPos rem a hp) h



open Cedar.Spec.Ext.Datetime in
/-- **DateOnly case of `wf_of_parse`.** If `DateOnly.parse str = .ok zt`, then `str` is the rendering
    of a fully well-formed date-only `DatetimeComponents`. -/
theorem dateOnly_wf_inv (str : String) (zt : Std.Time.ZonedDateTime)
    (h : DateOnly.parse str = .ok zt) :
    ∃ c : DatetimeComponents, str = c.asString ∧ c.syntaxWf ∧ c.constraintsWf := by
  have hgo := dateOnly_parse_ok_inv str zt h
  obtain ⟨year, month, day, hm, hd, hyfd, hmfd, hdfd, hstr, hbuild⟩ :=
    dateOnly_full_inv DateOnly.config zt hgo
  -- The day bound tightens to `≤ daysInMonth` via `build`.
  have hdayle : fieldValue day ≤ daysInMonth (fieldValue year) (fieldValue month) :=
    build_dateOnly_inv hm hd zt hbuild
  refine ⟨{ date := { year, month, day }, time := none }, ?_, ?_, ?_⟩
  · -- asString
    show str = ({ year, month, day } : DateComponents).asString ++ ""
    rw [String.append_empty]
    show str = year ++ "-" ++ month ++ "-" ++ day
    exact hstr
  · exact ⟨⟨hyfd, hmfd, hdfd⟩, trivial⟩
  · exact ⟨⟨hm.1, hm.2, hd.1, hdayle⟩, trivial⟩



/-! ## Phase 1: time-field string preservation helpers -/

/-- `parseWithDate` on the hour modifier preserves the string component. -/
theorem parseWithDate_hour_preserves {s : String} (b : DateBuilder) (config : FormatConfig)
    (p : s.Pos) (rem : ParseIt) (b' : DateBuilder)
    (hpar : parseWithDate b config (.modifier (.H {padding := 2})) ⟨s, p⟩
        = ParseResult.success rem b') : rem.1 = s := by
  rw [parseWithDate_modifier_app] at hpar
  cases hH : parseWith config (.H {padding := 2}) ⟨s, p⟩ with
  | error pos msg => rw [hH] at hpar; simp at hpar
  | success rem' v =>
    rw [hH] at hpar
    replace hpar : ParseResult.success rem' (b.insert (.H {padding := 2}) v)
      = ParseResult.success rem b' := hpar
    injection hpar with hit _; rw [← hit]
    exact parseNatToBounded_two_preserves p rem' v
      (by rw [show parseWith config (.H {padding := 2})
            = (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE 0 23)) from rfl] at hH;
          exact hH)

/-- `parseWithDate` on the minute modifier preserves the string component. -/
theorem parseWithDate_minute_preserves {s : String} (b : DateBuilder) (config : FormatConfig)
    (p : s.Pos) (rem : ParseIt) (b' : DateBuilder)
    (hpar : parseWithDate b config (.modifier (.m {padding := 2})) ⟨s, p⟩
        = ParseResult.success rem b') : rem.1 = s := by
  rw [parseWithDate_modifier_app] at hpar
  cases hM : parseWith config (.m {padding := 2}) ⟨s, p⟩ with
  | error pos msg => rw [hM] at hpar; simp at hpar
  | success rem' v =>
    rw [hM] at hpar
    replace hpar : ParseResult.success rem' (b.insert (.m {padding := 2}) v)
      = ParseResult.success rem b' := hpar
    injection hpar with hit _; rw [← hit]
    exact parseNatToBounded_two_preserves p rem' v
      (by rw [show parseWith config (.m {padding := 2})
            = (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE 0 59)) from rfl] at hM;
          exact hM)

/-- `parseWith` on the second modifier (leap seconds disabled) preserves the string component. -/
theorem parseWith_second_preserves {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (p : s.Pos) (rem : ParseIt) (v : Second.Ordinal true)
    (hpar : parseWith config (.s {padding := 2}) ⟨s, p⟩ = ParseResult.success rem v) : rem.1 = s := by
  rw [show parseWith config (.s {padding := 2})
        = (if config.allowLeapSeconds then parseNatToBounded (parseFlexibleNum 2)
           else (do let res : Bounded.LE 0 59 ← parseNatToBounded (parseFlexibleNum 2)
                    return res.expandTop (by decide))) from rfl] at hpar
  rw [hcfg] at hpar
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Bind.bind] at hpar
  rw [parsec_bind_app] at hpar
  cases hinner : (parseNatToBounded (parseFlexibleNum 2) : Parser (Bounded.LE 0 59)) ⟨s, p⟩ with
  | error pos msg => rw [hinner] at hpar; simp at hpar
  | success rem' res =>
    rw [hinner] at hpar
    obtain ⟨sr, pr⟩ := rem'
    have hsr : sr = s := parseNatToBounded_two_preserves p ⟨sr, pr⟩ res hinner
    replace hpar : ParseResult.success (⟨sr, pr⟩ : ParseIt)
        (res.expandTop (by decide) : Bounded.LE 0 60) = ParseResult.success rem v := hpar
    injection hpar with hit _; rw [← hit]; exact hsr

/-- `parseWithDate` on the second modifier (leap seconds disabled) preserves the string component. -/
theorem parseWithDate_second_preserves {s : String} (b : DateBuilder) (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (p : s.Pos) (rem : ParseIt) (b' : DateBuilder)
    (hpar : parseWithDate b config (.modifier (.s {padding := 2})) ⟨s, p⟩
        = ParseResult.success rem b') : rem.1 = s := by
  rw [parseWithDate_modifier_app] at hpar
  cases hS : parseWith config (.s {padding := 2}) ⟨s, p⟩ with
  | error pos msg => rw [hS] at hpar; simp at hpar
  | success rem' v =>
    rw [hS] at hpar
    replace hpar : ParseResult.success rem' (b.insert (.s {padding := 2}) v)
      = ParseResult.success rem b' := hpar
    injection hpar with hit _; rw [← hit]
    exact parseWith_second_preserves config hcfg p rem' v hS

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal
  Std.Time.GenericFormat in
-- Invert the eleven format parts shared by every time-bearing datetime parser.
theorem datetimePrefix_inv {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (tail : FormatString)
    (out : ParseIt) (zt : ZonedDateTime)
    (hgo : parser.go config .any {}
      ([.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
        .string "-", .modifier (.d {padding := 2}), .string "T",
        .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
        .string ":", .modifier (.s {padding := 2})] ++ tail)
      ⟨s, s.startPos⟩ = ParseResult.success out zt) :
    ∃ (year month day hh mm ss rest : String)
      (hm : 1 ≤ fieldValue month ∧ fieldValue month ≤ 12)
      (hd : 1 ≤ fieldValue day ∧ fieldValue day ≤ 31)
      (H : Hour.Ordinal) (m : Minute.Ordinal) (sec : Second.Ordinal true)
      (p : s.Pos),
      IsFixedDigits 4 year ∧ IsFixedDigits 2 month ∧ IsFixedDigits 2 day ∧
      IsFixedDigits 2 hh ∧ IsFixedDigits 2 mm ∧ IsFixedDigits 2 ss ∧
      fieldValue hh ≤ 23 ∧ fieldValue mm ≤ 59 ∧ fieldValue ss ≤ 59 ∧
      s = year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss ++ rest ∧
      p.Splits (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss)
        rest ∧
      parser.go config .any
        { ({} : DateBuilder) with
          y := some (Int.ofNat (fieldValue year)),
          M := some (Bounded.LE.ofNat' (fieldValue month) hm),
          d := some (Bounded.LE.ofNat' (fieldValue day) hd),
          H := some H, m := some m, s := some sec }
        tail ⟨s, p⟩ = ParseResult.success out zt := by
  have hsplit0 : s.startPos.Splits "" s := String.splits_startPos s
  obtain ⟨p1, vy, hy, hgo⟩ := go_step_modifier config .any _ _ _ s.startPos out zt
    (fun r b h => parseWithDate_dateFields_preserves _ config _ s.startPos r b
      (Or.inl rfl) h) hgo
  obtain ⟨year, rest1, hyfd, hyval, hysuf, hysp⟩ :=
    parseWith_year_inv_at s.startPos p1 "" s config vy hsplit0 hy
  rw [String.empty_append] at hysp
  obtain ⟨p2, oy, hsep, hgo⟩ := go_step_string config .any _ "-" _ p1 out zt hgo
  obtain ⟨rest2, _, hsepsuf, hsepsp⟩ :=
    pstring_inv_at p1 p2 year rest1 "-" oy hysp hsep
  obtain ⟨p3, vm, hmonth, hgo⟩ := go_step_modifier config .any _ _ _ p2 out zt
    (fun r b h => parseWithDate_dateFields_preserves _ config _ p2 r b
      (Or.inr (Or.inl rfl)) h) hgo
  obtain ⟨month, rest3, hmfd, hm, hmval, hmsuf, hmsp⟩ :=
    parseWith_month_inv_at p2 p3 (year ++ "-") rest2 config vm hsepsp hmonth
  obtain ⟨p4, om, hsep2, hgo⟩ := go_step_string config .any _ "-" _ p3 out zt hgo
  obtain ⟨rest4, _, hsep2suf, hsep2sp⟩ :=
    pstring_inv_at p3 p4 (year ++ "-" ++ month) rest3 "-" om hmsp hsep2
  obtain ⟨p5, vd, hday, hgo⟩ := go_step_modifier config .any _ _ _ p4 out zt
    (fun r b h => parseWithDate_dateFields_preserves _ config _ p4 r b
      (Or.inr (Or.inr (Or.inl rfl))) h) hgo
  obtain ⟨day, rest5, hdfd, hd, hdval, hdsuf, hdsp⟩ :=
    parseWith_day_inv_at p4 p5 (year ++ "-" ++ month ++ "-") rest4 config vd hsep2sp hday
  obtain ⟨p6, oT, hsepT, hgo⟩ := go_step_string config .any _ "T" _ p5 out zt hgo
  obtain ⟨rest6, _, hTsuf, hTsp⟩ :=
    pstring_inv_at p5 p6 (year ++ "-" ++ month ++ "-" ++ day) rest5 "T" oT hdsp hsepT
  obtain ⟨p7, H, hhour, hgo⟩ := go_step_modifier config .any _ _ _ p6 out zt
    (fun r b h => parseWithDate_hour_preserves _ config p6 r b h) hgo
  obtain ⟨hh, rest7, hhfd, hhbound, hhsuf, hhsp⟩ :=
    parseWith_hour_inv_at p6 p7 (year ++ "-" ++ month ++ "-" ++ day ++ "T")
      rest6 config H hTsp hhour
  obtain ⟨p8, oc, hsepC, hgo⟩ := go_step_string config .any _ ":" _ p7 out zt hgo
  obtain ⟨rest8, _, hCsuf, hCsp⟩ :=
    pstring_inv_at p7 p8 (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh)
      rest7 ":" oc hhsp hsepC
  obtain ⟨p9, m, hminute, hgo⟩ := go_step_modifier config .any _ _ _ p8 out zt
    (fun r b h => parseWithDate_minute_preserves _ config p8 r b h) hgo
  obtain ⟨mm, rest9, hmmfd, hmmbound, hmmsuf, hmmsp⟩ :=
    parseWith_minute_inv_at p8 p9
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":")
      rest8 config m hCsp hminute
  obtain ⟨p10, oc2, hsepC2, hgo⟩ := go_step_string config .any _ ":" _ p9 out zt hgo
  obtain ⟨rest10, _, hC2suf, hC2sp⟩ :=
    pstring_inv_at p9 p10
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm)
      rest9 ":" oc2 hmmsp hsepC2
  obtain ⟨p11, sec, hsecond, hgo⟩ := go_step_modifier config .any _ _ _ p10 out zt
    (fun r b h => parseWithDate_second_preserves _ config hcfg p10 r b h) hgo
  obtain ⟨ss, rest11, hssfd, hssbound, hsssuf, hsssp⟩ :=
    parseWith_second_inv_at p10 p11
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":")
      rest10 config hcfg sec hC2sp hsecond
  have hstr : s =
      year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss ++ rest11 := by
    rw [hysuf, hsepsuf, hmsuf, hsep2suf, hdsuf, hTsuf, hhsuf, hCsuf, hmmsuf,
      hC2suf, hsssuf]
    simp only [String.append_assoc]
  subst hyval
  have hvm : vm = Bounded.LE.ofNat' (fieldValue month) hm :=
    Subtype.ext (by rw [hmval]; rfl)
  have hvd : vd = Bounded.LE.ofNat' (fieldValue day) hd :=
    Subtype.ext (by rw [hdval]; rfl)
  subst hvm
  subst hvd
  exact ⟨year, month, day, hh, mm, ss, rest11, hm, hd, H, m, sec, p11,
    hyfd, hmfd, hdfd, hhfd, hmmfd, hssfd, hhbound, hmmbound, hssbound,
    hstr, hsssp, hgo⟩

/-! ## Phase 2: DateUTC full parse inversion -/

open Std.Time.GenericFormat in
/-- **DateUTC full parse inversion.** If the DateUTC format's `parser.go` succeeds from the empty
    builder over the whole string `s`, ending at `endPos` with value `zt`, then `s` decomposes as the
    rendering of a well-formed UTC datetime, and `build` succeeds on the corresponding filled builder
    (whose time fields are the parsed hour/minute/second values). -/
theorem dateUTC_full_inv {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .string "Z"]
        ⟨s, s.startPos⟩ = ParseResult.success ⟨s, s.endPos⟩ zt) :
    ∃ (year month day hh mm ss : String)
      (hm : 1 ≤ fieldValue month ∧ fieldValue month ≤ 12)
      (hd : 1 ≤ fieldValue day ∧ fieldValue day ≤ 31),
      IsFixedDigits 4 year ∧ IsFixedDigits 2 month ∧ IsFixedDigits 2 day ∧
      IsFixedDigits 2 hh ∧ IsFixedDigits 2 mm ∧ IsFixedDigits 2 ss ∧
      fieldValue hh ≤ 23 ∧ fieldValue mm ≤ 59 ∧ fieldValue ss ≤ 59 ∧
      s = year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss ++ "Z" ∧
      ∃ (H : Hour.Ordinal) (m : Minute.Ordinal) (sec : Second.Ordinal true),
        ({ ({} : DateBuilder) with
                y := some (Int.ofNat (fieldValue year)),
                M := some (Bounded.LE.ofNat' (fieldValue month) hm),
                d := some (Bounded.LE.ofNat' (fieldValue day) hd),
                H := some H, m := some m, s := some sec }).build .any = some zt := by
  obtain ⟨year, month, day, hh, mm, ss, rest, hm, hd, H, m, sec, p,
      hyfd, hmfd, hdfd, hhfd, hmmfd, hssfd, hhbound, hmmbound, hssbound,
      hprefix, hsp, hgo⟩ :=
    datetimePrefix_inv config hcfg [.string "Z"] ⟨s, s.endPos⟩ zt hgo
  obtain ⟨p12, oZ, hZ, hgo⟩ := go_step_string config .any _ "Z" _ p _ zt hgo
  obtain ⟨rest12, _, hZsuf, hZsp⟩ :=
    pstring_inv_at p p12
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss)
      rest "Z" oZ hsp hZ
  obtain ⟨hbuild, hp12⟩ := go_nil_inv config _ p12 s.endPos zt hgo
  have hrest12 : rest12 = "" := by
    rw [hp12] at hZsp
    exact hZsp.eq_endPos_iff.mp rfl
  subst hrest12
  rw [String.append_empty] at hZsuf
  have hstr : s =
      year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss ++ "Z" := by
    rw [hprefix, hZsuf]
  exact ⟨year, month, day, hh, mm, ss, hm, hd, hyfd, hmfd, hdfd,
    hhfd, hmmfd, hssfd, hhbound, hmmbound, hssbound, hstr, H, m, sec, hbuild⟩

/-! ## Phase 3: build inversion, parse-ok inversion, and wf assembly -/

open Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **`build` inversion (DateUTC).** If the DateUTC builder (with `y`/`M`/`d` set from
    nonnegative year/month/day and `H`/`m`/`s` set to arbitrary time values) `build`s successfully,
    then the day satisfies the grammar bound `day ≤ daysInMonth year month`. The time fields do not
    enter the `Year.Offset.Valid` guard, so this mirrors `build_dateOnly_inv`. -/
theorem build_dateUTC_inv {yr mo dy : Nat} (H : Hour.Ordinal) (m : Minute.Ordinal)
    (sec : Second.Ordinal true)
    (hm : 1 ≤ mo ∧ mo ≤ 12) (hd : 1 ≤ dy ∧ dy ≤ 31)
    (zt : Std.Time.ZonedDateTime)
    (hbuild : ({ ({} : DateBuilder) with
        y := some (Int.ofNat yr),
        M := some (Bounded.LE.ofNat' mo hm),
        d := some (Bounded.LE.ofNat' dy hd),
        H := some H, m := some m, s := some sec }).build .any = some zt) :
    dy ≤ daysInMonth yr mo :=
  build_datetime_inv (some H) (some m) (some sec) none none hm hd zt hbuild

-- Thread the eleven format parts shared by every time-bearing datetime parser.
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
theorem datetimePrefix_go {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (p : s.Pos) (rem : ParseIt)
    (zt : Std.Time.ZonedDateTime) (tail : FormatString)
    (hgo : parser.go config .any {}
      ([.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
        .string "-", .modifier (.d {padding := 2}), .string "T",
        .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
        .string ":", .modifier (.s {padding := 2})] ++ tail)
      ⟨s, p⟩ = ParseResult.success rem zt) :
    ∃ (p' : s.Pos) (b : DateBuilder),
      parser.go config .any b tail ⟨s, p'⟩ = ParseResult.success rem zt := by
  obtain ⟨p1, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p _ zt
    (fun r b' h => parseWithDate_dateFields_preserves _ config _ p r b' (Or.inl rfl) h) hgo
  obtain ⟨p2, _, _, hgo⟩ := go_step_string config .any _ "-" _ p1 _ zt hgo
  obtain ⟨p3, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p2 _ zt
    (fun r b' h => parseWithDate_dateFields_preserves _ config _ p2 r b'
      (Or.inr (Or.inl rfl)) h) hgo
  obtain ⟨p4, _, _, hgo⟩ := go_step_string config .any _ "-" _ p3 _ zt hgo
  obtain ⟨p5, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p4 _ zt
    (fun r b' h => parseWithDate_dateFields_preserves _ config _ p4 r b'
      (Or.inr (Or.inr (Or.inl rfl))) h) hgo
  obtain ⟨p6, _, _, hgo⟩ := go_step_string config .any _ "T" _ p5 _ zt hgo
  obtain ⟨p7, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p6 _ zt
    (fun r b' h => parseWithDate_hour_preserves _ config p6 r b' h) hgo
  obtain ⟨p8, _, _, hgo⟩ := go_step_string config .any _ ":" _ p7 _ zt hgo
  obtain ⟨p9, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p8 _ zt
    (fun r b' h => parseWithDate_minute_preserves _ config p8 r b' h) hgo
  obtain ⟨p10, _, _, hgo⟩ := go_step_string config .any _ ":" _ p9 _ zt hgo
  obtain ⟨p11, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p10 _ zt
    (fun r b' h => parseWithDate_second_preserves _ config hcfg p10 r b' h) hgo
  exact ⟨p11, _, hgo⟩

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- The DateUTC `parser.go` preserves the string component of the iterator on success. -/
theorem dateUTC_go_preserves {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (p : s.Pos) (rem : ParseIt)
    (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .string "Z"]
        ⟨s, p⟩ = ParseResult.success rem zt) : rem.1 = s := by
  obtain ⟨p11, b, hgo⟩ := datetimePrefix_go config hcfg p rem zt [.string "Z"] hgo
  obtain ⟨p12, _, _, hgo⟩ := go_step_string config .any _ "Z" _ p11 _ zt hgo
  exact go_nil_preserves config b p12 rem zt hgo

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- **DateUTC `parse` success-inversion.** If `DateUTC.parse str = .ok zt`, the inner `parser.go`
    succeeded consuming the whole string (ending at `endPos`). -/
theorem dateUTC_parse_ok_inv (str : String) (zt : Std.Time.ZonedDateTime)
    (h : DateUTC.parse str = .ok zt) :
    parser.go DateUTC.config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .string "Z"]
        ⟨str, str.startPos⟩ = ParseResult.success ⟨str, str.endPos⟩ zt :=
  parse_ok_inv_of_preserves DateUTC str zt _ rfl
    (fun rem a hp => dateUTC_go_preserves DateUTC.config rfl str.startPos rem a hp) h

open Cedar.Spec.Ext.Datetime in
/-- **DateUTC case of `wf_of_parse`.** If `DateUTC.parse str = .ok zt`, then `str` is the rendering
    of a fully well-formed UTC-form `DatetimeComponents`. -/
theorem dateUTC_wf_inv (str : String) (zt : Std.Time.ZonedDateTime)
    (h : DateUTC.parse str = .ok zt) :
    ∃ c : DatetimeComponents, str = c.asString ∧ c.syntaxWf ∧ c.constraintsWf := by
  have hgo := dateUTC_parse_ok_inv str zt h
  obtain ⟨year, month, day, hh, mm, ss, hm, hd, hyfd, hmfd, hdfd, hhfd, hmmfd, hssfd,
      hhbound, hmmbound, hssbound, hstr, H, m, sec, hbuild⟩ :=
    dateUTC_full_inv DateUTC.config rfl zt hgo
  have hdayle : fieldValue day ≤ daysInMonth (fieldValue year) (fieldValue month) :=
    build_dateUTC_inv H m sec hm hd zt hbuild
  refine ⟨{ date := { year, month, day },
            time := some ⟨⟨hh, mm, ss⟩, none, Zone.utc⟩ }, ?_, ?_, ?_⟩
  · show str = ({ year, month, day } : DateComponents).asString
        ++ ("T" ++ (⟨hh, mm, ss⟩ : TimeComponents).asString
            ++ (match (none : Option String) with | none => "" | some sss => "." ++ sss)
            ++ Zone.utc.asString)
    show str = year ++ "-" ++ month ++ "-" ++ day
        ++ ("T" ++ (hh ++ ":" ++ mm ++ ":" ++ ss) ++ "" ++ "Z")
    rw [hstr]; simp only [String.append_assoc, String.append_empty]
  · exact ⟨⟨hyfd, hmfd, hdfd⟩, ⟨hhfd, hmmfd, hssfd⟩, trivial, trivial⟩
  · exact ⟨⟨hm.1, hm.2, hd.1, hdayle⟩, ⟨hhbound, hmmbound, hssbound⟩, trivial⟩

#print axioms dateUTC_wf_inv

/-- `parseWithDate` on the `.S (.truncated 3)` fraction modifier preserves the string component. -/
theorem parseWithDate_fraction_preserves {s : String} (b : DateBuilder) (config : FormatConfig)
    (p : s.Pos) (rem : ParseIt) (b' : DateBuilder)
    (hpar : parseWithDate b config (.modifier (.S (.truncated 3))) ⟨s, p⟩
        = ParseResult.success rem b') : rem.1 = s := by
  rw [parseWithDate_modifier_app] at hpar
  cases hS : parseWith config (.S (.truncated 3)) ⟨s, p⟩ with
  | error pos msg => rw [hS] at hpar; simp at hpar
  | success rem' v =>
    rw [hS] at hpar
    replace hpar : ParseResult.success rem' (b.insert (.S (.truncated 3)) v)
      = ParseResult.success rem b' := hpar
    injection hpar with hit _; rw [← hit]
    -- preserve via the fraction parser core
    rw [show parseWith config (.S (.truncated 3))
          = (parseNatToBounded (parseFractionNum 3 9) : Parser (Bounded.LE 0 999999999)) from rfl]
      at hS
    unfold parseNatToBounded parseFractionNum at hS
    simp only [bind, Bind.bind] at hS
    rw [parsec_bind_app] at hS
    cases hinner : (String.toNat! <$> rightPadAscii 9 '0' <$> exactlyChars (satisfy Char.isDigit) 3)
        ⟨s, p⟩ with
    | error pos msg => rw [hinner] at hS; simp at hS
    | success reminner w =>
      rw [hinner] at hS
      obtain ⟨sr, pr⟩ := reminner
      replace hS : (if h : 0 ≤ w ∧ w ≤ 999999999 then
            (pure (Bounded.LE.ofNat' w h) : Parser (Bounded.LE 0 999999999))
          else fail s!"need a natural number in the interval of {0} to {999999999}") ⟨sr, pr⟩
          = ParseResult.success rem' v := hS
      have hsr : sr = s := by
        rw [parsec_map_app, parsec_map_app] at hinner
        cases hec : exactlyChars (satisfy Char.isDigit) 3 ⟨s, p⟩ with
        | error pos msg => rw [hec] at hinner; simp at hinner
        | success rem2 out =>
          rw [hec] at hinner
          obtain ⟨s2, p2⟩ := rem2
          simp only [ParseResult.success.injEq, Sigma.mk.injEq] at hinner
          obtain ⟨⟨hs2, _⟩, _⟩ := hinner
          rw [← hs2]; exact exactlyChars_go_preserves 3 0 "" p ⟨s2, p2⟩ out hec
      subst hsr
      by_cases hb : 0 ≤ w ∧ w ≤ 999999999
      · rw [dif_pos hb] at hS
        replace hS : ParseResult.success (⟨sr, pr⟩ : ParseIt) (Bounded.LE.ofNat' w hb)
          = ParseResult.success rem' v := hS
        injection hS with hit2 _; rw [← hit2]
      · rw [dif_neg hb, Std.Internal.Parsec.fail] at hS; simp at hS

open Std.Time.GenericFormat in
/-- **DateUTCWithMillis full parse inversion.** -/
theorem dateUTCWithMillis_full_inv {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .string ".",
         .modifier (.S (.truncated 3)), .string "Z"]
        ⟨s, s.startPos⟩ = ParseResult.success ⟨s, s.endPos⟩ zt) :
    ∃ (year month day hh mm ss sss : String)
      (hm : 1 ≤ fieldValue month ∧ fieldValue month ≤ 12)
      (hd : 1 ≤ fieldValue day ∧ fieldValue day ≤ 31),
      IsFixedDigits 4 year ∧ IsFixedDigits 2 month ∧ IsFixedDigits 2 day ∧
      IsFixedDigits 2 hh ∧ IsFixedDigits 2 mm ∧ IsFixedDigits 2 ss ∧ IsFixedDigits 3 sss ∧
      fieldValue hh ≤ 23 ∧ fieldValue mm ≤ 59 ∧ fieldValue ss ≤ 59 ∧
      s = year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss
          ++ "." ++ sss ++ "Z" ∧
      ∃ (H : Hour.Ordinal) (m : Minute.Ordinal) (sec : Second.Ordinal true)
        (S : Nanosecond.Ordinal),
        ({ ({} : DateBuilder) with
                y := some (Int.ofNat (fieldValue year)),
                M := some (Bounded.LE.ofNat' (fieldValue month) hm),
                d := some (Bounded.LE.ofNat' (fieldValue day) hd),
                H := some H, m := some m, s := some sec, S := some S }).build .any = some zt := by
  obtain ⟨year, month, day, hh, mm, ss, rest, hm, hd, H, m, sec, p,
      hyfd, hmfd, hdfd, hhfd, hmmfd, hssfd, hhbound, hmmbound, hssbound,
      hprefix, hsp, hgo⟩ :=
    datetimePrefix_inv config hcfg
      [.string ".", .modifier (.S (.truncated 3)), .string "Z"]
      ⟨s, s.endPos⟩ zt hgo
  obtain ⟨p12, oD, hD, hgo⟩ := go_step_string config .any _ "." _ p _ zt hgo
  obtain ⟨rest12, _, hDsuf, hDsp⟩ :=
    pstring_inv_at p p12
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss)
      rest "." oD hsp hD
  obtain ⟨p13, S, hS, hgo⟩ := go_step_modifier config .any _ _ _ p12 _ zt
    (fun r b h => parseWithDate_fraction_preserves _ config p12 r b h) hgo
  obtain ⟨sss, rest13, hsssfd, hSsuf, hSsp⟩ :=
    parseWith_fraction_inv_at p12 p13
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss ++ ".")
      rest12 config S hDsp hS
  obtain ⟨p14, oZ, hZ, hgo⟩ := go_step_string config .any _ "Z" _ p13 _ zt hgo
  obtain ⟨rest14, _, hZsuf, hZsp⟩ :=
    pstring_inv_at p13 p14
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss
        ++ "." ++ sss)
      rest13 "Z" oZ hSsp hZ
  obtain ⟨hbuild, hp14⟩ := go_nil_inv config _ p14 s.endPos zt hgo
  have hrest14 : rest14 = "" := by
    rw [hp14] at hZsp
    exact hZsp.eq_endPos_iff.mp rfl
  subst hrest14
  rw [String.append_empty] at hZsuf
  have hstr : s = year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":"
      ++ ss ++ "." ++ sss ++ "Z" := by
    rw [hprefix, hDsuf, hSsuf, hZsuf]
    simp only [String.append_assoc]
  exact ⟨year, month, day, hh, mm, ss, sss, hm, hd, hyfd, hmfd, hdfd,
    hhfd, hmmfd, hssfd, hsssfd, hhbound, hmmbound, hssbound, hstr,
    H, m, sec, S, hbuild⟩

open Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **`build` inversion (DateUTCWithMillis).** Same as `build_dateUTC_inv` plus the nano field;
    the fractional-seconds field does not enter the `Year.Offset.Valid` guard. -/
theorem build_dateUTCWithMillis_inv {yr mo dy : Nat} (H : Hour.Ordinal) (m : Minute.Ordinal)
    (sec : Second.Ordinal true) (S : Nanosecond.Ordinal)
    (hm : 1 ≤ mo ∧ mo ≤ 12) (hd : 1 ≤ dy ∧ dy ≤ 31)
    (zt : Std.Time.ZonedDateTime)
    (hbuild : ({ ({} : DateBuilder) with
        y := some (Int.ofNat yr),
        M := some (Bounded.LE.ofNat' mo hm),
        d := some (Bounded.LE.ofNat' dy hd),
        H := some H, m := some m, s := some sec, S := some S }).build .any = some zt) :
    dy ≤ daysInMonth yr mo :=
  build_datetime_inv (some H) (some m) (some sec) (some S) none hm hd zt hbuild

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- The DateUTCWithMillis `parser.go` preserves the string component of the iterator on success. -/
theorem dateUTCWithMillis_go_preserves {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (p : s.Pos) (rem : ParseIt)
    (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .string ".",
         .modifier (.S (.truncated 3)), .string "Z"]
        ⟨s, p⟩ = ParseResult.success rem zt) : rem.1 = s := by
  obtain ⟨p11, _, hgo⟩ := datetimePrefix_go config hcfg p rem zt
    [.string ".", .modifier (.S (.truncated 3)), .string "Z"] hgo
  obtain ⟨p12, _, _, hgo⟩ := go_step_string config .any _ "." _ p11 _ zt hgo
  obtain ⟨p13, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p12 _ zt
    (fun r b' h => parseWithDate_fraction_preserves _ config p12 r b' h) hgo
  obtain ⟨p14, _, _, hgo⟩ := go_step_string config .any _ "Z" _ p13 _ zt hgo
  exact go_nil_preserves config _ p14 rem zt hgo

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- **DateUTCWithMillis `parse` success-inversion.** -/
theorem dateUTCWithMillis_parse_ok_inv (str : String) (zt : Std.Time.ZonedDateTime)
    (h : DateUTCWithMillis.parse str = .ok zt) :
    parser.go DateUTCWithMillis.config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .string ".",
         .modifier (.S (.truncated 3)), .string "Z"]
        ⟨str, str.startPos⟩ = ParseResult.success ⟨str, str.endPos⟩ zt :=
  parse_ok_inv_of_preserves DateUTCWithMillis str zt _ rfl
    (fun rem a hp =>
      dateUTCWithMillis_go_preserves DateUTCWithMillis.config rfl str.startPos rem a hp) h

open Cedar.Spec.Ext.Datetime in
/-- **DateUTCWithMillis case of `wf_of_parse`.** -/
theorem dateUTCWithMillis_wf_inv (str : String) (zt : Std.Time.ZonedDateTime)
    (h : DateUTCWithMillis.parse str = .ok zt) :
    ∃ c : DatetimeComponents, str = c.asString ∧ c.syntaxWf ∧ c.constraintsWf := by
  have hgo := dateUTCWithMillis_parse_ok_inv str zt h
  obtain ⟨year, month, day, hh, mm, ss, sss, hm, hd, hyfd, hmfd, hdfd, hhfd, hmmfd, hssfd, hsssfd,
      hhbound, hmmbound, hssbound, hstr, H, m, sec, S, hbuild⟩ :=
    dateUTCWithMillis_full_inv DateUTCWithMillis.config rfl zt hgo
  have hdayle : fieldValue day ≤ daysInMonth (fieldValue year) (fieldValue month) :=
    build_dateUTCWithMillis_inv H m sec S hm hd zt hbuild
  refine ⟨{ date := { year, month, day },
            time := some ⟨⟨hh, mm, ss⟩, some sss, Zone.utc⟩ }, ?_, ?_, ?_⟩
  · show str = ({ year, month, day } : DateComponents).asString
        ++ ("T" ++ (⟨hh, mm, ss⟩ : TimeComponents).asString
            ++ (match (some sss : Option String) with | none => "" | some sss => "." ++ sss)
            ++ Zone.utc.asString)
    show str = year ++ "-" ++ month ++ "-" ++ day
        ++ ("T" ++ (hh ++ ":" ++ mm ++ ":" ++ ss) ++ ("." ++ sss) ++ "Z")
    rw [hstr]; simp only [String.append_assoc]
  · exact ⟨⟨hyfd, hmfd, hdfd⟩, ⟨hhfd, hmmfd, hssfd⟩, hsssfd, trivial⟩
  · exact ⟨⟨hm.1, hm.2, hd.1, hdayle⟩, ⟨hhbound, hmmbound, hssbound⟩, trivial⟩

#print axioms dateUTCWithMillis_wf_inv

/-! ## Phase 3: DateWithOffset (the `±hhmm` offset tail) -/

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- `pchar` preserves the string component on success. -/
theorem pchar_preserves {s : String} (c : Char) (p : s.Pos) (rem : ParseIt) (out : Char)
    (hpar : pchar c ⟨s, p⟩ = ParseResult.success rem out) : rem.1 = s := by
  rw [pchar_eq] at hpar
  by_cases hn : Input.hasNext (⟨s, p⟩ : ParseIt) = true
  · simp only [hn, dif_pos] at hpar
    by_cases hc : Input.curr' (⟨s, p⟩ : ParseIt) hn = c
    · rw [next'_eq] at hpar
      simp only [hc, if_pos] at hpar
      injection hpar with hit _
      obtain ⟨sr, pr⟩ := rem; simp only [Sigma.mk.injEq] at hit
      exact hit.1.symm
    · simp only [hc, if_neg, not_false_iff] at hpar; simp at hpar
  · simp only [hn] at hpar; simp at hpar

open Std.Internal.Parsec Std.Internal.Parsec.String in
/-- The sign alternation preserves the string component on success. -/
theorem sign_preserves {s : String} (p : s.Pos) (rem : ParseIt) (a : Int)
    (hpar : ((pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1)) : Parser Int) ⟨s, p⟩
        = ParseResult.success rem a) : rem.1 = s := by
  cases hplus : pchar '+' (⟨s, p⟩ : ParseIt) with
  | success remp cp =>
    have hremp : remp.1 = s := pchar_preserves '+' p remp cp hplus
    have hsign : ((pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1)) : Parser Int) ⟨s, p⟩
        = ParseResult.success remp 1 := by
      rw [orElse_app, seqRight_app, hplus]; rfl
    rw [hsign] at hpar; injection hpar with hit _; rw [← hit]; exact hremp
  | error remp errp =>
    have hpos : remp = (⟨s, p⟩ : ParseIt) := by
      rw [pchar_eq] at hplus
      by_cases hn : Input.hasNext (⟨s, p⟩ : ParseIt) = true
      · simp only [hn, dif_pos] at hplus
        by_cases hc : Input.curr' (⟨s, p⟩ : ParseIt) hn = '+'
        · simp only [hc, if_pos] at hplus; simp at hplus
        · simp only [hc, if_neg, not_false_iff] at hplus; injection hplus with h1 _; exact h1.symm
      · simp only [hn] at hplus; injection hplus with h1 _; exact h1.symm
    subst hpos
    rw [orElse_app, seqRight_app, hplus] at hpar
    simp only [Input.pos, ↓reduceIte] at hpar
    rw [seqRight_app] at hpar
    cases hminus : pchar '-' (⟨s, p⟩ : ParseIt) with
    | error pos msg => rw [hminus] at hpar; simp at hpar
    | success remm cm =>
      rw [hminus] at hpar
      replace hpar : ParseResult.success remm (-1 : Int) = ParseResult.success rem a := hpar
      injection hpar with hit _; rw [← hit]
      exact pchar_preserves '-' p remm cm hminus

set_option backward.isDefEq.respectTransparency false in
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWith config (.x .hourMinute)` preserves the string component on success. -/
theorem parseWith_offset_preserves {s : String} (config : FormatConfig) (p : s.Pos)
    (rem : ParseIt) (v : Std.Time.TimeZone.Offset)
    (hpar : parseWith config (.x .hourMinute) ⟨s, p⟩ = ParseResult.success rem v) : rem.1 = s := by
  rw [show parseWith config (.x .hourMinute) = Std.Time.parseOffset .yes .no false from rfl] at hpar
  unfold Std.Time.parseOffset at hpar
  simp only [bind, Bind.bind] at hpar
  rw [parsec_bind_app] at hpar
  cases hsign : ((pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1)) : Parser Int) ⟨s, p⟩ with
  | error pos msg => rw [hsign] at hpar; simp at hpar
  | success rem1 a1 =>
    rw [hsign] at hpar
    obtain ⟨s1, p1⟩ := rem1
    have hs1 : s1 = s := sign_preserves p ⟨s1, p1⟩ a1 hsign
    subst s1
    simp only [] at hpar
    rw [parsec_bind_app] at hpar
    split at hpar
    case h_2 pos msg heq => simp at hpar
    case h_1 rem2 vhoff heq =>
      rw [parsec_map_app, parsec_bind_app] at heq
      cases hph : parseOneOrTwoNum (⟨s, p1⟩ : ParseIt) with
      | error pos msg => rw [hph] at heq; simp at heq
      | success rem2' vh =>
        rw [hph] at heq
        obtain ⟨s2, p2⟩ := rem2'
        have hs2 : s2 = s := parseOneOrTwoNum_preserves p1 ⟨s2, p2⟩ vh hph
        subst s2
        replace heq : ParseResult.success (⟨s, p2⟩ : ParseIt) (UnitVal.ofInt (vh : Int))
            = ParseResult.success rem2 vhoff := heq
        injection heq with hit hvoff; subst rem2; subst vhoff
        simp only [] at hpar
        by_cases hg : ((vh : Int) < 0 ∨ (vh : Int) > 23)
        · rw [if_pos hg] at hpar
          simp [Std.Internal.Parsec.fail, Std.Internal.Parsec.bind] at hpar
        · rw [if_neg hg] at hpar
          rw [parsec_bind_app] at hpar
          split at hpar
          case h_2 pos msg heqm => simp at hpar
          case h_1 rem3 vmopt heqm =>
            simp only [Bool.false_eq_true, if_false, parsec_map_app, seqRight_app] at heqm
            rw [show (Pure.pure ':' : Parser Char) (⟨s, p2⟩ : ParseIt)
                = ParseResult.success (⟨s, p2⟩ : ParseIt) ':' from rfl] at heqm
            simp only [] at heqm
            rw [parsec_bind_app] at heqm
            cases hpm : parseOneOrTwoNum (⟨s, p2⟩ : ParseIt) with
            | error pos msg => rw [hpm] at heqm; simp at heqm
            | success rem3' vm =>
              rw [hpm] at heqm
              obtain ⟨s3, p3⟩ := rem3'
              have hs3 : s3 = s := parseOneOrTwoNum_preserves p2 ⟨s3, p3⟩ vm hpm
              subst s3
              replace heqm : ParseResult.success (⟨s, p3⟩ : ParseIt)
                  (some (UnitVal.ofInt (vm : Int))) = ParseResult.success rem3 vmopt := heqm
              injection heqm with hit hvmopt; subst rem3; subst vmopt
              simp only [] at hpar
              by_cases hgm : ((vm : Int) > 59)
              · rw [if_pos hgm] at hpar
                simp [Std.Internal.Parsec.fail, Std.Internal.Parsec.bind] at hpar
              · rw [if_neg hgm] at hpar
                replace hpar : ParseResult.success (⟨s, p3⟩ : ParseIt) _
                    = ParseResult.success rem v := hpar
                injection hpar with hit _; rw [← hit]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time in
/-- `parseWithDate` on the `.x .hourMinute` offset modifier preserves the string component. -/
theorem parseWithDate_offset_preserves {s : String} (b : DateBuilder) (config : FormatConfig)
    (p : s.Pos) (rem : ParseIt) (b' : DateBuilder)
    (hpar : parseWithDate b config (.modifier (.x .hourMinute)) ⟨s, p⟩
        = ParseResult.success rem b') : rem.1 = s := by
  rw [parseWithDate_modifier_app] at hpar
  cases hX : parseWith config (.x .hourMinute) ⟨s, p⟩ with
  | error pos msg => rw [hX] at hpar; simp at hpar
  | success rem' v =>
    rw [hX] at hpar
    replace hpar : ParseResult.success rem' (b.insert (.x .hourMinute) v)
      = ParseResult.success rem b' := hpar
    injection hpar with hit _; rw [← hit]
    exact parseWith_offset_preserves config p rem' v hX

open Std.Time.GenericFormat in
/-- **DateWithOffset full parse inversion.** Like `dateUTC_full_inv`, but the tail is an explicit
    `±hhmm` offset (`.x .hourMinute`) rather than the `'Z'` marker. -/
theorem dateWithOffset_full_inv {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (hlen : checkOffsetLen s = true)
    (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .modifier (.x .hourMinute)]
        ⟨s, s.startPos⟩ = ParseResult.success ⟨s, s.endPos⟩ zt) :
    ∃ (year month day hh mm ss : String) (neg : Bool) (ohh omm : String)
      (hm : 1 ≤ fieldValue month ∧ fieldValue month ≤ 12)
      (hd : 1 ≤ fieldValue day ∧ fieldValue day ≤ 31),
      IsFixedDigits 4 year ∧ IsFixedDigits 2 month ∧ IsFixedDigits 2 day ∧
      IsFixedDigits 2 hh ∧ IsFixedDigits 2 mm ∧ IsFixedDigits 2 ss ∧
      IsFixedDigits 2 ohh ∧ IsFixedDigits 2 omm ∧
      fieldValue hh ≤ 23 ∧ fieldValue mm ≤ 59 ∧ fieldValue ss ≤ 59 ∧
      fieldValue ohh ≤ 23 ∧ fieldValue omm ≤ 59 ∧
      s = year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss
          ++ ((if neg then "-" else "+") ++ ohh ++ omm) ∧
      ∃ (H : Hour.Ordinal) (m : Minute.Ordinal) (sec : Second.Ordinal true)
        (off : Std.Time.TimeZone.Offset),
        ({ ({} : DateBuilder) with
                y := some (Int.ofNat (fieldValue year)),
                M := some (Bounded.LE.ofNat' (fieldValue month) hm),
                d := some (Bounded.LE.ofNat' (fieldValue day) hd),
                H := some H, m := some m, s := some sec, x := some off }).build .any = some zt := by
  obtain ⟨year, month, day, hh, mm, ss, rest, hm, hd, H, m, sec, p,
      hyfd, hmfd, hdfd, hhfd, hmmfd, hssfd, hhbound, hmmbound, hssbound,
      hprefix, hsp, hgo⟩ :=
    datetimePrefix_inv config hcfg [.modifier (.x .hourMinute)] ⟨s, s.endPos⟩ zt hgo
  obtain ⟨p12, off, hX, hgo⟩ := go_step_modifier config .any _ _ _ p _ zt
    (fun r b h => parseWithDate_offset_preserves _ config p r b h) hgo
  obtain ⟨neg, ohh, omm, rest12, hohdig, hommdig, hohb, hommb, hXsuf, hXsp⟩ :=
    parseWith_offset_inv_at p p12
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss)
      rest config off hsp hX
  obtain ⟨hbuild, hp12⟩ := go_nil_inv config _ p12 s.endPos zt hgo
  have hrest12 : rest12 = "" := by
    rw [hp12] at hXsp
    exact hXsp.eq_endPos_iff.mp rfl
  subst hrest12
  have hsg : String.singleton (if neg then '-' else '+') =
      (if neg then "-" else "+") := by
    cases neg <;> rfl
  have hstr : s = year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm
      ++ ":" ++ ss ++ ((if neg then "-" else "+") ++ ohh ++ omm) := by
    rw [hprefix, hXsuf, hsg]
    simp only [String.append_assoc, String.append_empty]
  have hdateT :
      ∀ ch ∈ (year ++ "-" ++ month ++ "-" ++ day).toList, (ch == 'T') = false := by
    simpa using three_fields_no_pred year month day '-' (· == 'T')
      (no_beq_of_isDigits hyfd.1 'T' (by decide))
      (no_beq_of_isDigits hmfd.1 'T' (by decide))
      (no_beq_of_isDigits hdfd.1 'T' (by decide)) (by decide)
  have htimeT :
      ∀ ch ∈ (hh ++ ":" ++ mm ++ ":" ++ ss).toList, (ch == 'T') = false := by
    simpa using three_fields_no_pred hh mm ss ':' (· == 'T')
      (no_beq_of_isDigits hhfd.1 'T' (by decide))
      (no_beq_of_isDigits hmmfd.1 'T' (by decide))
      (no_beq_of_isDigits hssfd.1 'T' (by decide)) (by decide)
  have htimeSign :
      ∀ ch ∈ (hh ++ ":" ++ mm ++ ":" ++ ss).toList,
        (ch == '+' || ch == '-') = false := by
    simpa using three_fields_no_pred hh mm ss ':' (fun c => c == '+' || c == '-')
      (no_sign_of_isDigits hhfd.1) (no_sign_of_isDigits hmmfd.1)
      (no_sign_of_isDigits hssfd.1) (by decide)
  have hcheck := hlen
  rw [hstr] at hcheck
  have hcheck' : checkOffsetLen
      ((year ++ "-" ++ month ++ "-" ++ day) ++ String.singleton 'T' ++
        (hh ++ ":" ++ mm ++ ":" ++ ss) ++
        String.singleton (if neg then '-' else '+') ++ ohh ++ omm) = true := by
    cases neg <;> simpa [String.append_assoc,
      show ("T" : String) = String.singleton 'T' from rfl,
      show ("+" : String) = String.singleton '+' from rfl,
      show ("-" : String) = String.singleton '-' from rfl] using hcheck
  obtain ⟨hohfd, hommfd⟩ :=
    checkOffsetLen_offset_fields neg hdateT htimeT htimeSign hohdig hommdig hcheck'
  exact ⟨year, month, day, hh, mm, ss, neg, ohh, omm, hm, hd, hyfd, hmfd,
    hdfd, hhfd, hmmfd, hssfd, hohfd, hommfd, hhbound, hmmbound, hssbound,
    hohb, hommb, hstr, H, m, sec, off, hbuild⟩

open Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **`build` inversion (DateWithOffset).** Same as `build_dateUTC_inv`; the offset only enters the
    zone construction, not the `Year.Offset.Valid` day guard. -/
theorem build_dateWithOffset_inv {yr mo dy : Nat} (H : Hour.Ordinal) (m : Minute.Ordinal)
    (sec : Second.Ordinal true) (off : Std.Time.TimeZone.Offset)
    (hm : 1 ≤ mo ∧ mo ≤ 12) (hd : 1 ≤ dy ∧ dy ≤ 31)
    (zt : Std.Time.ZonedDateTime)
    (hbuild : ({ ({} : DateBuilder) with
        y := some (Int.ofNat yr),
        M := some (Bounded.LE.ofNat' mo hm),
        d := some (Bounded.LE.ofNat' dy hd),
        H := some H, m := some m, s := some sec, x := some off }).build .any = some zt) :
    dy ≤ daysInMonth yr mo :=
  build_datetime_inv (some H) (some m) (some sec) none (some off) hm hd zt hbuild

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- The DateWithOffset `parser.go` preserves the string component of the iterator on success. -/
theorem dateWithOffset_go_preserves {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (p : s.Pos) (rem : ParseIt)
    (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .modifier (.x .hourMinute)]
        ⟨s, p⟩ = ParseResult.success rem zt) : rem.1 = s := by
  obtain ⟨p11, _, hgo⟩ := datetimePrefix_go config hcfg p rem zt
    [.modifier (.x .hourMinute)] hgo
  obtain ⟨p12, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p11 _ zt
    (fun r b' h => parseWithDate_offset_preserves _ config p11 r b' h) hgo
  exact go_nil_preserves config _ p12 rem zt hgo

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- **DateWithOffset `parse` success-inversion.** -/
theorem dateWithOffset_parse_ok_inv (str : String) (zt : Std.Time.ZonedDateTime)
    (h : DateWithOffset.parse str = .ok zt) :
    parser.go DateWithOffset.config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .modifier (.x .hourMinute)]
        ⟨str, str.startPos⟩ = ParseResult.success ⟨str, str.endPos⟩ zt :=
  parse_ok_inv_of_preserves DateWithOffset str zt _ rfl
    (fun rem a hp =>
      dateWithOffset_go_preserves DateWithOffset.config rfl str.startPos rem a hp) h

open Cedar.Spec.Ext.Datetime in
/-- **DateWithOffset case of `wf_of_parse`.** If `DateWithOffset.parse str = .ok zt`, then `str` is
    the rendering of fully well-formed components whose zone is an explicit `±hhmm` offset. -/
theorem dateWithOffset_wf_inv (str : String) (zt : Std.Time.ZonedDateTime)
    (hlen : checkOffsetLen str = true) (h : DateWithOffset.parse str = .ok zt) :
    ∃ c : DatetimeComponents, str = c.asString ∧ c.syntaxWf ∧ c.constraintsWf := by
  have hgo := dateWithOffset_parse_ok_inv str zt h
  obtain ⟨year, month, day, hh, mm, ss, neg, ohh, omm, hm, hd, hyfd, hmfd, hdfd, hhfd, hmmfd, hssfd,
      hohfd, hommfd, hhbound, hmmbound, hssbound, hohb, hommb, hstr, H, m, sec, off, hbuild⟩ :=
    dateWithOffset_full_inv DateWithOffset.config rfl hlen zt hgo
  have hdayle : fieldValue day ≤ daysInMonth (fieldValue year) (fieldValue month) :=
    build_dateWithOffset_inv H m sec off hm hd zt hbuild
  refine ⟨{ date := { year, month, day },
            time := some ⟨⟨hh, mm, ss⟩, none, Zone.offset ⟨neg, ohh, omm⟩⟩ }, ?_, ?_, ?_⟩
  · show str = ({ year, month, day } : DateComponents).asString
        ++ ("T" ++ (⟨hh, mm, ss⟩ : TimeComponents).asString
            ++ (match (none : Option String) with | none => "" | some sss => "." ++ sss)
            ++ (Zone.offset ⟨neg, ohh, omm⟩).asString)
    show str = year ++ "-" ++ month ++ "-" ++ day
        ++ ("T" ++ (hh ++ ":" ++ mm ++ ":" ++ ss) ++ ""
            ++ ((if neg then "-" else "+") ++ ohh ++ omm))
    rw [hstr]; simp only [String.append_assoc, String.append_empty]
  · exact ⟨⟨hyfd, hmfd, hdfd⟩, ⟨hhfd, hmmfd, hssfd⟩, trivial, hohfd, hommfd⟩
  · exact ⟨⟨hm.1, hm.2, hd.1, hdayle⟩, ⟨hhbound, hmmbound, hssbound⟩, hohb, hommb⟩

open Std.Time.GenericFormat in
/-- **DateWithOffsetAndMillis full parse inversion.** Hybrid of `dateUTCWithMillis_full_inv` (the
    fractional `.SSS` seconds) and `dateWithOffset_full_inv` (the `±hhmm` offset tail). -/
theorem dateWithOffsetAndMillis_full_inv {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (hlen : checkOffsetLen s = true)
    (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .string ".",
         .modifier (.S (.truncated 3)), .modifier (.x .hourMinute)]
        ⟨s, s.startPos⟩ = ParseResult.success ⟨s, s.endPos⟩ zt) :
    ∃ (year month day hh mm ss sss : String) (neg : Bool) (ohh omm : String)
      (hm : 1 ≤ fieldValue month ∧ fieldValue month ≤ 12)
      (hd : 1 ≤ fieldValue day ∧ fieldValue day ≤ 31),
      IsFixedDigits 4 year ∧ IsFixedDigits 2 month ∧ IsFixedDigits 2 day ∧
      IsFixedDigits 2 hh ∧ IsFixedDigits 2 mm ∧ IsFixedDigits 2 ss ∧ IsFixedDigits 3 sss ∧
      IsFixedDigits 2 ohh ∧ IsFixedDigits 2 omm ∧
      fieldValue hh ≤ 23 ∧ fieldValue mm ≤ 59 ∧ fieldValue ss ≤ 59 ∧
      fieldValue ohh ≤ 23 ∧ fieldValue omm ≤ 59 ∧
      s = year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss
          ++ "." ++ sss ++ ((if neg then "-" else "+") ++ ohh ++ omm) ∧
      ∃ (H : Hour.Ordinal) (m : Minute.Ordinal) (sec : Second.Ordinal true)
        (S : Nanosecond.Ordinal) (off : Std.Time.TimeZone.Offset),
        ({ ({} : DateBuilder) with
                y := some (Int.ofNat (fieldValue year)),
                M := some (Bounded.LE.ofNat' (fieldValue month) hm),
                d := some (Bounded.LE.ofNat' (fieldValue day) hd),
                H := some H, m := some m, s := some sec, S := some S,
                x := some off }).build .any = some zt := by
  obtain ⟨year, month, day, hh, mm, ss, rest, hm, hd, H, m, sec, p,
      hyfd, hmfd, hdfd, hhfd, hmmfd, hssfd, hhbound, hmmbound, hssbound,
      hprefix, hsp, hgo⟩ :=
    datetimePrefix_inv config hcfg
      [.string ".", .modifier (.S (.truncated 3)), .modifier (.x .hourMinute)]
      ⟨s, s.endPos⟩ zt hgo
  obtain ⟨p12, oD, hD, hgo⟩ := go_step_string config .any _ "." _ p _ zt hgo
  obtain ⟨rest12, _, hDsuf, hDsp⟩ :=
    pstring_inv_at p p12
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss)
      rest "." oD hsp hD
  obtain ⟨p13, S, hS, hgo⟩ := go_step_modifier config .any _ _ _ p12 _ zt
    (fun r b h => parseWithDate_fraction_preserves _ config p12 r b h) hgo
  obtain ⟨sss, rest13, hsssfd, hSsuf, hSsp⟩ :=
    parseWith_fraction_inv_at p12 p13
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss ++ ".")
      rest12 config S hDsp hS
  obtain ⟨p14, off, hX, hgo⟩ := go_step_modifier config .any _ _ _ p13 _ zt
    (fun r b h => parseWithDate_offset_preserves _ config p13 r b h) hgo
  obtain ⟨neg, ohh, omm, rest14, hohdig, hommdig, hohb, hommb, hXsuf, hXsp⟩ :=
    parseWith_offset_inv_at p13 p14
      (year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm ++ ":" ++ ss
        ++ "." ++ sss)
      rest13 config off hSsp hX
  obtain ⟨hbuild, hp14⟩ := go_nil_inv config _ p14 s.endPos zt hgo
  have hrest14 : rest14 = "" := by
    rw [hp14] at hXsp
    exact hXsp.eq_endPos_iff.mp rfl
  subst hrest14
  have hsg : String.singleton (if neg then '-' else '+') =
      (if neg then "-" else "+") := by
    cases neg <;> rfl
  have hstr : s = year ++ "-" ++ month ++ "-" ++ day ++ "T" ++ hh ++ ":" ++ mm
      ++ ":" ++ ss ++ "." ++ sss ++ ((if neg then "-" else "+") ++ ohh ++ omm) := by
    rw [hprefix, hDsuf, hSsuf, hXsuf, hsg]
    simp only [String.append_assoc, String.append_empty]
  have hdateT :
      ∀ ch ∈ (year ++ "-" ++ month ++ "-" ++ day).toList, (ch == 'T') = false := by
    simpa using three_fields_no_pred year month day '-' (· == 'T')
      (no_beq_of_isDigits hyfd.1 'T' (by decide))
      (no_beq_of_isDigits hmfd.1 'T' (by decide))
      (no_beq_of_isDigits hdfd.1 'T' (by decide)) (by decide)
  have hbaseTimeT :
      ∀ ch ∈ (hh ++ ":" ++ mm ++ ":" ++ ss).toList, (ch == 'T') = false := by
    simpa using three_fields_no_pred hh mm ss ':' (· == 'T')
      (no_beq_of_isDigits hhfd.1 'T' (by decide))
      (no_beq_of_isDigits hmmfd.1 'T' (by decide))
      (no_beq_of_isDigits hssfd.1 'T' (by decide)) (by decide)
  have htimeT :
      ∀ ch ∈ (hh ++ ":" ++ mm ++ ":" ++ ss ++ "." ++ sss).toList,
        (ch == 'T') = false := by
    simpa using append_sep_no_pred (hh ++ ":" ++ mm ++ ":" ++ ss) sss '.'
      (· == 'T') hbaseTimeT (no_beq_of_isDigits hsssfd.1 'T' (by decide)) (by decide)
  have hbaseTimeSign :
      ∀ ch ∈ (hh ++ ":" ++ mm ++ ":" ++ ss).toList,
        (ch == '+' || ch == '-') = false := by
    simpa using three_fields_no_pred hh mm ss ':' (fun c => c == '+' || c == '-')
      (no_sign_of_isDigits hhfd.1) (no_sign_of_isDigits hmmfd.1)
      (no_sign_of_isDigits hssfd.1) (by decide)
  have htimeSign :
      ∀ ch ∈ (hh ++ ":" ++ mm ++ ":" ++ ss ++ "." ++ sss).toList,
        (ch == '+' || ch == '-') = false := by
    simpa using append_sep_no_pred (hh ++ ":" ++ mm ++ ":" ++ ss) sss '.'
      (fun c => c == '+' || c == '-') hbaseTimeSign
      (no_sign_of_isDigits hsssfd.1) (by decide)
  have hcheck := hlen
  rw [hstr] at hcheck
  have hcheck' : checkOffsetLen
      ((year ++ "-" ++ month ++ "-" ++ day) ++ String.singleton 'T' ++
        (hh ++ ":" ++ mm ++ ":" ++ ss ++ "." ++ sss) ++
        String.singleton (if neg then '-' else '+') ++ ohh ++ omm) = true := by
    cases neg <;> simpa [String.append_assoc,
      show ("T" : String) = String.singleton 'T' from rfl,
      show ("+" : String) = String.singleton '+' from rfl,
      show ("-" : String) = String.singleton '-' from rfl] using hcheck
  obtain ⟨hohfd, hommfd⟩ :=
    checkOffsetLen_offset_fields neg hdateT htimeT htimeSign hohdig hommdig hcheck'
  exact ⟨year, month, day, hh, mm, ss, sss, neg, ohh, omm, hm, hd, hyfd, hmfd,
    hdfd, hhfd, hmmfd, hssfd, hsssfd, hohfd, hommfd, hhbound, hmmbound, hssbound,
    hohb, hommb, hstr, H, m, sec, S, off, hbuild⟩

open Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **`build` inversion (DateWithOffsetAndMillis).** The fractional-seconds and offset fields do not
    enter the `Year.Offset.Valid` day guard. -/
theorem build_dateWithOffsetAndMillis_inv {yr mo dy : Nat} (H : Hour.Ordinal) (m : Minute.Ordinal)
    (sec : Second.Ordinal true) (S : Nanosecond.Ordinal) (off : Std.Time.TimeZone.Offset)
    (hm : 1 ≤ mo ∧ mo ≤ 12) (hd : 1 ≤ dy ∧ dy ≤ 31)
    (zt : Std.Time.ZonedDateTime)
    (hbuild : ({ ({} : DateBuilder) with
        y := some (Int.ofNat yr),
        M := some (Bounded.LE.ofNat' mo hm),
        d := some (Bounded.LE.ofNat' dy hd),
        H := some H, m := some m, s := some sec, S := some S, x := some off }).build .any = some zt) :
    dy ≤ daysInMonth yr mo :=
  build_datetime_inv
    (some H) (some m) (some sec) (some S) (some off) hm hd zt hbuild

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- The DateWithOffsetAndMillis `parser.go` preserves the string component on success. -/
theorem dateWithOffsetAndMillis_go_preserves {s : String} (config : FormatConfig)
    (hcfg : config.allowLeapSeconds = false) (p : s.Pos) (rem : ParseIt)
    (zt : Std.Time.ZonedDateTime)
    (hgo : parser.go config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .string ".",
         .modifier (.S (.truncated 3)), .modifier (.x .hourMinute)]
        ⟨s, p⟩ = ParseResult.success rem zt) : rem.1 = s := by
  obtain ⟨p11, _, hgo⟩ := datetimePrefix_go config hcfg p rem zt
    [.string ".", .modifier (.S (.truncated 3)), .modifier (.x .hourMinute)] hgo
  obtain ⟨p12, _, _, hgo⟩ := go_step_string config .any _ "." _ p11 _ zt hgo
  obtain ⟨p13, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p12 _ zt
    (fun r b' h => parseWithDate_fraction_preserves _ config p12 r b' h) hgo
  obtain ⟨p14, _, _, hgo⟩ := go_step_modifier config .any _ _ _ p13 _ zt
    (fun r b' h => parseWithDate_offset_preserves _ config p13 r b' h) hgo
  exact go_nil_preserves config _ p14 rem zt hgo

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.GenericFormat in
/-- **DateWithOffsetAndMillis `parse` success-inversion.** -/
theorem dateWithOffsetAndMillis_parse_ok_inv (str : String) (zt : Std.Time.ZonedDateTime)
    (h : DateWithOffsetAndMillis.parse str = .ok zt) :
    parser.go DateWithOffsetAndMillis.config .any {}
        [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2}), .string ".",
         .modifier (.S (.truncated 3)), .modifier (.x .hourMinute)]
        ⟨str, str.startPos⟩ = ParseResult.success ⟨str, str.endPos⟩ zt :=
  parse_ok_inv_of_preserves DateWithOffsetAndMillis str zt _ rfl
    (fun rem a hp =>
      dateWithOffsetAndMillis_go_preserves
        DateWithOffsetAndMillis.config rfl str.startPos rem a hp) h

open Cedar.Spec.Ext.Datetime in
/-- **DateWithOffsetAndMillis case of `wf_of_parse`.** -/
theorem dateWithOffsetAndMillis_wf_inv (str : String) (zt : Std.Time.ZonedDateTime)
    (hlen : checkOffsetLen str = true) (h : DateWithOffsetAndMillis.parse str = .ok zt) :
    ∃ c : DatetimeComponents, str = c.asString ∧ c.syntaxWf ∧ c.constraintsWf := by
  have hgo := dateWithOffsetAndMillis_parse_ok_inv str zt h
  obtain ⟨year, month, day, hh, mm, ss, sss, neg, ohh, omm, hm, hd, hyfd, hmfd, hdfd, hhfd, hmmfd,
      hssfd, hsssfd, hohfd, hommfd, hhbound, hmmbound, hssbound, hohb, hommb, hstr,
      H, m, sec, S, off, hbuild⟩ :=
    dateWithOffsetAndMillis_full_inv DateWithOffsetAndMillis.config rfl hlen zt hgo
  have hdayle : fieldValue day ≤ daysInMonth (fieldValue year) (fieldValue month) :=
    build_dateWithOffsetAndMillis_inv H m sec S off hm hd zt hbuild
  refine ⟨{ date := { year, month, day },
            time := some ⟨⟨hh, mm, ss⟩, some sss, Zone.offset ⟨neg, ohh, omm⟩⟩ }, ?_, ?_, ?_⟩
  · show str = ({ year, month, day } : DateComponents).asString
        ++ ("T" ++ (⟨hh, mm, ss⟩ : TimeComponents).asString
            ++ (match (some sss : Option String) with | none => "" | some sss => "." ++ sss)
            ++ (Zone.offset ⟨neg, ohh, omm⟩).asString)
    show str = year ++ "-" ++ month ++ "-" ++ day
        ++ ("T" ++ (hh ++ ":" ++ mm ++ ":" ++ ss) ++ ("." ++ sss)
            ++ ((if neg then "-" else "+") ++ ohh ++ omm))
    rw [hstr]; simp only [String.append_assoc]
  · exact ⟨⟨hyfd, hmfd, hdfd⟩, ⟨hhfd, hmmfd, hssfd⟩, hsssfd, hohfd, hommfd⟩
  · exact ⟨⟨hm.1, hm.2, hd.1, hdayle⟩, ⟨hhbound, hmmbound, hssbound⟩, hohb, hommb⟩

open Cedar.Spec.Ext.Datetime in
/-- **`wf_of_parse`** (the target). Dispatch on which parser in the 5-way alternation succeeded.
    The DateOnly branch is fully discharged by `dateOnly_wf_inv`; the other four formats require the
    analogous full inversions (see the honest-blocker note in the report). -/
theorem wf_of_parse {str : String} (zt : Std.Time.ZonedDateTime)
    (hlen : checkOffsetLen str = true)
    (hzt : (DateOnly.parse str <|> DateUTC.parse str
        <|> DateUTCWithMillis.parse str <|> DateWithOffset.parse str
        <|> DateWithOffsetAndMillis.parse str).toOption = some zt) :
    ∃ c : DatetimeComponents, str = c.asString ∧ c.syntaxWf ∧ c.constraintsWf := by
  -- Case on whether the first parser (DateOnly) succeeds.
  cases hdo : DateOnly.parse str with
  | ok zt0 =>
    -- DateOnly succeeded: the whole `.ok` inverts to a well-formed date-only component.
    exact dateOnly_wf_inv str zt0 hdo
  | error e0 =>
    -- DateOnly failed; the alternation falls through to the remaining four parsers.
    rw [hdo] at hzt
    replace hzt : (DateUTC.parse str <|> DateUTCWithMillis.parse str
        <|> DateWithOffset.parse str <|> DateWithOffsetAndMillis.parse str).toOption = some zt := hzt
    cases hutc : DateUTC.parse str with
    | ok zt1 =>
      exact dateUTC_wf_inv str zt1 hutc
    | error e1 =>
      rw [hutc] at hzt
      replace hzt : (DateUTCWithMillis.parse str
          <|> DateWithOffset.parse str <|> DateWithOffsetAndMillis.parse str).toOption
          = some zt := hzt
      cases hutcm : DateUTCWithMillis.parse str with
      | ok zt2 =>
        exact dateUTCWithMillis_wf_inv str zt2 hutcm
      | error e2 =>
        rw [hutcm] at hzt
        replace hzt : (DateWithOffset.parse str <|> DateWithOffsetAndMillis.parse str).toOption
            = some zt := hzt
        cases hoff : DateWithOffset.parse str with
        | ok zt3 =>
          exact dateWithOffset_wf_inv str zt3 hlen hoff
        | error e3 =>
          rw [hoff] at hzt
          replace hzt : (DateWithOffsetAndMillis.parse str).toOption = some zt := hzt
          cases hoffm : DateWithOffsetAndMillis.parse str with
          | ok zt4 =>
            exact dateWithOffsetAndMillis_wf_inv str zt4 hlen hoffm
          | error e4 =>
            rw [hoffm] at hzt
            -- All five failed: `.toOption` of an error is `none`, contradicting `some zt`.
            simp [Except.toOption] at hzt

end WfOfParse

section AlternationProof
open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat Cedar.Spec.Ext.Datetime

/-! ## Except `<|>` reductions -/

theorem except_ok_orElse {α : Type} (a : α)
    (q : Except String α) :
    (Except.ok a <|> q) = Except.ok a := rfl

theorem except_error_orElse {α : Type} (e : String)
    (q : Except String α) :
    (Except.error e <|> q) = q := rfl

/-! ## Master "parse produces error" helpers

`GenericFormat.parse F s = (parser F.string F.config .any <* eof).run s`. Two ways the alternation's
earlier parsers fail on a wrong-form string:
  (A) the inner `parser` itself errors (a `pstring`/offset step diverges); or
  (B) the inner `parser` succeeds but *not at end of string* (leftover), so the trailing `<* eof`
      rejects. -/

/-- (A) If the inner `parser` errors, so does `.parse`. -/
theorem parse_error_of_parser_error {aw : Awareness} (F : GenericFormat aw) (s : String)
    (pos : ParseIt) (err : Std.Internal.Parsec.Error)
    (h : parser F.string F.config aw ⟨s, s.startPos⟩ = ParseResult.error pos err) :
    ∃ e, F.parse s = .error e := by
  unfold GenericFormat.parse Std.Internal.Parsec.String.Parser.run
  rw [seqLeft_app, h]
  exact ⟨_, rfl⟩

/-- (B) If the inner `parser` succeeds at a position `p ≠ endPos`, `<* eof` rejects, so `.parse`
    errors. -/
theorem parse_error_of_parser_success_ne_end {aw : Awareness} (F : GenericFormat aw) (s : String)
    (p : s.Pos) (a : aw.type) (hp : p ≠ s.endPos)
    (h : parser F.string F.config aw ⟨s, s.startPos⟩ = ParseResult.success ⟨s, p⟩ a) :
    ∃ e, F.parse s = .error e := by
  unfold GenericFormat.parse Std.Internal.Parsec.String.Parser.run
  rw [seqLeft_app, h]
  have heof : eof (⟨s, p⟩ : ParseIt)
      = ParseResult.error (⟨s, p⟩ : ParseIt) (.other "expected end of input") := by
    show (if Input.hasNext (⟨s, p⟩ : ParseIt) then _ else _) = _
    have hhn : Input.hasNext (⟨s, p⟩ : ParseIt) = true := (hasNext_iff s p).mpr hp
    rw [hhn]; rfl
  simp only [heof]
  exact ⟨_, rfl⟩

/-! ## DateOnly fails on a time-bearing string

`c.asString = c.date.asString ++ tp.asString` with `tp.asString = "T" ++ ...` nonempty. The DateOnly
format's `parser.go` threads the five date steps identically (they only inspect the date prefix),
`build` succeeds, but the resulting position sits right after the date (before `"T"`), which is not
`endPos`. So `<* eof` rejects. -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- The DateOnly `parser.go` threaded on `c.date.asString ++ tail` (any `tail`) reaches `[]` with the
    date builder at the position splitting `c.date.asString | tail`. -/
theorem dateOnly_go_on_prefix {d : DateComponents} (tail : String) (config : FormatConfig)
    (hsyn : d.syntaxWf) (hcon : d.constraintsWf) :
    ∃ (hm : 1 ≤ fieldValue d.month ∧ fieldValue d.month ≤ 12)
      (hd : 1 ≤ fieldValue d.day ∧ fieldValue d.day ≤ 31)
      (p : (d.asString ++ tail).Pos),
      parser.go config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2})]
          ⟨d.asString ++ tail, (d.asString ++ tail).startPos⟩
        = parser.go config .any
            { ({} : DateBuilder) with
              y := some (Int.ofNat (fieldValue d.year)),
              M := some (Bounded.LE.ofNat' (fieldValue d.month) hm),
              d := some (Bounded.LE.ofNat' (fieldValue d.day) hd) }
            [] ⟨d.asString ++ tail, p⟩ ∧
      p.Splits d.asString tail := by
  obtain ⟨hy, hmm, hdd⟩ := hsyn
  obtain ⟨hm1, hm2, hd1, hd2⟩ := hcon
  have hmbound : 1 ≤ fieldValue d.month ∧ fieldValue d.month ≤ 12 := ⟨hm1, hm2⟩
  have hdaysle : daysInMonth (fieldValue d.year) (fieldValue d.month) ≤ 31 := by
    unfold daysInMonth
    split
    · omega
    · split
      · split <;> omega
      · omega
  have hdbound : 1 ≤ fieldValue d.day ∧ fieldValue d.day ≤ 31 := ⟨hd1, Nat.le_trans hd2 hdaysle⟩
  -- Re-associate so each date field sits at the front of the remaining suffix, tail at the end.
  have hassoc : d.asString ++ tail = d.year ++ ("-" ++ (d.month ++ ("-" ++ (d.day ++ tail)))) := by
    unfold DateComponents.asString
    rw [String.append_assoc, String.append_assoc, String.append_assoc, String.append_assoc]
  have hsplit0 : (d.asString ++ tail).startPos.Splits ""
      (d.year ++ ("-" ++ (d.month ++ ("-" ++ (d.day ++ tail))))) := by
    rw [← hassoc]; exact String.splits_startPos _
  obtain ⟨p1, hpar1, hsp1⟩ :=
    step_year (d.asString ++ tail).startPos ""
      ("-" ++ (d.month ++ ("-" ++ (d.day ++ tail)))) d.year {} config hy hsplit0
  rw [String.empty_append] at hsp1
  obtain ⟨p2, hpar2, hsp2⟩ :=
    step_sep p1 d.year (d.month ++ ("-" ++ (d.day ++ tail))) "-"
      { ({} : DateBuilder) with y := some (Int.ofNat (fieldValue d.year)) } config hsp1
  obtain ⟨p3, hm', hpar3, hsp3⟩ :=
    step_month p2 (d.year ++ "-") ("-" ++ (d.day ++ tail)) d.month
      { ({} : DateBuilder) with y := some (Int.ofNat (fieldValue d.year)) } config hmm hmbound hsp2
  let bYM : DateBuilder :=
    { ({} : DateBuilder) with y := some (Int.ofNat (fieldValue d.year)),
                              M := some (Bounded.LE.ofNat' (fieldValue d.month) hm') }
  obtain ⟨p4, hpar4, hsp4⟩ :=
    step_sep p3 (d.year ++ "-" ++ d.month) (d.day ++ tail) "-" bYM config hsp3
  obtain ⟨p5, hd', hpar5, hsp5⟩ :=
    step_day p4 (d.year ++ "-" ++ d.month ++ "-") tail d.day bYM config hdd hdbound hsp4
  refine ⟨hm', hd', p5, ?_, ?_⟩
  · simp only [go_cons_app, hpar1, hpar2, hpar3, hpar4, hpar5, bYM]
  · -- p5.Splits (d.year ++ "-" ++ d.month ++ "-" ++ d.day) tail ; rewrite LHS to d.asString
    have : d.year ++ "-" ++ d.month ++ "-" ++ d.day = d.asString := by
      unfold DateComponents.asString; rfl
    rw [this] at hsp5
    exact hsp5

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **DateOnly fails on a time-bearing string.** If `c.time = some tp`, then
    `c.asString = c.date.asString ++ tp.asString` with `tp.asString` nonempty (starts with `"T"`),
    so `DateOnly.parse c.asString = .error`. -/
theorem dateOnly_parse_error_of_time {c : DatetimeComponents} (tp : TimePart)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp) :
    ∃ e, DateOnly.parse c.asString = .error e := by
  have hdsyn : c.date.syntaxWf := hsyn.1
  have hdcon : c.date.constraintsWf := hcon.1
  -- c.asString = c.date.asString ++ tp.asString
  have hcstr : c.asString = c.date.asString ++ tp.asString := by
    simp only [DatetimeComponents.asString, htime]
  -- tp.asString is nonempty (starts with the literal 'T')
  have htail_ne : tp.asString ≠ "" := by
    intro h
    have hlen := congrArg String.length h
    simp only [TimePart.asString, String.length_append] at hlen
    have h1 : "T".length = 1 := by decide
    have h0 : "".length = 0 := by decide
    omega
  obtain ⟨hm, hd, p, hgo, hsp⟩ := dateOnly_go_on_prefix tp.asString DateOnly.config hdsyn hdcon
  -- build succeeds
  obtain ⟨zt, hbuild, _⟩ := build_dateOnly_value hdsyn hdcon hm hd _ rfl
  -- the inner parser succeeds at position p (= after date, before tail), which is ≠ endPos
  have hp_ne : p ≠ (c.date.asString ++ tp.asString).endPos := by
    rw [Ne, hsp.eq_endPos_iff]; exact htail_ne
  have hparser : parser DateOnly.string DateOnly.config .any
      ⟨c.date.asString ++ tp.asString, (c.date.asString ++ tp.asString).startPos⟩
      = ParseResult.success ⟨c.date.asString ++ tp.asString, p⟩ zt := by
    have hp : parser DateOnly.string DateOnly.config .any
        = parser.go DateOnly.config .any {}
            [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
             .string "-", .modifier (.d {padding := 2})] := rfl
    rw [hp, hgo]
    exact go_nil_some DateOnly.config _ _ zt hbuild
  rw [hcstr]
  exact parse_error_of_parser_success_ne_end DateOnly _ p zt hp_ne hparser

/-! ## Next-part failure primitives -/

/-- `pstring (singleton lc)` fails at position `p` whose remaining suffix starts with `c ≠ lc`. -/
theorem pstring_singleton_error {s : String} (p : s.Pos) (pre rest : String) (c lc : Char)
    (hsplit : p.Splits pre (String.singleton c ++ rest)) (hne : lc ≠ c) :
    ∃ e, pstring (String.singleton lc) (⟨s, p⟩ : ParseIt) = ParseResult.error ⟨s, p⟩ e := by
  have hguard : (s.sliceFrom p).startsWith (String.singleton lc) = false := by
    rw [String.Slice.startsWith_string_eq_false_iff, hsplit.copy_sliceFrom_eq]
    rw [String.toList_singleton, String.toList_append, String.toList_singleton]
    intro hpre
    -- [lc] <+: c :: rest.toList  ⇒  lc = c, contradiction
    obtain ⟨l', hl'⟩ := hpre
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl'
    exact hne hl'.1
  refine ⟨.other s!"expected: {String.singleton lc}", ?_⟩
  show (if (s.sliceFrom p).startsWith (String.singleton lc) then _ else _) = _
  rw [hguard]
  simp only [Bool.false_eq_true, ↓reduceIte]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWithDate b config (.string (singleton lc))` fails at a position whose remaining suffix
    starts with `c ≠ lc`. -/
theorem parseWithDate_string_error {s : String} (p : s.Pos) (pre rest : String) (c lc : Char)
    (b : DateBuilder) (config : FormatConfig)
    (hsplit : p.Splits pre (String.singleton c ++ rest)) (hne : lc ≠ c) :
    ∃ (pos : ParseIt) (e : Std.Internal.Parsec.Error),
      parseWithDate b config (.string (String.singleton lc)) ⟨s, p⟩ = ParseResult.error pos e := by
  obtain ⟨e, herr⟩ := pstring_singleton_error p pre rest c lc hsplit hne
  refine ⟨⟨s, p⟩, e, ?_⟩
  unfold parseWithDate
  simp only [pure, SeqRight.seqRight]
  show (Std.Internal.Parsec.bind (pstring (String.singleton lc)) (fun _ => Std.Internal.Parsec.pure b)) ⟨s, p⟩ = _
  rw [parsec_bind_app, herr]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- The offset modifier `parseWith config (.x .hourMinute)` fails at a position whose remaining
    suffix starts with `c₀ ∉ {'+','-'}` (its leading sign alternation rejects). -/
theorem parseWith_offset_error {s : String} (p : s.Pos) (pre rest : String) (c₀ : Char)
    (config : FormatConfig)
    (hsplit : p.Splits pre (String.singleton c₀ ++ rest)) (hp : c₀ ≠ '+') (hm : c₀ ≠ '-') :
    ∃ (pos : ParseIt) (e : Std.Internal.Parsec.Error),
      parseWith config (.x .hourMinute) ⟨s, p⟩ = ParseResult.error pos e := by
  have hne : p ≠ s.endPos := hsplit.ne_endPos_of_singleton
  have hhn : Input.hasNext (⟨s, p⟩ : ParseIt) = true := (hasNext_iff s p).mpr hne
  have hgetc : p.get hne = c₀ := by
    obtain ⟨t₂', ht⟩ := hsplit.exists_eq_singleton_append hne
    rw [String.singleton_append_inj] at ht
    exact ht.1.symm
  -- pchar '+' fails at ⟨s,p⟩ (position unchanged).
  have hplus : pchar '+' (⟨s, p⟩ : ParseIt)
      = ParseResult.error ⟨s, p⟩ (.other s!"expected: '{'+'}'") := by
    rw [pchar_eq]; simp only [hhn, dif_pos]; rw [curr'_eq]
    have : ¬ (p.get ((hasNext_iff s p).mp hhn) = '+') := by rw [hgetc]; exact hp
    simp only [this, if_false]
  have hminus : pchar '-' (⟨s, p⟩ : ParseIt)
      = ParseResult.error ⟨s, p⟩ (.other s!"expected: '{'-'}'") := by
    rw [pchar_eq]; simp only [hhn, dif_pos]; rw [curr'_eq]
    have : ¬ (p.get ((hasNext_iff s p).mp hhn) = '-') := by rw [hgetc]; exact hm
    simp only [this, if_false]
  refine ⟨⟨s, p⟩, .other s!"expected: '{'-'}'", ?_⟩
  show Std.Time.parseOffset .yes .no false ⟨s, p⟩ = _
  unfold Std.Time.parseOffset
  simp only [bind, Bind.bind]
  rw [parsec_bind_app]
  -- The sign alternation errors at ⟨s,p⟩.
  have hsign : ((pchar '+' *> pure 1) <|> (pchar '-' *> pure (-1)) : Parser Int) ⟨s, p⟩
      = ParseResult.error ⟨s, p⟩ (.other s!"expected: '{'-'}'") := by
    rw [orElse_app, seqRight_app, hplus]
    simp only [Input.pos, if_true]
    rw [seqRight_app, hminus]
  rw [hsign]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal in
/-- `parseWithDate b config (.modifier (.x .hourMinute))` fails when the offset modifier fails. -/
theorem parseWithDate_offset_error {s : String} (p : s.Pos) (pre rest : String) (c₀ : Char)
    (b : DateBuilder) (config : FormatConfig)
    (hsplit : p.Splits pre (String.singleton c₀ ++ rest)) (hp : c₀ ≠ '+') (hm : c₀ ≠ '-') :
    ∃ (pos : ParseIt) (e : Std.Internal.Parsec.Error),
      parseWithDate b config (.modifier (.x .hourMinute)) ⟨s, p⟩ = ParseResult.error pos e := by
  obtain ⟨pos, e, herr⟩ := parseWith_offset_error p pre rest c₀ config hsplit hp hm
  refine ⟨pos, e, ?_⟩
  unfold parseWithDate
  simp only [bind, Bind.bind, pure]
  rw [parsec_bind_app, herr]

/-! ## Shared `yyyy-MM-dd'T'HH:mm:ss` prefix threading

All four time-bearing formats share the 11-part prefix `[y,"-",M,"-",d,"T",H,":",m,":",s]`. This
lemma threads that prefix on `c.date.asString ++ "T" ++ tp.time.asString ++ tail` (any `tail`, any
format suffix `suf`), leaving `parser.go` positioned after the seconds field with the six-field
builder, ready to run `suf`. -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
theorem prefix_thread {c : DatetimeComponents} (tp : TimePart) (tail : String)
    (config : FormatConfig) (hcfg : config.allowLeapSeconds = false)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp)
    (suf : FormatString) :
    ∃ (hm : 1 ≤ fieldValue c.date.month ∧ fieldValue c.date.month ≤ 12)
      (hd : 1 ≤ fieldValue c.date.day ∧ fieldValue c.date.day ≤ 31)
      (hh : 0 ≤ fieldValue tp.time.hours ∧ fieldValue tp.time.hours ≤ 23)
      (hmin : 0 ≤ fieldValue tp.time.minutes ∧ fieldValue tp.time.minutes ≤ 59)
      (hsec : 0 ≤ fieldValue tp.time.seconds ∧ fieldValue tp.time.seconds ≤ 59)
      (p : (c.date.asString ++ "T" ++ tp.time.asString ++ tail).Pos),
      parser.go config .any {}
          ([.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
            .string "-", .modifier (.d {padding := 2}), .string "T",
            .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
            .string ":", .modifier (.s {padding := 2})] ++ suf)
          ⟨c.date.asString ++ "T" ++ tp.time.asString ++ tail,
            (c.date.asString ++ "T" ++ tp.time.asString ++ tail).startPos⟩
        = parser.go config .any
            { ({} : DateBuilder) with
              y := some (Int.ofNat (fieldValue c.date.year)),
              M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
              d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
              H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
              m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
              s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                          : Bounded.LE 0 60) }
            suf ⟨c.date.asString ++ "T" ++ tp.time.asString ++ tail, p⟩ ∧
      p.Splits (c.date.asString ++ "T" ++ tp.time.asString) tail :=
  parseWithDate_datetimePrefix tp tail config hcfg hsyn hcon htime suf

/-! ## Tail structure after `time.asString`

`c.asString = c.date.asString ++ "T" ++ tp.time.asString ++ tail`, where
`tail = (millis-part) ++ tp.zone.asString`. We expose `tail = singleton c₀ ++ rest` and identify the
leading char `c₀` for each form. -/

/-- `c.asString` factors through the shared prefix and a tail. -/
theorem asString_prefix_tail {c : DatetimeComponents} (tp : TimePart) (htime : c.time = some tp) :
    c.asString = c.date.asString ++ "T" ++ tp.time.asString
      ++ ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString) := by
  simp only [DatetimeComponents.asString, TimePart.asString, htime, String.append_assoc]
  rfl

/-! ## Wrong-form failure via prefix + next-part mismatch

Given a `.string (singleton lc)` as the first suffix part, if the tail (after `ss`) starts with
`c₀ ≠ lc`, the format `F = prefix ++ [.string (singleton lc), ...]` errors on `c.asString`. -/

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- Master wrong-form failure for formats whose first post-prefix part is a `.string (singleton lc)`
    literal, when the actual tail starts with `c₀ ≠ lc`. -/
theorem parse_error_string_suffix (F : GenericFormat .any)
    {c : DatetimeComponents} (tp : TimePart) (lc c₀ : Char) (rest : String) (suf' : FormatString)
    (hcfg : F.config.allowLeapSeconds = false)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp)
    (hstr : F.string
      = [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2})] ++ (.string (String.singleton lc) :: suf'))
    (htail : (match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString
      = String.singleton c₀ ++ rest)
    (hne : lc ≠ c₀) :
    ∃ e, F.parse c.asString = .error e := by
  -- The full string equals prefix-string ++ tail.
  have hcstr := asString_prefix_tail tp htime
  -- Thread the shared prefix; the config comes from F.
  obtain ⟨hm, hd, hh, hmin, hsec, p, hgo, hsp⟩ :=
    prefix_thread tp ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString)
      F.config hcfg hsyn hcon htime (.string (String.singleton lc) :: suf')
  -- Rewrite target into the fixed string.
  rw [hcstr]
  -- tail = singleton c₀ ++ rest, so p splits (date++T++time) (singleton c₀ ++ rest)
  have hsp' : p.Splits (c.date.asString ++ "T" ++ tp.time.asString) (String.singleton c₀ ++ rest) := by
    rw [← htail]; exact hsp
  obtain ⟨pos, e, herr⟩ := parseWithDate_string_error p _ rest c₀ lc _ F.config hsp' hne
  -- Build: the inner parser errors.
  have hparser : parser F.string F.config .any
      ⟨c.date.asString ++ "T" ++ tp.time.asString
          ++ ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString),
        (c.date.asString ++ "T" ++ tp.time.asString
          ++ ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString)).startPos⟩
      = ParseResult.error pos e := by
    have hp : parser F.string F.config .any = parser.go F.config .any {} F.string := rfl
    rw [hp, hstr, hgo, go_cons_app, herr]
  exact parse_error_of_parser_error F _ pos e hparser

/-! ## Tail leading-char decompositions

Identify `tail = singleton c₀ ++ rest` for each shape. -/

/-- Millis present: tail starts with `'.'`. -/
theorem tail_millis {tp : TimePart} {sss : String} (hmillis : tp.millis = some sss) :
    ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString)
      = String.singleton '.' ++ (sss ++ tp.zone.asString) := by
  rw [hmillis]
  simp only [String.append_assoc]
  rfl

/-- No millis, offset zone: tail starts with the sign char. -/
theorem tail_offset {tp : TimePart} {o : OffsetComponents}
    (hmillis : tp.millis = none) (hzone : tp.zone = Zone.offset o) :
    ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString)
      = String.singleton (if o.negative then '-' else '+') ++ (o.hours ++ o.minutes) := by
  rw [hmillis, hzone]
  simp only [String.empty_append, Zone.asString, OffsetComponents.asString, String.append_assoc]
  cases o.negative <;> rfl

/-- No millis, UTC zone: tail is exactly `"Z"`. -/
theorem tail_utc {tp : TimePart} (hmillis : tp.millis = none) (hutc : tp.zone = Zone.utc) :
    ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString)
      = String.singleton 'Z' ++ "" := by
  rw [hmillis, hutc]
  simp only [String.empty_append, Zone.asString]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- Master wrong-form failure for formats whose first post-prefix part is the offset modifier
    `.x .hourMinute`, when the actual tail starts with `c₀ ∉ {'+','-'}`. -/
theorem parse_error_offset_suffix (F : GenericFormat .any)
    {c : DatetimeComponents} (tp : TimePart) (c₀ : Char) (rest : String) (suf' : FormatString)
    (hcfg : F.config.allowLeapSeconds = false)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp)
    (hstr : F.string
      = [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2})] ++ (.modifier (.x .hourMinute) :: suf'))
    (htail : (match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString
      = String.singleton c₀ ++ rest)
    (hp : c₀ ≠ '+') (hm : c₀ ≠ '-') :
    ∃ e, F.parse c.asString = .error e := by
  have hcstr := asString_prefix_tail tp htime
  obtain ⟨_, _, _, _, _, p, hgo, hsp⟩ :=
    prefix_thread tp ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString)
      F.config hcfg hsyn hcon htime (.modifier (.x .hourMinute) :: suf')
  rw [hcstr]
  have hsp' : p.Splits (c.date.asString ++ "T" ++ tp.time.asString) (String.singleton c₀ ++ rest) := by
    rw [← htail]; exact hsp
  obtain ⟨pos, e, herr⟩ := parseWithDate_offset_error p _ rest c₀ _ F.config hsp' hp hm
  have hparser : parser F.string F.config .any
      ⟨c.date.asString ++ "T" ++ tp.time.asString
          ++ ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString),
        (c.date.asString ++ "T" ++ tp.time.asString
          ++ ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString)).startPos⟩
      = ParseResult.error pos e := by
    have hpp : parser F.string F.config .any = parser.go F.config .any {} F.string := rfl
    rw [hpp, hstr, hgo, go_cons_app, herr]
  exact parse_error_of_parser_error F _ pos e hparser

/-! ## Per-parser wrong-form failures -/

/-- `DateUTC.string` decomposes as prefix ++ `.string "Z" :: []`. -/
theorem dateUTC_string_eq :
    DateUTC.string
      = [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2})]
        ++ (.string (String.singleton 'Z') :: []) := rfl

theorem dateUTCWithMillis_string_eq :
    DateUTCWithMillis.string
      = [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2})]
        ++ (.string (String.singleton '.') :: [.modifier (.S (.truncated 3)), .string "Z"]) := rfl

/-- **DateUTC fails on a millis-bearing string** (tail starts with `'.'`). -/
theorem dateUTC_parse_error_of_millis {c : DatetimeComponents} (tp : TimePart) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp)
    (hmillis : tp.millis = some sss) :
    ∃ e, DateUTC.parse c.asString = .error e :=
  parse_error_string_suffix DateUTC tp 'Z' '.' (sss ++ tp.zone.asString) []
    rfl hsyn hcon htime dateUTC_string_eq (tail_millis hmillis) (by decide)

/-- **DateUTC fails on an offset-no-millis string** (tail starts with the sign). -/
theorem dateUTC_parse_error_of_offset {c : DatetimeComponents} (tp : TimePart) (o : OffsetComponents)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp)
    (hmillis : tp.millis = none) (hzone : tp.zone = Zone.offset o) :
    ∃ e, DateUTC.parse c.asString = .error e :=
  parse_error_string_suffix DateUTC tp 'Z' (if o.negative then '-' else '+') (o.hours ++ o.minutes) []
    rfl hsyn hcon htime dateUTC_string_eq (tail_offset hmillis hzone) (by cases o.negative <;> decide)

/-- **DateUTCWithMillis fails on a UTC-no-millis string** (tail starts with `'Z'`). -/
theorem dateUTCWithMillis_parse_error_of_utc {c : DatetimeComponents} (tp : TimePart)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp)
    (hmillis : tp.millis = none) (hutc : tp.zone = Zone.utc) :
    ∃ e, DateUTCWithMillis.parse c.asString = .error e :=
  parse_error_string_suffix DateUTCWithMillis tp '.' 'Z' "" [.modifier (.S (.truncated 3)), .string "Z"]
    rfl hsyn hcon htime dateUTCWithMillis_string_eq (tail_utc hmillis hutc) (by decide)

/-- **DateUTCWithMillis fails on an offset-no-millis string** (tail starts with the sign). -/
theorem dateUTCWithMillis_parse_error_of_offset {c : DatetimeComponents} (tp : TimePart)
    (o : OffsetComponents)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp)
    (hmillis : tp.millis = none) (hzone : tp.zone = Zone.offset o) :
    ∃ e, DateUTCWithMillis.parse c.asString = .error e :=
  parse_error_string_suffix DateUTCWithMillis tp '.' (if o.negative then '-' else '+')
    (o.hours ++ o.minutes) [.modifier (.S (.truncated 3)), .string "Z"]
    rfl hsyn hcon htime dateUTCWithMillis_string_eq (tail_offset hmillis hzone)
    (by cases o.negative <;> decide)

theorem dateWithOffset_string_eq :
    DateWithOffset.string
      = [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
         .string "-", .modifier (.d {padding := 2}), .string "T",
         .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
         .string ":", .modifier (.s {padding := 2})]
        ++ (.modifier (.x .hourMinute) :: []) := rfl

/-- **DateWithOffset fails on a millis-bearing string** (tail starts with `'.'`, not a sign). -/
theorem dateWithOffset_parse_error_of_millis {c : DatetimeComponents} (tp : TimePart) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp)
    (hmillis : tp.millis = some sss) :
    ∃ e, DateWithOffset.parse c.asString = .error e :=
  parse_error_offset_suffix DateWithOffset tp '.' (sss ++ tp.zone.asString) []
    rfl hsyn hcon htime dateWithOffset_string_eq (tail_millis hmillis) (by decide) (by decide)

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **DateUTCWithMillis fails on an offset-AND-millis string.** The `.` and `.SSS` parts match, but
    the trailing `.string "Z"` sees the offset sign. -/
theorem dateUTCWithMillis_parse_error_of_offsetMillis {c : DatetimeComponents} (tp : TimePart)
    (o : OffsetComponents) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf) (htime : c.time = some tp)
    (hmillis : tp.millis = some sss) (hzone : tp.zone = Zone.offset o) :
    ∃ e, DateUTCWithMillis.parse c.asString = .error e := by
  -- SSS is well-formed (3 digits) from syntaxWf.
  have hsssdig : IsFixedDigits 3 sss := by
    have htsyn : tp.syntaxWf := by
      have := hsyn.2; rw [htime] at this; exact this
    have := htsyn.2.1
    rw [hmillis] at this; exact this
  have hsssb : fieldValue sss ≤ 999 := fieldValue_le_999 hsssdig
  have hcstr := asString_prefix_tail tp htime
  -- Thread the shared prefix with suffix [".", .S trunc3, "Z"].
  obtain ⟨hm, hd, hh, hmin, hsec, p, hgo, hsp⟩ :=
    prefix_thread tp ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString)
      DateUTCWithMillis.config rfl hsyn hcon htime
      [.string (String.singleton '.'), .modifier (.S (.truncated 3)), .string "Z"]
  -- The six-field builder that `prefix_thread` leaves.
  let b6 : DateBuilder :=
    { ({} : DateBuilder) with
      y := some (Int.ofNat (fieldValue c.date.year)),
      M := some (Bounded.LE.ofNat' (fieldValue c.date.month) hm),
      d := some (Bounded.LE.ofNat' (fieldValue c.date.day) hd),
      H := some (Bounded.LE.ofNat' (fieldValue tp.time.hours) hh),
      m := some (Bounded.LE.ofNat' (fieldValue tp.time.minutes) hmin),
      s := some ((Bounded.LE.ofNat' (fieldValue tp.time.seconds) hsec).expandTop (by decide)
                  : Bounded.LE 0 60) }
  rw [hcstr]
  -- tail = "." ++ sss ++ (sign ++ hh ++ mm)
  have htail : (match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString
      = String.singleton '.' ++ (sss ++ (String.singleton (if o.negative then '-' else '+')
          ++ (o.hours ++ o.minutes))) := by
    rw [hmillis, hzone]
    simp only [Zone.asString, OffsetComponents.asString, String.append_assoc]
    cases o.negative <;> rfl
  have hsp0 : p.Splits (c.date.asString ++ "T" ++ tp.time.asString)
      (String.singleton '.' ++ (sss ++ (String.singleton (if o.negative then '-' else '+')
          ++ (o.hours ++ o.minutes)))) := by
    rw [← htail]; exact hsp
  -- Step: "." matches.
  obtain ⟨p1, hpar1, hsp1⟩ :=
    step_sep p (c.date.asString ++ "T" ++ tp.time.asString)
      (sss ++ (String.singleton (if o.negative then '-' else '+') ++ (o.hours ++ o.minutes)))
      (String.singleton '.') b6 DateUTCWithMillis.config hsp0
  -- Step: .SSS parses sss.
  obtain ⟨p2, _hh2, hpar2, hsp2⟩ :=
    step_fraction p1 (c.date.asString ++ "T" ++ tp.time.asString ++ String.singleton '.')
      (String.singleton (if o.negative then '-' else '+') ++ (o.hours ++ o.minutes)) sss b6
      DateUTCWithMillis.config hsssdig hsssb hsp1
  -- Step: "Z" fails on the sign char.
  obtain ⟨pos, e, herr⟩ :=
    parseWithDate_string_error p2 _ (o.hours ++ o.minutes)
      (if o.negative then '-' else '+') 'Z'
      { b6 with S := some (Bounded.LE.ofNat' (fieldValue sss * 1000000) _hh2) }
      DateUTCWithMillis.config hsp2
      (by cases o.negative <;> decide)
  have hparser : parser DateUTCWithMillis.string DateUTCWithMillis.config .any
      ⟨c.date.asString ++ "T" ++ tp.time.asString
          ++ ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString),
        (c.date.asString ++ "T" ++ tp.time.asString
          ++ ((match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString)).startPos⟩
      = ParseResult.error pos e := by
    have hpp : parser DateUTCWithMillis.string DateUTCWithMillis.config .any
        = parser.go DateUTCWithMillis.config .any {} DateUTCWithMillis.string := rfl
    have hZ : ("Z" : String) = String.singleton 'Z' := rfl
    rw [hpp, dateUTCWithMillis_string_eq, hgo]
    simp only [go_cons_app, b6, hpar1, hpar2, hZ, herr]
  exact parse_error_of_parser_error DateUTCWithMillis _ pos e hparser

/-! ## Case 1 scaffolding -/

theorem case1_asString {c : DatetimeComponents} (htime : c.time = none) :
    c.asString = c.date.asString := by
  simp only [DatetimeComponents.asString, htime, String.append_empty]

theorem case1_toMillis {c : DatetimeComponents} (htime : c.time = none) :
    c.toMillis = c.date.toMillis := by
  simp only [DatetimeComponents.toMillis, htime, Int.add_zero]

/-- **Case 1: DateOnly form.** `c.time = none`. `DateOnly.parse` is first in the chain, so no
    failure lemmas are needed. -/
theorem case1_value {c : DatetimeComponents} (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = none) :
    ((DateOnly.parse c.asString <|> DateUTC.parse c.asString <|> DateUTCWithMillis.parse c.asString
        <|> DateWithOffset.parse c.asString
        <|> DateWithOffsetAndMillis.parse c.asString).toOption).map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some c.toMillis := by
  have hdsyn : c.date.syntaxWf := hsyn.1
  have hdcon : c.date.constraintsWf := hcon.1
  obtain ⟨zt, hparse, hval⟩ := dateOnly_parse_eq_ok hdsyn hdcon
  rw [case1_asString htime, hparse, except_ok_orElse]
  show (some zt).map _ = _
  have : c.date.toMillis
      = epochDays (fieldValue c.date.year) (fieldValue c.date.month) (fieldValue c.date.day)
        * 86400000 := rfl
  rw [Option.map_some, hval, ← this, ← case1_toMillis htime]

/-- Turn an error into an orElse fall-through. -/
theorem orElse_of_error {α : Type} {x : Except String α} (q : Except String α)
    (h : ∃ e, x = .error e) : (x <|> q) = q := by
  obtain ⟨e, he⟩ := h; rw [he, except_error_orElse]

/-- **Case 2: DateUTC form.** `c.time = some tp`, UTC zone, no millis. DateOnly fails; DateUTC
    succeeds (2nd in chain). -/
theorem case2_value {c : DatetimeComponents} (tp : TimePart)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = none) :
    ((DateOnly.parse c.asString <|> DateUTC.parse c.asString <|> DateUTCWithMillis.parse c.asString
        <|> DateWithOffset.parse c.asString
        <|> DateWithOffsetAndMillis.parse c.asString).toOption).map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some c.toMillis := by
  rw [orElse_of_error _ (dateOnly_parse_error_of_time tp hsyn hcon htime)]
  obtain ⟨zt, hparse, hval⟩ := dateUTC_parse_eq_ok tp hsyn hcon htime hutc hmillis
  rw [hparse, except_ok_orElse]
  show (some zt).map _ = _
  rw [Option.map_some, hval]

/-- **Case 3: DateUTCWithMillis form.** UTC zone, millis present. DateOnly + DateUTC fail;
    DateUTCWithMillis succeeds (3rd in chain). -/
theorem case3_value {c : DatetimeComponents} (tp : TimePart) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = some sss) :
    ((DateOnly.parse c.asString <|> DateUTC.parse c.asString <|> DateUTCWithMillis.parse c.asString
        <|> DateWithOffset.parse c.asString
        <|> DateWithOffsetAndMillis.parse c.asString).toOption).map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some c.toMillis := by
  rw [orElse_of_error _ (dateOnly_parse_error_of_time tp hsyn hcon htime),
      orElse_of_error _ (dateUTC_parse_error_of_millis tp sss hsyn hcon htime hmillis)]
  obtain ⟨zt, hparse, hval⟩ := dateUTCWithMillis_parse_eq_ok tp sss hsyn hcon htime hutc hmillis
  rw [hparse, except_ok_orElse]
  show (some zt).map _ = _
  rw [Option.map_some, hval]

/-- **Case 4: DateWithOffset form.** Offset zone, no millis. DateOnly + DateUTC + DateUTCWithMillis
    fail; DateWithOffset succeeds (4th in chain). -/
theorem case4_value {c : DatetimeComponents} (tp : TimePart) (o : OffsetComponents)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = none) :
    ((DateOnly.parse c.asString <|> DateUTC.parse c.asString <|> DateUTCWithMillis.parse c.asString
        <|> DateWithOffset.parse c.asString
        <|> DateWithOffsetAndMillis.parse c.asString).toOption).map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some c.toMillis := by
  rw [orElse_of_error _ (dateOnly_parse_error_of_time tp hsyn hcon htime),
      orElse_of_error _ (dateUTC_parse_error_of_offset tp o hsyn hcon htime hmillis hzone),
      orElse_of_error _ (dateUTCWithMillis_parse_error_of_offset tp o hsyn hcon htime hmillis hzone)]
  obtain ⟨zt, hparse, hval⟩ := dateWithOffset_parse_eq_ok tp o hsyn hcon htime hzone hmillis
  rw [hparse, except_ok_orElse]
  show (some zt).map _ = _
  rw [Option.map_some, hval]

/-- **Case 5: DateWithOffsetAndMillis form.** Offset zone, millis present. All four earlier
    parsers fail; DateWithOffsetAndMillis succeeds (5th, last). -/
theorem case5_value {c : DatetimeComponents} (tp : TimePart) (o : OffsetComponents) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = some sss) :
    ((DateOnly.parse c.asString <|> DateUTC.parse c.asString <|> DateUTCWithMillis.parse c.asString
        <|> DateWithOffset.parse c.asString
        <|> DateWithOffsetAndMillis.parse c.asString).toOption).map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some c.toMillis := by
  rw [orElse_of_error _ (dateOnly_parse_error_of_time tp hsyn hcon htime),
      orElse_of_error _ (dateUTC_parse_error_of_millis tp sss hsyn hcon htime hmillis),
      orElse_of_error _
        (dateUTCWithMillis_parse_error_of_offsetMillis tp o sss hsyn hcon htime hmillis hzone),
      orElse_of_error _ (dateWithOffset_parse_error_of_millis tp sss hsyn hcon htime hmillis)]
  obtain ⟨zt, hparse, hval⟩ :=
    dateWithOffsetAndMillis_parse_eq_ok tp o sss hsyn hcon htime hzone hmillis
  rw [hparse]
  show (some zt).map _ = _
  rw [Option.map_some, hval]

/-! ## Main theorem: 5-way case split -/

/-- **Format-alternation characterization** (the `stdTime_alternation_value` target). -/
theorem stdTime_alternation_value {c : DatetimeComponents} (hsyn : c.syntaxWf)
    (hcon : c.constraintsWf) :
    ((DateOnly.parse c.asString <|> DateUTC.parse c.asString <|> DateUTCWithMillis.parse c.asString
        <|> DateWithOffset.parse c.asString
        <|> DateWithOffsetAndMillis.parse c.asString).toOption).map
      (fun zt => zt.toTimestamp.toMillisecondsSinceUnixEpoch.toInt)
      = some c.toMillis := by
  match htime : c.time with
  | none => exact case1_value hsyn hcon htime
  | some tp =>
    match hzone : tp.zone, hmillis : tp.millis with
    | Zone.utc, none => exact case2_value tp hsyn hcon htime hzone hmillis
    | Zone.utc, some sss => exact case3_value tp sss hsyn hcon htime hzone hmillis
    | Zone.offset o, none => exact case4_value tp o hsyn hcon htime hzone hmillis
    | Zone.offset o, some sss => exact case5_value tp o sss hsyn hcon htime hzone hmillis
end AlternationProof

/-! ## Forward parse-guard lemmas

`Datetime.parse` applies three Boolean guards (`dateContainsLeapSeconds`, `checkOffsetLen`,
`tzOffsetMinsLt60`) before the format alternation. On a well-formed rendering `c.asString` all three
pass; these lemmas discharge them for `parse_complete`. The offset-minutes guard reduces to the
grammar bound `fieldValue o.minutes ≤ 59`, which requires the `String.Slice`-level fact that
`toNat?` and `isNat` depend only on the character list. -/

/-- `String.Slice.isNat` and `String.Slice.toNat?` see only the underlying character list, so two
    slices with equal `copy.toList` have equal `toNat?`. -/
theorem slice_toNat?_congr (s t : String.Slice) (h : s.copy.toList = t.copy.toList) :
    s.toNat? = t.toNat? := by
  unfold String.Slice.toNat?
  have hisNat : s.isNat = t.isNat := by
    unfold String.Slice.isNat
    simp only [Id.run]
    rw [show (forIn s (none, false) _ : Id _) = forIn s.copy.toList (none, false) _ from
        String.Slice.forIn_eq_forIn_toList,
      show (forIn t (none, false) _ : Id _) = forIn t.copy.toList (none, false) _ from
        String.Slice.forIn_eq_forIn_toList, h]
  have hfold : ∀ (f : Nat → Char → Nat) (i : Nat),
      String.Slice.foldl f i s = String.Slice.foldl f i t := by
    intro f i
    rw [String.Slice.foldl_eq_foldl_toList, String.Slice.foldl_eq_foldl_toList, h]
  rw [hisNat, hfold]

/-- `String.toNat?` depends only on the character list. -/
theorem toNat?_congr (s t : String) (h : s.toList = t.toList) : s.toNat? = t.toNat? := by
  rw [String.toNat?, String.toNat?]
  apply slice_toNat?_congr
  rw [String.copy_toSlice, String.copy_toSlice, h]

/-- On a digit string, `toNat?` succeeds with the grammar's `fieldValue`. -/
theorem toNat?_eq_fieldValue (s : String) (h : IsDigits s) : s.toNat? = some (fieldValue s) := by
  have hsome : (toNat?' s).isSome = true := toNat?'_isSome_of_isDigits h
  rw [← toNat?'_eq_toNat? s h]
  unfold fieldValue
  cases hv : toNat?' s with
  | none => rw [hv] at hsome; simp at hsome
  | some v => rfl

/-- Taking the last two characters of `pre ++ mm`, where `mm` has length two, yields exactly `mm`
    (at the level of character lists). -/
theorem takeEnd_two_toList {pre mm : String} (h2 : mm.length = 2) :
    ((pre ++ mm).takeEnd 2).copy.toList = mm.toList := by
  rw [String.toList_copy_takeEnd, String.toList_append]
  have hml : mm.toList.length = 2 := by rw [String.length_toList, h2]
  rw [List.length_append, hml, Nat.add_sub_cancel, List.drop_left]

/-- A string that ends in a `String.singleton c` character `endsWith` its singleton. -/
theorem endsWith_singleton {pre : String} {c : Char} :
    (pre ++ String.singleton c).endsWith (String.singleton c) = true := by
  rw [String.endsWith_eq_endsWith_toSlice, String.Slice.endsWith_string_iff, String.copy_toSlice]
  exact ⟨pre.toList, by simp⟩

/-- **Timezone-offset-minutes guard.** On a well-formed rendering the `tzOffsetMinsLt60` guard
    passes: date-only strings are length ≤ 10, UTC strings end in `'Z'`, and offset strings end in
    the two-digit minutes field `mm`, which the grammar bounds by `59 < 60`. -/
theorem tzOffsetMinsLt60_asString {c : DatetimeComponents} (hsyn : c.syntaxWf)
    (hcon : c.constraintsWf) :
    tzOffsetMinsLt60 c.asString = true := by
  unfold tzOffsetMinsLt60
  match htime : c.time with
  | none =>
    -- DateOnly: length exactly 10, first disjunct holds.
    obtain ⟨⟨hy, hm, hd⟩, _⟩ := hsyn
    have hlen : c.asString.length = 10 := by
      simp only [DatetimeComponents.asString, htime, DateComponents.asString, String.append_empty,
        String.length_append]
      have hdash : ("-" : String).length = 1 := by decide
      rw [hy.2, hm.2, hd.2, hdash]
    have : (c.asString.length ≤ 10) = True := by simp [hlen]
    simp [this]
  | some tp =>
    match hzone : tp.zone with
    | Zone.utc =>
      -- UTC (with or without millis): string ends in 'Z'.
      have hends : c.asString.endsWith "Z" = true := by
        rw [String.endsWith_eq_endsWith_toSlice, String.Slice.endsWith_string_iff,
          String.copy_toSlice, asString_prefix_tail tp htime, hzone]
        refine ⟨(c.date.asString ++ "T" ++ tp.time.asString
          ++ (match tp.millis with | none => "" | some sss => "." ++ sss)).toList, ?_⟩
        cases htp : tp.millis with
        | none => simp [Zone.asString, String.toList_append]
        | some sss => simp [Zone.asString, String.toList_append]
      rw [hends]; simp
    | Zone.offset o =>
      -- Offset: string ends in the two-digit minutes field `o.minutes`.
      obtain ⟨_, htsyn⟩ := hsyn
      simp only [htime] at htsyn
      obtain ⟨_, _, hzsyn⟩ := htsyn
      rw [hzone] at hzsyn
      obtain ⟨_, homm⟩ := hzsyn
      obtain ⟨_, htcon⟩ := hcon
      simp only [htime] at htcon
      obtain ⟨_, hzcon⟩ := htcon
      rw [hzone] at hzcon
      obtain ⟨_, hommb⟩ := hzcon
      -- c.asString = pre ++ o.minutes
      have hstr : ∃ pre, c.asString = pre ++ o.minutes := by
        rw [asString_prefix_tail tp htime, hzone]
        refine ⟨c.date.asString ++ "T" ++ tp.time.asString
          ++ ((match tp.millis with | none => "" | some sss => "." ++ sss)
              ++ ((if o.negative then "-" else "+") ++ o.hours)), ?_⟩
        simp only [Zone.asString, OffsetComponents.asString, String.append_assoc]
      obtain ⟨pre, hpre⟩ := hstr
      have htne : ((c.asString.takeEnd 2).toNat?) = some (fieldValue o.minutes) := by
        rw [slice_toNat?_congr (c.asString.takeEnd 2) o.minutes.toSlice ?_]
        · show o.minutes.toNat? = _
          rw [toNat?_eq_fieldValue o.minutes homm.1]
        · rw [String.copy_toSlice, hpre]
          exact takeEnd_two_toList homm.2
      rw [htne]
      have : fieldValue o.minutes < 60 := Nat.lt_succ_of_le hommb
      simp [this]

/-- List-level: splitting `pre ++ sep :: suf` on `P`, with `pre` separator-free and `P sep`, yields
    a first segment `acc.reverse ++ pre`. -/
theorem splitOnPPrepend_head {α} (P : α → Bool) (pre suf acc : List α) (sep : α)
    (hsep : P sep = true) (hpre : ∀ x ∈ pre, P x = false) :
    ∃ tl, List.splitOnPPrepend P (pre ++ sep :: suf) acc = (acc.reverse ++ pre) :: tl := by
  induction pre generalizing acc with
  | nil =>
    rw [List.nil_append, List.splitOnPPrepend_cons_eq_if, hsep]
    exact ⟨List.splitOnP P suf, by simp⟩
  | cons a t ih =>
    simp only [List.cons_append]
    have ha : P a = false := hpre a (List.mem_cons.mpr (.inl rfl))
    rw [List.splitOnPPrepend_cons_neg ha]
    obtain ⟨tl, htl⟩ := ih (a :: acc) (fun x hx => hpre x (List.mem_cons.mpr (.inr hx)))
    exact ⟨tl, by rw [htl]; simp [List.reverse_cons, List.append_assoc]⟩

/-- String-level: splitting `pre ++ sep ++ rest` on `P`, with `pre` separator-free and `P sep`,
    puts `pre` at the head of the result. -/
theorem splitToList_head_sep (pre rest : String) (P : Char → Bool) (sep : Char)
    (hsep : P sep = true) (hpre : ∀ ch ∈ pre.toList, P ch = false) :
    ∃ tl, (pre ++ String.singleton sep ++ rest).splitToList P = pre :: tl := by
  rw [String.splitToList_of_valid]
  simp only [String.toList_append, String.toList_singleton, List.append_assoc, List.nil_append,
    List.cons_append]
  rw [List.splitOnP_eq_splitOnPPrepend]
  obtain ⟨tl, htl⟩ := splitOnPPrepend_head P pre.toList rest.toList [] sep hsep hpre
  refine ⟨tl.map String.ofList, ?_⟩
  rw [htl]; simp

/-- The date rendering `year ++ "-" ++ month ++ "-" ++ day` contains no `'T'`. -/
theorem date_no_T {d : DateComponents} (h : d.syntaxWf) :
    ∀ ch ∈ d.asString.toList, decide (ch = 'T') = false := by
  obtain ⟨hy, hm, hd⟩ := h
  have hT : ('T' : Char).isDigit = false := by decide
  intro ch hc
  unfold DateComponents.asString at hc
  have hdash : ("-" : String).toList = ['-'] := rfl
  rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
    hdash] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((((hc | hc) | hc) | hc) | hc)
  · exact not_mem_of_isDigits hy.1 hT ch hc
  · rw [hc]; decide
  · exact not_mem_of_isDigits hm.1 hT ch hc
  · rw [hc]; decide
  · exact not_mem_of_isDigits hd.1 hT ch hc

/-- **Offset-length guard.** On a well-formed rendering the `checkOffsetLen` guard passes:
    splitting on `'T'` separates the date from the time-bearing tail, then splitting the tail on
    an offset sign isolates exactly four digit characters. Date-only and UTC renderings contain no
    offset sign and pass directly. -/
theorem checkComponentLen_asString {c : DatetimeComponents} (hsyn : c.syntaxWf) :
    checkOffsetLen c.asString = true := by
  obtain ⟨hdate, htime⟩ := hsyn
  obtain ⟨hy, hm, hd⟩ := hdate
  have no_sign_of_digits : ∀ {s : String}, IsDigits s →
      ∀ ch ∈ s.toList, (ch == '+' || ch == '-') = false := by
    intro s hs ch hc
    rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
    constructor
    · intro heq
      subst ch
      have := hs.2 '+' hc
      simp at this
    · intro heq
      subst ch
      have := hs.2 '-' hc
      simp at this
  unfold checkOffsetLen
  cases htp : c.time with
  | none =>
    have hstr : c.asString = c.date.asString := by
      unfold DatetimeComponents.asString; rw [htp]; simp
    have hnoT : ∀ ch ∈ c.date.asString.toList, (fun x => x == 'T') ch = false := by
      intro ch hc; have := date_no_T ⟨hy, hm, hd⟩ ch hc; simpa using this
    rw [hstr, splitToList_no_sep _ _ hnoT]
  | some tp =>
    have htp_wf : tp.syntaxWf := by rw [htp] at htime; exact htime
    obtain ⟨htt, htms, htz⟩ := htp_wf
    obtain ⟨hth, htmi, hts⟩ := htt
    have hstr : c.asString = c.date.asString ++ String.singleton 'T' ++ timePartBody tp := by
      unfold DatetimeComponents.asString
      rw [htp]; simp only []
      rw [timePart_asString_eq, show ("T" : String) = String.singleton 'T' from rfl,
        String.append_assoc]
    -- The tail body contains no 'T'.
    have hbody_no_T : ∀ ch ∈ (timePartBody tp).toList, decide (ch = 'T') = false := by
      intro ch hc
      simp only [decide_eq_false_iff_not]; intro heq; subst heq
      unfold timePartBody at hc
      rw [String.toList_append, String.toList_append] at hc
      simp only [List.mem_append] at hc
      have hnd : ∀ {x : String}, IsDigits x → 'T' ∉ x.toList := by
        intro x hx hmem; have := not_mem_of_isDigits hx (sep := 'T') (by decide) 'T' hmem; simp at this
      rcases hc with (hc | hc) | hc
      · unfold TimeComponents.asString at hc
        have hcolon : (":" : String).toList = [':'] := rfl
        rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
          hcolon] at hc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with ((((hc | hc) | hc) | hc) | hc)
        · exact hnd hth.1 hc
        · exact absurd hc (by decide)
        · exact hnd htmi.1 hc
        · exact absurd hc (by decide)
        · exact hnd hts.1 hc
      · cases htms' : tp.millis with
        | none => rw [htms'] at hc; simp [millisChunk] at hc
        | some sss =>
          rw [htms'] at hc htms
          unfold millisChunk at hc
          have hdotL : ("." : String).toList = ['.'] := rfl
          rw [String.toList_append, hdotL] at hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with hc | hc
          · exact absurd hc (by decide)
          · exact hnd htms.1 hc
      · cases htz' : tp.zone with
        | utc =>
          rw [htz'] at hc
          have : (Zone.utc.asString).toList = ['Z'] := rfl
          rw [this] at hc; simp only [List.mem_singleton] at hc; exact absurd hc (by decide)
        | offset o =>
          rw [htz'] at hc htz
          obtain ⟨hoh, hom⟩ := htz
          unfold Zone.asString OffsetComponents.asString at hc
          have hsign : (if o.negative then "-" else "+").toList = [if o.negative then '-' else '+'] := by
            cases o.negative <;> rfl
          rw [String.toList_append, String.toList_append, hsign] at hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with (hc | hc) | hc
          · revert hc; cases o.negative <;> decide
          · exact hnd hoh.1 hc
          · exact hnd hom.1 hc
    rw [hstr, splitToList_eq c.date.asString (timePartBody tp) (· == 'T') 'T' (by simp)
      (by intro ch hc; have := date_no_T ⟨hy, hm, hd⟩ ch hc; simpa using this)
      (by intro ch hc; have := hbody_no_T ch hc; simpa using this)]
    change (match (timePartBody tp).splitToList (fun c => c == '+' || c == '-') with
      | [_] => true
      | [_, offset] => offset.length == 4 && offset.all Char.isDigit
      | _ => false) = true
    have htime_no_sign : ∀ ch ∈ tp.time.asString.toList,
        (fun c => c == '+' || c == '-') ch = false := by
      intro ch hc
      unfold TimeComponents.asString at hc
      have hcolon : (":" : String).toList = [':'] := rfl
      rw [String.toList_append, String.toList_append, String.toList_append,
        String.toList_append, hcolon] at hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((((hc | hc) | hc) | hc) | hc)
      · exact no_sign_of_digits hth.1 ch hc
      · rw [hc]; decide
      · exact no_sign_of_digits htmi.1 ch hc
      · rw [hc]; decide
      · exact no_sign_of_digits hts.1 ch hc
    have hmillis_no_sign : ∀ ch ∈ (millisChunk tp.millis).toList,
        (fun c => c == '+' || c == '-') ch = false := by
      cases hmopt : tp.millis with
      | none => simp [millisChunk]
      | some sss =>
        rw [hmopt] at htms
        intro ch hc
        unfold millisChunk at hc
        have hdot : ("." : String).toList = ['.'] := rfl
        rw [String.toList_append, hdot] at hc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with hc | hc
        · rw [hc]; decide
        · exact no_sign_of_digits htms.1 ch hc
    have hprefix_no_sign : ∀ ch ∈ (tp.time.asString ++ millisChunk tp.millis).toList,
        (fun c => c == '+' || c == '-') ch = false := by
      intro ch hc
      rw [String.toList_append] at hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc
      · exact htime_no_sign ch hc
      · exact hmillis_no_sign ch hc
    cases hzone : tp.zone with
    | utc =>
      have hbody_no_sign : ∀ ch ∈ (timePartBody tp).toList,
          (fun c => c == '+' || c == '-') ch = false := by
        intro ch hc
        have hbody : timePartBody tp =
            (tp.time.asString ++ millisChunk tp.millis) ++ "Z" := by
          unfold timePartBody
          rw [hzone]
          simp [Zone.asString, String.append_assoc]
        rw [hbody, String.toList_append] at hc
        simp only [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hprefix_no_sign ch hc
        · have hz : ("Z" : String).toList = ['Z'] := rfl
          rw [hz] at hc
          simp only [List.mem_singleton] at hc
          rw [hc]
          decide
      rw [splitToList_no_sep _ _ hbody_no_sign]
    | offset o =>
      rw [hzone] at htz
      obtain ⟨hoh, hom⟩ := htz
      have hoff_no_sign : ∀ ch ∈ (o.hours ++ o.minutes).toList,
          (fun c => c == '+' || c == '-') ch = false := by
        intro ch hc
        rw [String.toList_append] at hc
        simp only [List.mem_append] at hc
        rcases hc with hc | hc
        · exact no_sign_of_digits hoh.1 ch hc
        · exact no_sign_of_digits hom.1 ch hc
      have hbody : timePartBody tp =
          (tp.time.asString ++ millisChunk tp.millis) ++
            String.singleton (if o.negative then '-' else '+') ++ (o.hours ++ o.minutes) := by
        unfold timePartBody
        rw [hzone]
        simp only [Zone.asString, OffsetComponents.asString, String.append_assoc]
        cases o.negative <;> rfl
      rw [hbody, splitToList_eq _ _ _ (if o.negative then '-' else '+')
        (by cases o.negative <;> decide) hprefix_no_sign hoff_no_sign]
      have hlen : (o.hours ++ o.minutes).length = 4 := by
        simp [hoh.2, hom.2]
      have hall : (o.hours ++ o.minutes).all Char.isDigit = true := by
        rw [String.all_bool_eq, List.all_eq_true]
        intro ch hc
        rw [String.toList_append] at hc
        simp only [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hoh.1.2 ch hc
        · exact hom.1.2 ch hc
      simp [hlen, hall]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **Built `ZonedDateTime`'s timezone offset.** `DateBuilder.build .any` produces a
    `ZonedDateTime` whose timezone offset is the builder's resolved offset field
    (`O <|> X <|> x <|> Z`, defaulting to zero). -/
theorem build_tz_offset (b : DateBuilder) (zt : Std.Time.ZonedDateTime)
    (h : b.build .any = some zt) :
    zt.timezone.offset = (b.O <|> b.X <|> b.x <|> b.Z).getD TimeZone.Offset.zero := by
  revert h
  unfold DateBuilder.build
  simp only [Option.map_eq_map, Option.map_eq_some_iff]
  rintro ⟨pdt, -, hzt⟩
  subst hzt; rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **Timezone offset of a DateOnly/UTC parse.** When the builder's offset field is unset
    (the zero-offset zone, as in the DateOnly / UTC / UTC-with-millis forms), the parsed
    `ZonedDateTime`'s offset seconds are zero. -/
theorem build_tz_offset_zero (b : DateBuilder) (zt : Std.Time.ZonedDateTime)
    (h : b.build .any = some zt) (hb : b.O = none ∧ b.X = none ∧ b.x = none ∧ b.Z = none) :
    zt.timezone.offset.second.val = 0 := by
  rw [build_tz_offset b zt h, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- **Timezone offset of an offset-form parse.** When the builder's `x` field carries the parsed
    `±(hh·3600+mm·60)` offset (and `O`/`X`/`Z` are unset, as in the two offset forms), the parsed
    `ZonedDateTime`'s offset seconds are exactly that signed magnitude. -/
theorem build_tz_offset_x (b : DateBuilder) (zt : Std.Time.ZonedDateTime) (v : Int)
    (h : b.build .any = some zt)
    (hb : b.O = none ∧ b.X = none ∧ b.x = some (TimeZone.Offset.ofSeconds ⟨v⟩) ∧ b.Z = none) :
    zt.timezone.offset.second.val = v := by
  rw [build_tz_offset b zt h, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
  rfl

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- DateOnly parse: the timezone offset is zero (the builder sets no offset field). -/
theorem dateOnly_parse_tz {d : DateComponents} (hsyn : d.syntaxWf) (hcon : d.constraintsWf) :
    ∃ zt, DateOnly.parse d.asString = .ok zt ∧ zt.timezone.offset.second.val = 0 := by
  obtain ⟨hm, hd, hgo⟩ := parseWithDate_dateOnly DateOnly.config hsyn hcon
  obtain ⟨zt, hbuild, _⟩ := build_dateOnly_value hsyn hcon hm hd _ rfl
  refine ⟨zt, ?_, build_tz_offset_zero _ zt hbuild ⟨rfl, rfl, rfl, rfl⟩⟩
  have hp : parser DateOnly.string DateOnly.config .any
      = parser.go DateOnly.config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2})] := rfl
  have happ :
      (parser DateOnly.string DateOnly.config .any <* eof) ⟨d.asString, d.asString.startPos⟩
        = ParseResult.success ⟨d.asString, d.asString.endPos⟩ zt := by
    rw [seqLeft_app, hp, hgo, go_nil_some DateOnly.config _ _ zt hbuild]
    simp only []; rw [eof_endPos]
  show (DateOnly.parse d.asString) = .ok zt
  unfold Std.Time.GenericFormat.parse Std.Internal.Parsec.String.Parser.run
  rw [happ]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- DateUTC parse: the timezone offset is zero. -/
theorem dateUTC_parse_tz {c : DatetimeComponents} (tp : TimePart)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = none) :
    ∃ zt, DateUTC.parse c.asString = .ok zt ∧ zt.timezone.offset.second.val = 0 := by
  obtain ⟨hm, hd, hh, hmin, hsec, hgo⟩ :=
    parseWithDate_dateUTC tp DateUTC.config rfl hsyn hcon htime hutc hmillis
  obtain ⟨zt, hbuild, _⟩ :=
    build_dateUTC_value tp hsyn hcon htime hutc hmillis hm hd hh hmin hsec _ rfl
  refine ⟨zt, ?_, build_tz_offset_zero _ zt hbuild ⟨rfl, rfl, rfl, rfl⟩⟩
  have hp : parser DateUTC.string DateUTC.config .any
      = parser.go DateUTC.config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2}), .string "T",
           .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
           .string ":", .modifier (.s {padding := 2}), .string "Z"] := rfl
  have happ :
      (parser DateUTC.string DateUTC.config .any <* eof) ⟨c.asString, c.asString.startPos⟩
        = ParseResult.success ⟨c.asString, c.asString.endPos⟩ zt := by
    rw [seqLeft_app, hp, hgo, go_nil_some DateUTC.config _ _ zt hbuild]
    simp only []; rw [eof_endPos]
  show (DateUTC.parse c.asString) = .ok zt
  unfold Std.Time.GenericFormat.parse Std.Internal.Parsec.String.Parser.run
  rw [happ]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- DateUTCWithMillis parse: the timezone offset is zero. -/
theorem dateUTCWithMillis_parse_tz {c : DatetimeComponents} (tp : TimePart) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hutc : tp.zone = Zone.utc) (hmillis : tp.millis = some sss) :
    ∃ zt, DateUTCWithMillis.parse c.asString = .ok zt ∧ zt.timezone.offset.second.val = 0 := by
  obtain ⟨hm, hd, hh, hmin, hsec, hms, hgo⟩ :=
    parseWithDate_dateUTCWithMillis tp sss DateUTCWithMillis.config rfl hsyn hcon htime hutc hmillis
  obtain ⟨zt, hbuild, _⟩ :=
    build_dateUTCWithMillis_value tp sss hsyn hcon htime hutc hmillis hm hd hh hmin hsec hms _ rfl
  refine ⟨zt, ?_, build_tz_offset_zero _ zt hbuild ⟨rfl, rfl, rfl, rfl⟩⟩
  have hp : parser DateUTCWithMillis.string DateUTCWithMillis.config .any
      = parser.go DateUTCWithMillis.config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2}), .string "T",
           .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
           .string ":", .modifier (.s {padding := 2}), .string ".",
           .modifier (.S (.truncated 3)), .string "Z"] := rfl
  have happ :
      (parser DateUTCWithMillis.string DateUTCWithMillis.config .any <* eof)
          ⟨c.asString, c.asString.startPos⟩
        = ParseResult.success ⟨c.asString, c.asString.endPos⟩ zt := by
    rw [seqLeft_app, hp, hgo, go_nil_some DateUTCWithMillis.config _ _ zt hbuild]
    simp only []; rw [eof_endPos]
  show (DateUTCWithMillis.parse c.asString) = .ok zt
  unfold Std.Time.GenericFormat.parse Std.Internal.Parsec.String.Parser.run
  rw [happ]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- DateWithOffset parse: the timezone offset is the parsed `±(hh·3600+mm·60)`, bounded by `hcon`. -/
theorem dateWithOffset_parse_tz {c : DatetimeComponents} (tp : TimePart) (o : OffsetComponents)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = none) :
    ∃ zt, DateWithOffset.parse c.asString = .ok zt ∧
      zt.timezone.offset.second.val
        = ((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
            * (if o.negative then -1 else 1) := by
  obtain ⟨hm, hd, hh, hmin, hsec, hgo⟩ :=
    parseWithDate_dateWithOffset tp o DateWithOffset.config rfl hsyn hcon htime hzone hmillis
  obtain ⟨zt, hbuild, _⟩ :=
    build_dateWithOffset_value tp o hsyn hcon htime hzone hmillis hm hd hh hmin hsec _ rfl
  have htz : zt.timezone.offset.second.val
      = ((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
          * (if o.negative then -1 else 1) :=
    build_tz_offset_x _ zt _ hbuild ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨zt, ?_, htz⟩
  have hp : parser DateWithOffset.string DateWithOffset.config .any
      = parser.go DateWithOffset.config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2}), .string "T",
           .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
           .string ":", .modifier (.s {padding := 2}), .modifier (.x .hourMinute)] := rfl
  have happ :
      (parser DateWithOffset.string DateWithOffset.config .any <* eof)
          ⟨c.asString, c.asString.startPos⟩
        = ParseResult.success ⟨c.asString, c.asString.endPos⟩ zt := by
    rw [seqLeft_app, hp, hgo, go_nil_some DateWithOffset.config _ _ zt hbuild]
    simp only []; rw [eof_endPos]
  show (DateWithOffset.parse c.asString) = .ok zt
  unfold Std.Time.GenericFormat.parse Std.Internal.Parsec.String.Parser.run
  rw [happ]

open Std.Internal.Parsec Std.Internal.Parsec.String Std.Time Std.Time.Internal Std.Time.GenericFormat in
/-- DateWithOffsetAndMillis parse: the timezone offset is the parsed `±(hh·3600+mm·60)`. -/
theorem dateWithOffsetAndMillis_parse_tz {c : DatetimeComponents} (tp : TimePart)
    (o : OffsetComponents) (sss : String)
    (hsyn : c.syntaxWf) (hcon : c.constraintsWf)
    (htime : c.time = some tp) (hzone : tp.zone = Zone.offset o) (hmillis : tp.millis = some sss) :
    ∃ zt, DateWithOffsetAndMillis.parse c.asString = .ok zt ∧
      zt.timezone.offset.second.val
        = ((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
            * (if o.negative then -1 else 1) := by
  obtain ⟨hm, hd, hh, hmin, hsec, hms, hgo⟩ :=
    parseWithDate_dateWithOffsetAndMillis tp o sss DateWithOffsetAndMillis.config rfl hsyn hcon
      htime hzone hmillis
  obtain ⟨zt, hbuild, _⟩ :=
    build_dateWithOffsetAndMillis_value tp o sss hsyn hcon htime hzone hmillis hm hd hh hmin hsec
      hms _ rfl
  have htz : zt.timezone.offset.second.val
      = ((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
          * (if o.negative then -1 else 1) :=
    build_tz_offset_x _ zt _ hbuild ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨zt, ?_, htz⟩
  have hp : parser DateWithOffsetAndMillis.string DateWithOffsetAndMillis.config .any
      = parser.go DateWithOffsetAndMillis.config .any {}
          [.modifier (.y .fourDigit), .string "-", .modifier (.M (.inl {padding := 2})),
           .string "-", .modifier (.d {padding := 2}), .string "T",
           .modifier (.H {padding := 2}), .string ":", .modifier (.m {padding := 2}),
           .string ":", .modifier (.s {padding := 2}), .string ".",
           .modifier (.S (.truncated 3)), .modifier (.x .hourMinute)] := rfl
  have happ :
      (parser DateWithOffsetAndMillis.string DateWithOffsetAndMillis.config .any <* eof)
          ⟨c.asString, c.asString.startPos⟩
        = ParseResult.success ⟨c.asString, c.asString.endPos⟩ zt := by
    rw [seqLeft_app, hp, hgo, go_nil_some DateWithOffsetAndMillis.config _ _ zt hbuild]
    simp only []; rw [eof_endPos]
  show (DateWithOffsetAndMillis.parse c.asString) = .ok zt
  unfold Std.Time.GenericFormat.parse Std.Internal.Parsec.String.Parser.run
  rw [happ]

/-- **Offset-range side condition.** The `< MAX_OFFSET_SECONDS` check that `Datetime.parse` applies
    to the parsed zone always passes on a well-formed string, because the grammar bounds offsets to
    `±23:59` (`|hh·3600 + mm·60| ≤ 86340 < 86400`). Needs `hcon` for the numeric bounds `hh ≤ 23`,
    `mm ≤ 59`; `hsyn` alone (fixed-digit widths) would only give `hh, mm ≤ 99`. -/
theorem offset_lt_max_of_syntaxWf {c : DatetimeComponents} (hsyn : c.syntaxWf)
    (hcon : c.constraintsWf)
    (zt : Std.Time.ZonedDateTime)
    (hzt : (DateOnly.parse c.asString <|> DateUTC.parse c.asString
        <|> DateUTCWithMillis.parse c.asString <|> DateWithOffset.parse c.asString
        <|> DateWithOffsetAndMillis.parse c.asString).toOption = some zt) :
    zt.timezone.offset.second.val.natAbs < MAX_OFFSET_SECONDS := by
  -- Identify which parser succeeds (as in `stdTime_alternation_value`) and read off its offset:
  -- either zero (DateOnly/UTC/UTCmillis) or `±(hh·3600+mm·60)` bounded by `hcon` (offset forms).
  have hztval : zt.timezone.offset.second.val = 0 ∨
      (∃ (o : OffsetComponents), fieldValue o.hours ≤ 23 ∧ fieldValue o.minutes ≤ 59 ∧
        zt.timezone.offset.second.val
          = ((fieldValue o.hours : Int) * 3600 + (fieldValue o.minutes : Int) * 60)
              * (if o.negative then -1 else 1)) := by
    match htime : c.time with
    | none =>
      obtain ⟨zt', hparse, htz⟩ := dateOnly_parse_tz hsyn.1 hcon.1
      rw [case1_asString htime, hparse, except_ok_orElse] at hzt
      rw [Except.toOption] at hzt; injection hzt with heq; subst heq; exact Or.inl htz
    | some tp =>
      have hzcon : tp.zone.constraintsWf := by
        have := hcon.2; rw [htime] at this; exact this.2
      match hzone : tp.zone, hmillis : tp.millis with
      | Zone.utc, none =>
        obtain ⟨zt', hparse, htz⟩ := dateUTC_parse_tz tp hsyn hcon htime hzone hmillis
        rw [orElse_of_error _ (dateOnly_parse_error_of_time tp hsyn hcon htime),
          hparse, except_ok_orElse] at hzt
        rw [Except.toOption] at hzt; injection hzt with heq; subst heq; exact Or.inl htz
      | Zone.utc, some sss =>
        obtain ⟨zt', hparse, htz⟩ := dateUTCWithMillis_parse_tz tp sss hsyn hcon htime hzone hmillis
        rw [orElse_of_error _ (dateOnly_parse_error_of_time tp hsyn hcon htime),
          orElse_of_error _ (dateUTC_parse_error_of_millis tp sss hsyn hcon htime hmillis),
          hparse, except_ok_orElse] at hzt
        rw [Except.toOption] at hzt; injection hzt with heq; subst heq; exact Or.inl htz
      | Zone.offset o, none =>
        rw [hzone] at hzcon
        obtain ⟨hohb, homb⟩ := hzcon
        obtain ⟨zt', hparse, htz⟩ := dateWithOffset_parse_tz tp o hsyn hcon htime hzone hmillis
        rw [orElse_of_error _ (dateOnly_parse_error_of_time tp hsyn hcon htime),
          orElse_of_error _ (dateUTC_parse_error_of_offset tp o hsyn hcon htime hmillis hzone),
          orElse_of_error _
            (dateUTCWithMillis_parse_error_of_offset tp o hsyn hcon htime hmillis hzone),
          hparse, except_ok_orElse] at hzt
        rw [Except.toOption] at hzt; injection hzt with heq; subst heq
        exact Or.inr ⟨o, hohb, homb, htz⟩
      | Zone.offset o, some sss =>
        rw [hzone] at hzcon
        obtain ⟨hohb, homb⟩ := hzcon
        obtain ⟨zt', hparse, htz⟩ :=
          dateWithOffsetAndMillis_parse_tz tp o sss hsyn hcon htime hzone hmillis
        rw [orElse_of_error _ (dateOnly_parse_error_of_time tp hsyn hcon htime),
          orElse_of_error _ (dateUTC_parse_error_of_millis tp sss hsyn hcon htime hmillis),
          orElse_of_error _
            (dateUTCWithMillis_parse_error_of_offsetMillis tp o sss hsyn hcon htime hmillis hzone),
          orElse_of_error _ (dateWithOffset_parse_error_of_millis tp sss hsyn hcon htime hmillis),
          hparse] at hzt
        rw [Except.toOption] at hzt; injection hzt with heq; subst heq
        exact Or.inr ⟨o, hohb, homb, htz⟩
  -- Bound the offset value: |off| ≤ 23·3600 + 59·60 = 86340 < 86400 = MAX_OFFSET_SECONDS.
  rcases hztval with hz | ⟨o, hohb, homb, hoff⟩
  · rw [hz]; decide
  · -- The signed magnitude `hh·3600 + mm·60` is `hcon`-bounded by `23·3600 + 59·60 = 86340`;
    -- `omega` handles the `natAbs`/cast arithmetic directly once the sign `if` is resolved.
    rw [MAX_OFFSET_SECONDS, hoff]
    cases o.negative with
    | false => rw [if_neg (by decide), Int.mul_one]; omega
    | true => rw [if_pos rfl, Int.mul_neg, Int.mul_one, Int.natAbs_neg]; omega

/-- **`computeValue` equals the components' value.** Pure book-keeping bridging the two views of the
    value: `computeValue str` (the structural re-parse) and `c.toMillis` (the record's value), for
    `str = c.asString`. This one is parser-independent and provable from `parseComponents_asString`
    once the `.map DatetimeComponents.toMillis` is unfolded. -/
theorem computeValue_asString {c : DatetimeComponents} (hsyn : c.syntaxWf) :
    computeValue c.asString = some c.toMillis := by
  unfold computeValue
  rw [parseComponents_asString hsyn]
  rfl

/-! ## Leap-seconds guard

`dateContainsLeapSeconds str` reads the two bytes at positions 17 and 18 (the seconds field of a
`Date 'T' Time …` rendering, whose prefix `yyyy-MM-ddThh:mm:` is exactly 17 ASCII bytes) and rejects
`"…60…"`. On a well-formed rendering it always returns `false`: date-only strings are too short
(length 10 < 20), and for time-bearing strings the grammar bounds the seconds field by `59`, so it
is never `"60"`. -/

/-- An ASCII digit occupies exactly one UTF-8 byte. -/
theorem isDigit_utf8Size_one {c : Char} (h : c.isDigit = true) : c.utf8Size = 1 := by
  rw [Char.utf8Size_eq_one_iff]
  unfold Char.isDigit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h9 : ('9'.val : UInt32) ≤ 127 := by decide
  exact Trans.trans h.2 h9

/-- Every character of a digit string occupies one UTF-8 byte. -/
theorem isDigits_utf8Size_one {s : String} (h : IsDigits s) :
    ∀ c ∈ s.toList, c.utf8Size = 1 :=
  fun c hc => isDigit_utf8Size_one (h.2 c hc)

/-- `utf8GetAux?` skips over an all-ASCII (one-byte-per-char) prefix `l1`: reading at byte index `n`
    past the prefix is the same as reading `l2` starting at byte index `i.byteIdx + l1.length`. -/
theorem utf8GetAux?_ascii_skip (l2 : List Char) (n : Nat) :
    ∀ (l1 : List Char) (i : String.Pos.Raw),
      (∀ c ∈ l1, c.utf8Size = 1) →
      i.byteIdx + l1.length ≤ n →
      String.Pos.Raw.utf8GetAux? (l1 ++ l2) i ⟨n⟩
        = String.Pos.Raw.utf8GetAux? l2 ⟨i.byteIdx + l1.length⟩ ⟨n⟩ := by
  intro l1
  induction l1 with
  | nil => intro i _ _; simp
  | cons c cs ih =>
    intro i hall hle
    rw [List.cons_append, String.Pos.Raw.utf8GetAux?]
    have hc1 : c.utf8Size = 1 := hall c List.mem_cons_self
    have hne : ¬ (i = (⟨n⟩ : String.Pos.Raw)) := by
      simp only [List.length_cons, String.Pos.Raw.ext_iff] at *; omega
    rw [if_neg hne]
    have hstep : i + c = (⟨i.byteIdx + 1⟩ : String.Pos.Raw) := by
      rw [String.Pos.Raw.add_char_eq, hc1]
    rw [hstep]
    have hih := ih ⟨i.byteIdx + 1⟩ (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      (by simp only [List.length_cons] at hle ⊢; omega)
    rw [hih]
    congr 1
    simp only [List.length_cons, String.Pos.Raw.mk.injEq]; omega

/-- On a character list `pre ++ a :: b :: rest` with a 17-char all-ASCII prefix `pre`, positions 17
    and 18 read off `a` and `b`. -/
theorem utf8GetAux?_pair (pre : List Char) (a b : Char) (rest : List Char)
    (hlen : pre.length = 17) (hpre : ∀ c ∈ pre, c.utf8Size = 1) (ha : a.utf8Size = 1) :
    String.Pos.Raw.utf8GetAux? (pre ++ a :: b :: rest) 0 ⟨17⟩ = some a ∧
    String.Pos.Raw.utf8GetAux? (pre ++ a :: b :: rest) 0 ⟨18⟩ = some b := by
  have h17 := utf8GetAux?_ascii_skip (a :: b :: rest) 17 pre 0 hpre (by simp [hlen])
  have h18 := utf8GetAux?_ascii_skip (a :: b :: rest) 18 pre 0 hpre (by simp [hlen])
  simp only [String.Pos.Raw.byteIdx_zero, Nat.zero_add, hlen] at h17 h18
  refine ⟨?_, ?_⟩
  · rw [h17, String.Pos.Raw.utf8GetAux?, if_pos rfl]
  · rw [h18, String.Pos.Raw.utf8GetAux?]
    have hne : ¬ ((⟨17⟩ : String.Pos.Raw) = (⟨18⟩ : String.Pos.Raw)) := by
      simp [String.Pos.Raw.ext_iff]
    rw [if_neg hne]
    have hstep : (⟨17⟩ : String.Pos.Raw) + a = (⟨18⟩ : String.Pos.Raw) := by
      rw [String.Pos.Raw.add_char_eq, ha]
    rw [hstep, String.Pos.Raw.utf8GetAux?, if_pos rfl]

/-- A time-bearing rendering splits as (17-char prefix `yyyy-MM-ddThh:mm:`) ++ seconds ++ tail. -/
theorem asString_seconds_split {c : DatetimeComponents} {tp : TimePart} (htime : c.time = some tp) :
    ∃ tail, c.asString = (c.date.asString ++ "T" ++ tp.time.hours ++ ":" ++ tp.time.minutes ++ ":")
      ++ tp.time.seconds ++ tail := by
  refine ⟨(match tp.millis with | none => "" | some sss => "." ++ sss) ++ tp.zone.asString, ?_⟩
  rw [asString_prefix_tail tp htime]
  simp only [TimeComponents.asString, String.append_assoc]

/-- **Leap-seconds guard.** On a well-formed rendering the `dateContainsLeapSeconds` guard is
    `false`: date-only strings are length 10 < 20, and for time-bearing strings the seconds field
    (positions 17–18) is bounded by 59 by the grammar's constraints, so it is never `"60"`. -/
theorem dateContainsLeapSeconds_asString {c : DatetimeComponents} (hsyn : c.syntaxWf)
    (hcon : c.constraintsWf) :
    dateContainsLeapSeconds c.asString = false := by
  unfold dateContainsLeapSeconds
  obtain ⟨⟨hy, hm, hd⟩, htsyn⟩ := hsyn
  match htime : c.time with
  | none =>
    -- DateOnly: length exactly 10, first conjunct `10 >= 20` is false.
    have hlen : c.asString.length = 10 := by
      simp only [DatetimeComponents.asString, htime, DateComponents.asString, String.append_empty,
        String.length_append]
      have hdash : ("-" : String).length = 1 := by decide
      rw [hy.2, hm.2, hd.2, hdash]
    simp only [hlen, ge_iff_le, Nat.reduceLeDiff, decide_false, Bool.false_and]
  | some tp =>
    -- Time-bearing: read positions 17/18 as the two seconds digits.
    simp only [htime] at htsyn
    obtain ⟨⟨_hth, _htmi, hts⟩, _, _⟩ := htsyn
    obtain ⟨_, htcon⟩ := hcon
    simp only [htime] at htcon
    obtain ⟨⟨_, _, hsecb⟩, _⟩ := htcon
    -- Split the rendering as `pre ++ seconds ++ tail`, `pre` the 17-byte ASCII prefix.
    obtain ⟨tail, hcstr0⟩ := asString_seconds_split htime
    obtain ⟨pre, hpredef, hcstr⟩ :
        ∃ pre, pre = c.date.asString ++ "T" ++ tp.time.hours ++ ":" ++ tp.time.minutes ++ ":"
          ∧ c.asString = pre ++ tp.time.seconds ++ tail := ⟨_, rfl, hcstr0⟩
    -- `pre.length = 17`.
    have hpre_len : pre.length = 17 := by
      simp only [hpredef, DateComponents.asString, String.length_append]
      have hdash : ("-" : String).length = 1 := by decide
      have hT : ("T" : String).length = 1 := by decide
      have hcolon : (":" : String).length = 1 := by decide
      rw [hy.2, hm.2, hd.2, hdash, hT, _hth.2, _htmi.2, hcolon]
    -- Every character of `pre` is one UTF-8 byte.
    have hpre_utf8 : ∀ ch ∈ pre.toList, ch.utf8Size = 1 := by
      intro ch hc
      simp only [hpredef, DateComponents.asString, String.toList_append] at hc
      have hdash : ("-" : String).toList = ['-'] := rfl
      have hT : ("T" : String).toList = ['T'] := rfl
      have hcolon : (":" : String).toList = [':'] := rfl
      rw [hdash, hT, hcolon] at hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (((((((((hc | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc)
      · exact isDigit_utf8Size_one (hy.1.2 ch hc)
      · rw [hc]; decide
      · exact isDigit_utf8Size_one (hm.1.2 ch hc)
      · rw [hc]; decide
      · exact isDigit_utf8Size_one (hd.1.2 ch hc)
      · rw [hc]; decide
      · exact isDigit_utf8Size_one (_hth.1.2 ch hc)
      · rw [hc]; decide
      · exact isDigit_utf8Size_one (_htmi.1.2 ch hc)
      · rw [hc]; decide
    -- `seconds` is two digits `[s0, s1]`.
    have hsec_len : tp.time.seconds.toList.length = 2 := by
      rw [String.length_toList, hts.2]
    obtain ⟨s0, s1, hsec_eq⟩ : ∃ s0 s1, tp.time.seconds.toList = [s0, s1] := by
      match hl : tp.time.seconds.toList with
      | [a, b] => exact ⟨a, b, rfl⟩
      | [] => rw [hl] at hsec_len; simp at hsec_len
      | [_] => rw [hl] at hsec_len; simp at hsec_len
      | _ :: _ :: _ :: _ => rw [hl] at hsec_len; simp at hsec_len
    -- `c.asString.toList = pre.toList ++ s0 :: s1 :: tail.toList`.
    have hlist : c.asString.toList = pre.toList ++ (s0 :: s1 :: tail.toList) := by
      rw [hcstr, String.toList_append, String.toList_append, hsec_eq]
      simp only [hpredef, List.append_assoc, List.cons_append, List.nil_append]
    -- Read off positions 17 and 18.
    have hs0dig : s0.isDigit = true := by
      apply hts.1.2; rw [hsec_eq]; exact List.mem_cons_self
    obtain ⟨hg17, hg18⟩ := utf8GetAux?_pair pre.toList s0 s1 tail.toList hpre_len hpre_utf8
      (isDigit_utf8Size_one hs0dig)
    have hget17 : String.Pos.Raw.get? c.asString ⟨17⟩ = some s0 := by
      rw [String.Pos.Raw.get?, hlist]; exact hg17
    have hget18 : String.Pos.Raw.get? c.asString ⟨18⟩ = some s1 := by
      rw [String.Pos.Raw.get?, hlist]; exact hg18
    -- The two-digit conjunct is false: otherwise `seconds = "60"`, contradicting `≤ 59`.
    have hkey : (String.Pos.Raw.get? c.asString ⟨17⟩ == some '6'
        && String.Pos.Raw.get? c.asString ⟨18⟩ == some '0') = false := by
      rw [hget17, hget18]
      rcases Bool.eq_false_or_eq_true (some s0 == some '6' && some s1 == some '0') with h | h
      · exfalso
        simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at h
        obtain ⟨hs0, hs1⟩ := h
        have hfv : fieldValue tp.time.seconds = 60 := by
          rw [fieldValue_isDigits _ hts.1, hsec_eq, hs0, hs1]; decide
        omega
      · exact h
    rw [Bool.and_assoc, hkey, Bool.and_false]

/-! ## Int64-range bound for the datetime value

The grammar bounds a datetime to 4-digit years and `±23:59` offsets, so `toMillis` always fits in
`Int64`. We prove this by bounding `epochDays` (the Hinnant forward algorithm) and then the linear
`toMillis` combination. `omega` treats `Int.tdiv`/`Int.tmod` as opaque, so each `tdiv` site is fed the
Euclidean identity `Int.mul_tdiv_add_tmod` plus `tmod` sign/magnitude facts. -/

/-- The era-and-year-of-era contribution of `epochDays` for a nonnegative shifted year `yp ≤ 9999`.
    Feeds `omega` the `tdiv`/`tmod` facts for the `/400`, `/4`, and `/100` divisions. -/
theorem epochDays_era_block (yp : Int) (hlb : 0 ≤ yp) (hub : yp ≤ 9999) :
    -3 ≤ yp.tdiv 400 * 146097 +
        ((yp - yp.tdiv 400 * 400) * 365 + (yp - yp.tdiv 400 * 400).tdiv 4
          - (yp - yp.tdiv 400 * 400).tdiv 100) ∧
      yp.tdiv 400 * 146097 +
        ((yp - yp.tdiv 400 * 400) * 365 + (yp - yp.tdiv 400 * 400).tdiv 4
          - (yp - yp.tdiv 400 * 400).tdiv 100) ≤ 3652062 := by
  have he1 := Int.mul_tdiv_add_tmod yp 400
  have he2 : 0 ≤ yp.tmod 400 := Int.tmod_nonneg 400 hlb
  have he3 : yp.tmod 400 < 400 := Int.tmod_lt_of_pos yp (by omega)
  have hyoe_lb : 0 ≤ yp - yp.tdiv 400 * 400 := by omega
  have hyoe_ub : yp - yp.tdiv 400 * 400 ≤ 399 := by omega
  have hy4_1 := Int.mul_tdiv_add_tmod (yp - yp.tdiv 400 * 400) 4
  have hy4_2 : 0 ≤ (yp - yp.tdiv 400 * 400).tmod 4 := Int.tmod_nonneg 4 hyoe_lb
  have hy4_3 : (yp - yp.tdiv 400 * 400).tmod 4 < 4 := Int.tmod_lt_of_pos _ (by omega)
  have hy100_1 := Int.mul_tdiv_add_tmod (yp - yp.tdiv 400 * 400) 100
  have hy100_2 : 0 ≤ (yp - yp.tdiv 400 * 400).tmod 100 := Int.tmod_nonneg 100 hyoe_lb
  have hy100_3 : (yp - yp.tdiv 400 * 400).tmod 100 < 100 := Int.tmod_lt_of_pos _ (by omega)
  have hera_lb : 0 ≤ yp.tdiv 400 := by omega
  have hera_ub : yp.tdiv 400 ≤ 24 := by omega
  omega

/-- `epochDays` is bounded for any grammar-legal `(y, m, d)` with `y ≤ 9999`, `1 ≤ m ≤ 12`,
    `1 ≤ d ≤ 31`. The endpoints `epochDays 0 1 1 = -719528` and `epochDays 9999 12 31 = 2932896`
    are tight on the low side; the high bound is loosened to `2933000` (gap 104 days) to keep the
    `omega` combination robust. -/
theorem epochDays_bounds {y m d : Nat} (hy : y ≤ 9999) (hm : 1 ≤ m ∧ m ≤ 12)
    (hd : 1 ≤ d ∧ d ≤ 31) :
    -719528 ≤ epochDays y m d ∧ epochDays y m d ≤ 2933000 := by
  obtain ⟨hm1, hm2⟩ := hm
  obtain ⟨hd1, hd2⟩ := hd
  simp only [epochDays]
  -- Day-of-year divisor: the `/5` argument is nonnegative in every month branch.
  have hdoy_arg : (0 : Int) ≤ 153 * ((m : Int) + (if (m : Int) > 2 then -3 else 9)) + 2 := by
    split <;> (push_cast; omega)
  have hdoy1 := Int.mul_tdiv_add_tmod (153 * ((m : Int) + (if (m : Int) > 2 then -3 else 9)) + 2) 5
  have hdoy2 : 0 ≤ (153 * ((m : Int) + (if (m : Int) > 2 then -3 else 9)) + 2).tmod 5 :=
    Int.tmod_nonneg 5 hdoy_arg
  have hdoy3 : (153 * ((m : Int) + (if (m : Int) > 2 then -3 else 9)) + 2).tmod 5 < 5 :=
    Int.tmod_lt_of_pos _ (by omega)
  have hdoy_ub : 153 * ((m : Int) + (if (m : Int) > 2 then -3 else 9)) + 2 ≤ 1685 := by
    split <;> (push_cast; omega)
  -- Case on the era sign. When `y' ≥ 0` the era divisions are covered by `epochDays_era_block`.
  by_cases hyc : ((if (m:Int) > 2 then (y:Int) else (y:Int) - 1)) ≥ 0
  · rw [if_pos hyc]
    have hblk := epochDays_era_block (if (m:Int) > 2 then (y:Int) else (y:Int) - 1) hyc
      (by split <;> (push_cast; omega))
    omega
  · -- `y' < 0` forces `m ≤ 2` and `y = 0`, so `y' = -1` and the era terms are concrete.
    replace hyc : (if (m:Int) > 2 then (y:Int) else (y:Int) - 1) < 0 := Int.not_le.mp hyc
    have hm2' : ¬ (m:Int) > 2 := by
      intro h; rw [if_pos h] at hyc; push_cast at hyc; omega
    have hy0 : y = 0 := by rw [if_neg hm2'] at hyc; push_cast at hyc; omega
    subst hy0
    rw [if_neg hm2']
    push_cast
    omega

/-- `daysInMonth` is at most `31` for any year/month. -/
theorem daysInMonth_le_31 (y m : Nat) : daysInMonth y m ≤ 31 := by
  unfold daysInMonth
  split
  · omega
  · split
    · split <;> omega
    · omega

/-- A constraint-well-formed zone contributes at most `±86340` seconds (`23:59` in seconds). -/
theorem offsetSeconds_bound {z : Zone} (h : z.constraintsWf) :
    -86340 ≤ z.offsetSeconds ∧ z.offsetSeconds ≤ 86340 := by
  cases z with
  | utc => simp only [Zone.offsetSeconds]; omega
  | offset o =>
    simp only [Zone.constraintsWf] at h
    simp only [Zone.offsetSeconds, OffsetComponents.seconds]
    obtain ⟨hh, hm⟩ := h
    split <;> omega

/-- A well-formed datetime's epoch-millisecond value fits in a small range. The endpoints are
    `0000-01-01T00:00:00+2359` (`-62167305540000`) and `9999-12-31T23:59:59.999-2359`; the upper
    bound is loosened to `253411372739999` to absorb the `epochDays` slack (104 days × 86400000 ms),
    still far inside `Int64`. -/
theorem toMillis_range {c : DatetimeComponents} (hsyn : c.syntaxWf) (hcon : c.constraintsWf) :
    -62167305540000 ≤ c.toMillis ∧ c.toMillis ≤ 253411372739999 := by
  obtain ⟨hdsyn, htsyn⟩ := hsyn
  obtain ⟨hdcon, htcon⟩ := hcon
  obtain ⟨hysyn, hmsyn, hdsyn'⟩ := hdsyn
  have hyle : fieldValue c.date.year ≤ 9999 := fieldValue_le_9999 hysyn
  simp only [DateComponents.constraintsWf] at hdcon
  obtain ⟨hm1, hm2, hd1, hd2⟩ := hdcon
  have hdle : fieldValue c.date.day ≤ 31 := Nat.le_trans hd2 (daysInMonth_le_31 _ _)
  have hepoch := epochDays_bounds (y := fieldValue c.date.year) (m := fieldValue c.date.month)
    (d := fieldValue c.date.day) hyle ⟨hm1, hm2⟩ ⟨hd1, hdle⟩
  simp only [DatetimeComponents.toMillis, DateComponents.toMillis]
  cases htime : c.time with
  | none => simp only []; omega
  | some tp =>
    rw [htime] at htsyn htcon
    simp only [TimePart.syntaxWf] at htsyn
    obtain ⟨httsyn, hmillissyn, hzonesyn⟩ := htsyn
    simp only [TimePart.constraintsWf] at htcon
    obtain ⟨httcon, hzonecon⟩ := htcon
    obtain ⟨hhcon, hmincon, hsccon⟩ := httcon
    have hoff := offsetSeconds_bound (z := tp.zone) hzonecon
    obtain ⟨hoff_lb, hoff_ub⟩ := hoff
    simp only [TimePart.toMillis]
    cases hmm : tp.millis with
    | none => simp only []; omega
    | some sss =>
      rw [hmm] at hmillissyn
      simp only [IsWfOptionalMillis] at hmillissyn
      have hsssb := fieldValue_le_999 hmillissyn
      simp only []
      omega

/-- Corollary: a well-formed datetime's value never overflows `Int64`. -/
theorem toMillis_int64_range {c : DatetimeComponents} (hsyn : c.syntaxWf) (hcon : c.constraintsWf) :
    Int64.MIN ≤ c.toMillis ∧ c.toMillis ≤ Int64.MAX := by
  have h := toMillis_range hsyn hcon
  simp only [Int64.MIN, Int64.MAX]
  omega

end Cedar.Thm.Datetime
