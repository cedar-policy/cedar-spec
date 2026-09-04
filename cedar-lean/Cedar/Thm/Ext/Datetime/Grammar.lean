module

public import Cedar.Spec.Ext.Datetime
public import Cedar.Thm.Data.String

import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.Datetime
import all Cedar.Thm.Data.String

namespace Cedar.Thm.Datetime
open Cedar.Spec.Ext

/-! # Datetime grammar: definitions

This file contains only the grammar-level definitions — the well-formedness predicates — as a
direct, parser-independent transcription of the datetime grammar. Well-formedness takes the same
shape as the decimal and duration grammars — the string is the rendering of well-formed components
— but the datetime grammar describes a date optionally followed by a time, a fractional-seconds
field, and a zone designator, so the components form a nested record rather than a flat sequence
of fields.
The `Digit⁺` predicate `IsDigits` and its fixed-width refinement `IsFixedDigits` (the grammar's
`Digit{n}`, used for every numeric field here) are shared with the decimal and duration grammars
and live in `Cedar.Thm.Data.String`. -/

/-- Numeric value of a digit field, defaulting to `0` when the string does not parse. On a field
    satisfying `IsFixedDigits` the default is never taken, so this is exactly the field's value. -/
-- ANCHOR: fieldValue
public def fieldValue (s : String) : Nat := (toNat?' s).getD 0
-- ANCHOR_END: fieldValue

/-! ## Numeric constraints

The grammar's `Constraints` block bounds each numeric field. These are pure arithmetic predicates
over the field values; `daysInMonth` and `isLeapYear` transcribe the two auxiliary functions the
day constraint depends on. -/

/-- The grammar's `isLeapYear(y) = (4 | y) ∧ (¬(100 | y) ∨ (400 | y))`, as a decidable `Bool`. -/
-- ANCHOR: isLeapYear
public def isLeapYear (y : Nat) : Bool :=
  y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
-- ANCHOR_END: isLeapYear

/-- The grammar's `daysInMonth(y, m)`: 30 for April/June/September/November, 28 or 29 for
    February depending on the leap year, and 31 otherwise. -/
-- ANCHOR: daysInMonth
public def daysInMonth (y m : Nat) : Nat :=
  if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else if m == 2 then (if isLeapYear y then 29 else 28)
  else 31
-- ANCHOR_END: daysInMonth

/-! ## Components

Each nonterminal of the grammar becomes a record of its fixed-width digit fields. A `syntaxWf`
predicate pins the field widths (`Digit{n}`) and a `constraintsWf` predicate imposes the numeric
bounds from the grammar's `Constraints` block. -/

/-- The grammar's `Date ::= YYYY '-' MM '-' DD`. -/
-- ANCHOR: DateComponents
public structure DateComponents where
  year : String
  month : String
  day : String
-- ANCHOR_END: DateComponents

/-- `YYYY` is `Digit{4}`; `MM` and `DD` are `Digit{2}`. -/
-- ANCHOR: DateComponents.syntaxWf
public def DateComponents.syntaxWf (d : DateComponents) : Prop :=
  IsFixedDigits 4 d.year ∧
  IsFixedDigits 2 d.month ∧
  IsFixedDigits 2 d.day
-- ANCHOR_END: DateComponents.syntaxWf

/-- The month/day bounds: `01 ≤ MM ≤ 12` and `01 ≤ DD ≤ daysInMonth(YYYY, MM)`. -/
-- ANCHOR: DateComponents.constraintsWf
public def DateComponents.constraintsWf (d : DateComponents) : Prop :=
  let mm := fieldValue d.month
  1 ≤ mm ∧ mm ≤ 12 ∧
  1 ≤ fieldValue d.day ∧ fieldValue d.day ≤ daysInMonth (fieldValue d.year) mm
-- ANCHOR_END: DateComponents.constraintsWf

/-- Render a date as `YYYY '-' MM '-' DD`. -/
-- ANCHOR: DateComponents.asString
public def DateComponents.asString (d : DateComponents) : String :=
  d.year ++ "-" ++ d.month ++ "-" ++ d.day
-- ANCHOR_END: DateComponents.asString

/-- The grammar's `Time ::= hh ':' mm ':' ss`. -/
-- ANCHOR: TimeComponents
public structure TimeComponents where
  hours : String
  minutes : String
  seconds : String
-- ANCHOR_END: TimeComponents

/-- `hh`, `mm`, and `ss` are each `Digit{2}`. -/
-- ANCHOR: TimeComponents.syntaxWf
public def TimeComponents.syntaxWf (t : TimeComponents) : Prop :=
  IsFixedDigits 2 t.hours ∧
  IsFixedDigits 2 t.minutes ∧
  IsFixedDigits 2 t.seconds
-- ANCHOR_END: TimeComponents.syntaxWf

/-- The time bounds: `00 ≤ hh ≤ 23`, `00 ≤ mm ≤ 59`, `00 ≤ ss ≤ 59`. -/
-- ANCHOR: TimeComponents.constraintsWf
public def TimeComponents.constraintsWf (t : TimeComponents) : Prop :=
  fieldValue t.hours ≤ 23 ∧
  fieldValue t.minutes ≤ 59 ∧
  fieldValue t.seconds ≤ 59
-- ANCHOR_END: TimeComponents.constraintsWf

/-- Render a time as `hh ':' mm ':' ss`. -/
-- ANCHOR: TimeComponents.asString
public def TimeComponents.asString (t : TimeComponents) : String :=
  t.hours ++ ":" ++ t.minutes ++ ":" ++ t.seconds
-- ANCHOR_END: TimeComponents.asString

/-- The grammar's `Offset ::= ('+' | '-') hh mm`. `negative` records the sign character;
    `hours` and `mm` reuse the `hh`/`mm` nonterminals of `Time`. -/
-- ANCHOR: OffsetComponents
public structure OffsetComponents where
  negative : Bool
  hours : String
  minutes : String
-- ANCHOR_END: OffsetComponents

/-- The offset's `hh` and `mm` are each `Digit{2}`, matching the `Time` nonterminals. -/
-- ANCHOR: OffsetComponents.syntaxWf
public def OffsetComponents.syntaxWf (o : OffsetComponents) : Prop :=
  IsFixedDigits 2 o.hours ∧
  IsFixedDigits 2 o.minutes
-- ANCHOR_END: OffsetComponents.syntaxWf

/-- Because the offset reuses the `hh`/`mm` nonterminals, it inherits their bounds:
    `00 ≤ hh ≤ 23` and `00 ≤ mm ≤ 59`. -/
-- ANCHOR: OffsetComponents.constraintsWf
public def OffsetComponents.constraintsWf (o : OffsetComponents) : Prop :=
  fieldValue o.hours ≤ 23 ∧
  fieldValue o.minutes ≤ 59
-- ANCHOR_END: OffsetComponents.constraintsWf

/-- Render an offset as `('+' | '-') hh mm`. -/
-- ANCHOR: OffsetComponents.asString
public def OffsetComponents.asString (o : OffsetComponents) : String :=
  (if o.negative then "-" else "+") ++ o.hours ++ o.minutes
-- ANCHOR_END: OffsetComponents.asString

/-- The zone designator that terminates a datetime with a time: either the UTC marker `'Z'`
    (`Date 'T' Time 'Z'` / `Date 'T' Time '.' SSS 'Z'`) or an explicit `Offset`. -/
-- ANCHOR: Zone
public inductive Zone where
  | utc
  | offset (o : OffsetComponents)
-- ANCHOR_END: Zone

/-- A UTC marker imposes nothing; an offset must have well-formed digit fields. -/
-- ANCHOR: Zone.syntaxWf
public def Zone.syntaxWf : Zone → Prop
  | .utc => True
  | .offset o => o.syntaxWf
-- ANCHOR_END: Zone.syntaxWf

/-- A UTC marker imposes nothing; an offset must satisfy the `hh`/`mm` bounds. -/
-- ANCHOR: Zone.constraintsWf
public def Zone.constraintsWf : Zone → Prop
  | .utc => True
  | .offset o => o.constraintsWf
-- ANCHOR_END: Zone.constraintsWf

/-- Render the zone: `'Z'` for UTC, otherwise the offset's `('+' | '-') hh mm`. -/
-- ANCHOR: Zone.asString
public def Zone.asString : Zone → String
  | .utc => "Z"
  | .offset o => o.asString
-- ANCHOR_END: Zone.asString

/-- The time-bearing tail of a datetime: a `Time`, an optional fractional-seconds field `SSS`
    (`'.' SSS`), and a `Zone`. Absent `SSS` (`none`) corresponds to the forms without a
    `'.' SSS`; `some` corresponds to the `'.' SSS` forms. -/
-- ANCHOR: TimePart
public structure TimePart where
  time : TimeComponents
  millis : Option String
  zone : Zone
-- ANCHOR_END: TimePart

/-- Lift `IsFixedDigits 3` (the grammar's `SSS ::= Digit{3}`) to the optional field:
    an absent `SSS` is trivially valid. -/
-- ANCHOR: IsWfOptionalMillis
public def IsWfOptionalMillis : Option String → Prop
  | none => True
  | some millis => IsFixedDigits 3 millis
-- ANCHOR_END: IsWfOptionalMillis

/-- The time, the optional `SSS`, and the zone are each well-formed. -/
-- ANCHOR: TimePart.syntaxWf
public def TimePart.syntaxWf (tp : TimePart) : Prop :=
  tp.time.syntaxWf ∧
  IsWfOptionalMillis tp.millis ∧
  tp.zone.syntaxWf
-- ANCHOR_END: TimePart.syntaxWf

/-- The time and zone satisfy their numeric bounds. `SSS` is unconstrained (`000`–`999` are all
    valid), so it contributes no numeric constraint. -/
-- ANCHOR: TimePart.constraintsWf
public def TimePart.constraintsWf (tp : TimePart) : Prop :=
  tp.time.constraintsWf ∧ tp.zone.constraintsWf
-- ANCHOR_END: TimePart.constraintsWf

/-- Render the tail: `'T' Time ['.' SSS] Zone`, so `some sss` inserts `'.' sss`. -/
-- ANCHOR: TimePart.asString
public def TimePart.asString (tp : TimePart) : String :=
  "T" ++ tp.time.asString ++
    (match tp.millis with | none => "" | some sss => "." ++ sss) ++
    tp.zone.asString
-- ANCHOR_END: TimePart.asString

/-- A datetime is a `Date` optionally followed by a time-bearing tail. `none` is the date-only
    form `Date`; `some tp` covers the four `Date 'T' Time …` forms, with the presence of `SSS`
    and the choice of `Zone` selecting among them. -/
-- ANCHOR: DatetimeComponents
public structure DatetimeComponents where
  date : DateComponents
  time : Option TimePart
-- ANCHOR_END: DatetimeComponents

/-- Every present component has well-formed digit fields. -/
-- ANCHOR: DatetimeComponents.syntaxWf
public def DatetimeComponents.syntaxWf (c : DatetimeComponents) : Prop :=
  c.date.syntaxWf ∧ (match c.time with | none => True | some tp => tp.syntaxWf)
-- ANCHOR_END: DatetimeComponents.syntaxWf

/-- Every present component satisfies its numeric bounds. -/
-- ANCHOR: DatetimeComponents.constraintsWf
public def DatetimeComponents.constraintsWf (c : DatetimeComponents) : Prop :=
  c.date.constraintsWf ∧ (match c.time with | none => True | some tp => tp.constraintsWf)
-- ANCHOR_END: DatetimeComponents.constraintsWf

/-- Canonical string representation: the date, followed by the time-bearing tail when present.
    Phrasing well-formedness existentially over `asString` (below) bakes the grammar's structure
    in for free — the separators, the fixed field order, and the choice among the five top-level
    forms all follow from the shape of the witnessing record. -/
-- ANCHOR: DatetimeComponents.asString
public def DatetimeComponents.asString (c : DatetimeComponents) : String :=
  c.date.asString ++ (match c.time with | none => "" | some tp => tp.asString)
-- ANCHOR_END: DatetimeComponents.asString

/-- A datetime string is well-formed exactly when it is the rendering of some `DatetimeComponents`
    that is both syntactically well-formed and satisfies the grammar's numeric constraints. -/
-- ANCHOR: IsWfDatetime
public def IsWfDatetime (str : String) : Prop :=
  ∃ components : DatetimeComponents,
    components.syntaxWf ∧
    components.constraintsWf ∧
    str = components.asString
-- ANCHOR_END: IsWfDatetime

/-! ## Value function

`computeValue` mirrors the date/time → milliseconds-since-epoch conversion the parser performs,
stated independently of the parser's implementation. It re-parses the string into components (a
structural transcription of the grammar, as the decimal and duration value functions also do)
and applies a value function to them. It returns `none` for strings that do not match the grammar
structure; on `IsWfDatetime`-satisfying inputs it always returns `some` (see
`Cedar.Thm.Ext.Datetime`). -/

/-- Day count of a date since the Unix epoch (1970-01-01), via Howard Hinnant's `days_from_civil`
    algorithm. This transcribes `Std.Time.PlainDate.toEpochDay` over raw `Nat` fields,
    so that `computeValue` can be stated independently of the `Std.Time` date type. -/
-- ANCHOR: epochDays
public def epochDays (year month day : Nat) : Int :=
  let m : Int := month
  let d : Int := day
  let y : Int := if m > 2 then year else (year : Int) - 1
  let era : Int := (if y ≥ 0 then y else y - 399).tdiv 400
  let yoe : Int := y - era * 400
  let doy : Int := (153 * (m + (if m > 2 then -3 else 9)) + 2).tdiv 5 + d - 1
  let doe : Int := yoe * 365 + yoe.tdiv 4 - yoe.tdiv 100 + doy
  era * 146097 + doe - 719468
-- ANCHOR_END: epochDays

/-- The offset's signed second count: `± (hh × 3600 + mm × 60)`. Positive offsets (`+hhmm`) are
    east of UTC, so the parser subtracts this to normalize to UTC. -/
-- ANCHOR: OffsetComponents.seconds
public def OffsetComponents.seconds (o : OffsetComponents) : Int :=
  let mag : Int := fieldValue o.hours * 3600 + fieldValue o.minutes * 60
  if o.negative then -mag else mag
-- ANCHOR_END: OffsetComponents.seconds

/-- Signed UTC-normalization seconds contributed by a zone: `0` for the `'Z'` marker, and the
    offset's second count otherwise. -/
-- ANCHOR: Zone.offsetSeconds
public def Zone.offsetSeconds : Zone → Int
  | .utc => 0
  | .offset o => o.seconds
-- ANCHOR_END: Zone.offsetSeconds

/-- Milliseconds-since-epoch value of a well-formed date's midnight UTC. -/
-- ANCHOR: DateComponents.toMillis
public def DateComponents.toMillis (d : DateComponents) : Int :=
  epochDays (fieldValue d.year) (fieldValue d.month) (fieldValue d.day) * 86400000
-- ANCHOR_END: DateComponents.toMillis

/-- Milliseconds-since-epoch value of a datetime's time-bearing tail relative to its date's
    midnight: the wall-clock time in milliseconds, less the zone offset (converting to UTC),
    plus the optional fractional-seconds field. -/
-- ANCHOR: TimePart.toMillis
public def TimePart.toMillis (tp : TimePart) : Int :=
  let wallSeconds : Int :=
    fieldValue tp.time.hours * 3600 + fieldValue tp.time.minutes * 60 + fieldValue tp.time.seconds
  let millis : Int := match tp.millis with | none => 0 | some sss => fieldValue sss
  (wallSeconds - tp.zone.offsetSeconds) * 1000 + millis
-- ANCHOR_END: TimePart.toMillis

/-- Milliseconds-since-epoch value of a whole datetime: the date's midnight plus the time-bearing
    tail's contribution (`0` for the date-only form). -/
-- ANCHOR: DatetimeComponents.toMillis
public def DatetimeComponents.toMillis (c : DatetimeComponents) : Int :=
  c.date.toMillis + (match c.time with | none => 0 | some tp => tp.toMillis)
-- ANCHOR_END: DatetimeComponents.toMillis

/-- Structural parse of a `Date`: split on `'-'` into `[YYYY, MM, DD]`. -/
-- ANCHOR: parseDate
public def parseDate (s : String) : Option DateComponents :=
  match s.splitToList (· = '-') with
  | [year, month, day] => some { year, month, day }
  | _ => none
-- ANCHOR_END: parseDate

/-- Structural parse of a `Time`: split on `':'` into `[hh, mm, ss]`. -/
-- ANCHOR: parseTime
public def parseTime (s : String) : Option TimeComponents :=
  match s.splitToList (· = ':') with
  | [hours, minutes, seconds] => some { hours, minutes, seconds }
  | _ => none
-- ANCHOR_END: parseTime

/-- Structural parse of an `Offset ::= ('+' | '-') hh mm`: a sign character followed by exactly
    four characters, split into two two-character fields. -/
-- ANCHOR: parseOffset
public def parseOffset (s : String) : Option OffsetComponents :=
  match s.toList with
  | sign :: rest =>
    if (sign = '+' ∨ sign = '-') ∧ rest.length = 4 then
      some { negative := sign = '-',
             hours := String.ofList (rest.take 2),
             minutes := String.ofList (rest.drop 2) }
    else none
  | _ => none
-- ANCHOR_END: parseOffset

/-- Structural parse of the time-bearing tail's body — the portion after the `'T'`, i.e.
    `Time ['.' SSS] Zone`. The zone designator is split off the end by inspecting the character
    list in reverse (a trailing `'Z'` gives the UTC zone; otherwise the last five characters form
    an `Offset`), and the remainder is split on `'.'` into the time and the optional `SSS`. -/
-- ANCHOR: parseTimePart
public def parseTimePart (s : String) : Option TimePart := do
  let (timeMs, zone) ←
    match s.toList.reverse with
    | [] => none
    | c :: rev =>
      if c = 'Z' then some (String.ofList rev.reverse, Zone.utc)
      else do
        let o ← parseOffset (String.ofList ((c :: rev).take 5).reverse)
        some (String.ofList ((c :: rev).drop 5).reverse, Zone.offset o)
  match timeMs.splitToList (· = '.') with
  | [time] => do
    let t ← parseTime time
    some { time := t, millis := none, zone }
  | [time, sss] => do
    let t ← parseTime time
    some { time := t, millis := some sss, zone }
  | _ => none
-- ANCHOR_END: parseTimePart

/-- Structural parse of a datetime string into components: split on `'T'` into a date and an
    optional time-bearing tail. A direct transcription of the grammar's five top-level forms. -/
-- ANCHOR: parseComponents
public def parseComponents (str : String) : Option DatetimeComponents := do
  match str.splitToList (· = 'T') with
  | [date] => do
    let d ← parseDate date
    some { date := d, time := none }
  | [date, rest] => do
    let d ← parseDate date
    let tp ← parseTimePart rest
    some { date := d, time := some tp }
  | _ => none
-- ANCHOR_END: parseComponents

/-- Convert a datetime string to its milliseconds-since-epoch value, or `none` when the string
    does not match the grammar structure. Structurally re-parses the string and applies the
    components' value function `toMillis`. -/
-- ANCHOR: computeValue
public def computeValue (str : String) : Option Int :=
  (parseComponents str).map DatetimeComponents.toMillis
-- ANCHOR_END: computeValue

/-! ## Canonical serialization

`Datetime` stores an arbitrary `Int64` millisecond value, while the concrete syntax restricts
years to `0000` through `9999`. Serialization is therefore partial. It always emits the most
explicit grammar form, `YYYY-MM-DDTHH:mm:ss.SSS±HHMM`, using a zero offset when UTC is in range and
the smallest minute offset needed at either endpoint. All decimal fields are rendered here rather
than through `Std.Time`'s formatter. -/

/-- Milliseconds in one day. -/
public def MILLIS_PER_DAY : Int := 86400000

/-- Smallest millisecond value whose UTC civil date has a four-digit nonnegative year. -/
public def MIN_UTC_MILLIS : Int := -62167219200000

/-- Largest millisecond value whose UTC civil date has a four-digit nonnegative year. -/
public def MAX_UTC_MILLIS : Int := 253402300799999

/-- Largest legal timezone-offset magnitude, `23:59`, in milliseconds. -/
public def MAX_OFFSET_MILLIS : Int := 86340000

/-- Exact lower endpoint representable by the datetime grammar. -/
public def MIN_REPRESENTABLE_MILLIS : Int := MIN_UTC_MILLIS - MAX_OFFSET_MILLIS

/-- Exact upper endpoint representable by the datetime grammar. -/
public def MAX_REPRESENTABLE_MILLIS : Int := MAX_UTC_MILLIS + MAX_OFFSET_MILLIS

/-- Render a natural number as an ASCII decimal string padded with leading zeroes to `width`. -/
public def fixedWidthNat (width n : Nat) : String :=
  String.ofList (List.leftpad width '0' (toString n).toList)

/-- The local millisecond value and explicit offset selected for canonical serialization. -/
public structure CanonicalLocalTime where
  localMillis : Int
  offsetNegative : Bool
  offsetMinutes : Nat

/-- Select UTC whenever possible. Immediately outside the UTC civil range, select the smallest
    minute offset that moves the local civil time back into that range. -/
public def canonicalLocalTime? (value : Int) : Option CanonicalLocalTime :=
  if value < MIN_REPRESENTABLE_MILLIS ∨ MAX_REPRESENTABLE_MILLIS < value then
    none
  else if value < MIN_UTC_MILLIS then
    let minutes := (Int.ediv (MIN_UTC_MILLIS - value + 59999) 60000).toNat
    some {
      localMillis := value + minutes * 60000
      offsetNegative := false
      offsetMinutes := minutes
    }
  else if MAX_UTC_MILLIS < value then
    let minutes := (Int.ediv (value - MAX_UTC_MILLIS + 59999) 60000).toNat
    some {
      localMillis := value - minutes * 60000
      offsetNegative := true
      offsetMinutes := minutes
    }
  else
    some {
      localMillis := value
      offsetNegative := false
      offsetMinutes := 0
    }

/-- Build canonical grammar components from an in-range local millisecond value and its selected
    explicit offset. `PlainDate.ofEpochDay` supplies numeric calendar fields only; rendering is
    performed by `fixedWidthNat`. -/
public def canonicalComponents (localTime : CanonicalLocalTime) : DatetimeComponents :=
  let epochDay := Int.ediv localTime.localMillis MILLIS_PER_DAY
  let dayMillis := Int.emod localTime.localMillis MILLIS_PER_DAY
  let date := Std.Time.PlainDate.ofEpochDay (Std.Time.Day.Offset.ofInt epochDay)
  let hours := (Int.ediv dayMillis 3600000).toNat
  let minutes := (Int.ediv (Int.emod dayMillis 3600000) 60000).toNat
  let seconds := (Int.ediv (Int.emod dayMillis 60000) 1000).toNat
  let millis := (Int.emod dayMillis 1000).toNat
  let offsetHours := localTime.offsetMinutes / 60
  let offsetMinutes := localTime.offsetMinutes % 60
  {
    date := {
      year := fixedWidthNat 4 date.year.toInt.toNat
      month := fixedWidthNat 2 date.month.val.toNat
      day := fixedWidthNat 2 date.day.val.toNat
    }
    time := some {
      time := {
        hours := fixedWidthNat 2 hours
        minutes := fixedWidthNat 2 minutes
        seconds := fixedWidthNat 2 seconds
      }
      millis := some (fixedWidthNat 3 millis)
      zone := .offset {
        negative := localTime.offsetNegative
        hours := fixedWidthNat 2 offsetHours
        minutes := fixedWidthNat 2 offsetMinutes
      }
    }
  }

/-- Executable mirror of `IsFixedDigits`. -/
public def isFixedDigits (width : Nat) (s : String) : Bool :=
  (toNat?' s).isSome && s.length == width

/-- Executable mirror of `DatetimeComponents.syntaxWf`. -/
public def DatetimeComponents.syntaxWfB (components : DatetimeComponents) : Bool :=
  isFixedDigits 4 components.date.year &&
  isFixedDigits 2 components.date.month &&
  isFixedDigits 2 components.date.day &&
  match components.time with
  | none => true
  | some time =>
    isFixedDigits 2 time.time.hours &&
    isFixedDigits 2 time.time.minutes &&
    isFixedDigits 2 time.time.seconds &&
    (match time.millis with | none => true | some millis => isFixedDigits 3 millis) &&
    match time.zone with
    | .utc => true
    | .offset offset => isFixedDigits 2 offset.hours && isFixedDigits 2 offset.minutes

/-- Executable mirror of `DatetimeComponents.constraintsWf`. -/
public def DatetimeComponents.constraintsWfB (components : DatetimeComponents) : Bool :=
  let year := fieldValue components.date.year
  let month := fieldValue components.date.month
  let day := fieldValue components.date.day
  decide (1 ≤ month) && decide (month ≤ 12) &&
  decide (1 ≤ day) && decide (day ≤ daysInMonth year month) &&
  match components.time with
  | none => true
  | some time =>
    decide (fieldValue time.time.hours ≤ 23) &&
    decide (fieldValue time.time.minutes ≤ 59) &&
    decide (fieldValue time.time.seconds ≤ 59) &&
    match time.zone with
    | .utc => true
    | .offset offset =>
      decide (fieldValue offset.hours ≤ 23) &&
      decide (fieldValue offset.minutes ≤ 59)

/-- Produce certified canonical components for a datetime value. The final check is deliberately
    stated in terms of the owned grammar and value function, insulating serialization from
    `Std.Time` formatting behavior. -/
public def canonicalComponents? (d : Cedar.Spec.Ext.Datetime) : Option DatetimeComponents := do
  let localTime ← canonicalLocalTime? d.val.toInt
  let components := canonicalComponents localTime
  if components.syntaxWfB && components.constraintsWfB &&
      components.toMillis == d.val.toInt then
    some components
  else
    none

/-- Canonical partial serializer for datetime values. Every successful result has the fixed form
    `YYYY-MM-DDTHH:mm:ss.SSS±HHMM`. -/
public def toString? (d : Cedar.Spec.Ext.Datetime) : Option String :=
  (canonicalComponents? d).map DatetimeComponents.asString

/-- Canonical-form normalizer: parse the string and re-serialize. Returns `none` for malformed
    inputs (mirror of the decimal and duration normalizers); because serialization is partial the
    re-serialization is a `bind` rather than the total `map` used there. -/
public def normalize (str : String) : Option String := (Datetime.parse str).bind toString?

end Cedar.Thm.Datetime
