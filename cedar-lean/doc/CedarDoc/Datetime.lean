import VersoManual
import CedarDoc.GrammarBlock
import Cedar.Thm.Ext.Datetime

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Cedar.Spec.Ext
open Cedar.Thm.Datetime
open CedarDoc

set_option verso.code.warnLineLength 80

-- Source project for `anchor` code blocks: the sibling `cedar-lean` package.
set_option verso.exampleProject ".."

#doc (Manual) "Datetime Parsing" =>

Cedar datetime values are measured in milliseconds since the Unix epoch (`1970-01-01T00:00:00Z`), stored as `Int64`.

# Grammar

The accepted syntax for datetime literals is:

```grammar
grammar
  Datetime ::= Date
             | Date 'T' Time 'Z'
             | Date 'T' Time '.' SSS 'Z'
             | Date 'T' Time Offset
             | Date 'T' Time '.' SSS Offset

  Date     ::= YYYY '-' MM '-' DD
  Time     ::= hh ':' mm ':' ss
  SSS      ::= Digit{3}
  Offset   ::= ('+' | '-') hh mm
  YYYY     ::= Digit{4}
  MM       ::= Digit{2}
  DD       ::= Digit{2}
  hh       ::= Digit{2}
  mm       ::= Digit{2}
  ss       ::= Digit{2}
  Digit    ::= '0' | '1' | … | '9'

value
  value(Datetime) in milliseconds =
    epochDays(YYYY, MM, DD) × 86400000
    + (hh × 3600 + mm × 60 + ss - offsetSeconds) × 1000 + nat(SSS)
    where epochDays     = civil-calendar days since 1970-01-01
          offsetSeconds = 0 for 'Z'; ± (hh × 3600 + mm × 60) of the
                          Offset otherwise (+ is east of UTC)
          time fields   = 0 when the date-only form omits them

constraints
  - 01 ≤ MM ≤ 12
  - 01 ≤ DD ≤ daysInMonth(YYYY, MM)
  - 00 ≤ hh ≤ 23
  - 00 ≤ mm ≤ 59
  - 00 ≤ ss ≤ 59
  - value(Datetime) ∈ [Int64.min, Int64.max]   -- implied; see below

  daysInMonth(y, m) =
    30  if m ∈ {4, 6, 9, 11}
    28  if m = 2 ∧ ¬isLeapYear(y)
    29  if m = 2 ∧ isLeapYear(y)
    31  otherwise

  isLeapYear(y) =
    (4 | y) ∧ (¬(100 | y) ∨ (400 | y))
```

A datetime string is _valid_ if and only if it satisfies the grammar and constraints above.

Like decimal and duration, a datetime is stored over `Int64`, so its value formally carries the
constraint `value(Datetime) ∈ [Int64.min, Int64.max]`. Here the syntax already forces it: the
4-digit year and `±23:59` offset confine every valid string to the range
`0000-01-01T00:00:00+2359` … `9999-12-31T23:59:59.999-2359` — values `-62167305540000` to
`253402387139999` ms, well inside `Int64`. We prove this bound (`toMillis_int64_range`), so the
constraint is implied rather than separately checked; its payoff, a failure characterization with
no overflow case, appears in _Soundness and Completeness_.

Values beyond this range are still reachable — the `datetime.offset(duration)` operator can shift a
parsed instant anywhere in `Int64` — they simply have no literal.

*Note.* The `offset` _operator_ is distinct from the grammar's `Offset` _nonterminal_ (the
`±hhmm` timezone suffix of a literal, consumed during parsing to normalize the instant to UTC);
the Cedar documentation uses the one word for both.


# Formal Specification

We formalize validity by a single predicate `IsWfDatetime` (well-formed grammar syntax) — the range constraint needs no separate clause, since it is implied. The grammar describes a date optionally followed by a time, a fractional-seconds field, and a zone designator, so the specification is phrased over an explicit record of those components (as in the duration grammar).

Every numeric field of this grammar is a digit run of an exact width, so the building block is `IsFixedDigits` — the `Digit{n}` refinement of the shared `IsDigits` predicate (introduced in the _Decimal Parsing_ chapter). It too lives in `Cedar.Thm.Data.String`:

```anchor IsFixedDigits (module := Cedar.Thm.Data.String)
public def IsFixedDigits (n : Nat) (s : String) : Prop :=
  IsDigits s ∧ s.length = n
```

Each nonterminal of the grammar becomes a record of its digit fields, with a `syntaxWf` predicate pinning field widths and a `constraintsWf` predicate imposing the numeric bounds. For the `Date ::= YYYY '-' MM '-' DD` production:

```anchor DateComponents (module := Cedar.Thm.Ext.Datetime.Grammar)
public structure DateComponents where
  year : String
  month : String
  day : String
```

```anchor DateComponents.syntaxWf (module := Cedar.Thm.Ext.Datetime.Grammar)
public def DateComponents.syntaxWf (d : DateComponents) : Prop :=
  IsFixedDigits 4 d.year ∧
  IsFixedDigits 2 d.month ∧
  IsFixedDigits 2 d.day
```

```anchor DateComponents.constraintsWf (module := Cedar.Thm.Ext.Datetime.Grammar)
public def DateComponents.constraintsWf (d : DateComponents) : Prop :=
  let mm := fieldValue d.month
  1 ≤ mm ∧ mm ≤ 12 ∧
  1 ≤ fieldValue d.day ∧ fieldValue d.day ≤ daysInMonth (fieldValue d.year) mm
```

The month/day bounds refer to `daysInMonth` and `isLeapYear`, the two auxiliary grammar functions:

```anchor daysInMonth (module := Cedar.Thm.Ext.Datetime.Grammar)
public def daysInMonth (y m : Nat) : Nat :=
  if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else if m == 2 then (if isLeapYear y then 29 else 28)
  else 31
```

```anchor isLeapYear (module := Cedar.Thm.Ext.Datetime.Grammar)
public def isLeapYear (y : Nat) : Bool :=
  y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
```

The `Time`, `Offset`, and `Zone` nonterminals are modelled the same way; the time-bearing tail (`Time ['.' SSS] Zone`) is a `TimePart` combining a `TimeComponents`, an optional millisecond field, and a `Zone`:

```anchor TimePart (module := Cedar.Thm.Ext.Datetime.Grammar)
public structure TimePart where
  time : TimeComponents
  millis : Option String
  zone : Zone
```

A datetime is then a `Date` optionally followed by such a tail, and well-formedness reads straight off the grammar — the string is the rendering of some record that is both syntactically well-formed and satisfies the numeric constraints. Phrasing this existentially over `asString` bakes in the separators, the field order, and the choice among the five top-level forms:

```anchor DatetimeComponents (module := Cedar.Thm.Ext.Datetime.Grammar)
public structure DatetimeComponents where
  date : DateComponents
  time : Option TimePart
```

```anchor IsWfDatetime (module := Cedar.Thm.Ext.Datetime.Grammar)
public def IsWfDatetime (str : String) : Prop :=
  ∃ components : DatetimeComponents,
    components.syntaxWf ∧
    components.constraintsWf ∧
    str = components.asString
```

The value of a well-formed string is computed structurally by `computeValue`: it re-parses the rendering into its components and evaluates the grammar's value formula — days since the epoch (`epochDays`, the standard civil-calendar day count) scaled to milliseconds, plus the time-of-day, fractional, and zone contributions:

```anchor computeValue (module := Cedar.Thm.Ext.Datetime.Grammar)
public def computeValue (str : String) : Option Int :=
  (parseComponents str).map DatetimeComponents.toMillis
```

# Parser

`Datetime.parse` delegates the five accepted forms to `Std.Time.GenericFormat.parse`, one fixed format string per form, tried in order:

```anchor datetimeParse (module := Cedar.Spec.Ext.Datetime)
public def parse (str: String) : Option Datetime := do
  if dateContainsLeapSeconds str then failure
  if !checkOffsetLen str then failure
  if !tzOffsetMinsLt60 str then failure
  let val :=
    DateOnly.parse str <|>
    DateUTC.parse str <|>
    DateUTCWithMillis.parse str <|>
    DateWithOffset.parse str <|>
    DateWithOffsetAndMillis.parse str

  let zonedTime ← val.toOption
  if zonedTime.timezone.offset.second.val.natAbs < MAX_OFFSET_SECONDS
  then datetime? zonedTime.toTimestamp.toMillisecondsSinceUnixEpoch.toInt
  else none
```

Three Boolean guards precede the alternation, restricting `Std.Time`'s formats to the Cedar
grammar: leap seconds (`ss = 60`) are rejected, timezone offsets must contain exactly four digits
after the sign, and the offset minutes must be below 60. The explicit offset-width guard is needed
because Lean 4.33's `Std.Time` parser accepts one or two digits for each offset field. A final range
check bounds the timezone offset, and `datetime?` narrows the epoch-millisecond value to `Int64`.

```lean -show
-- Bring the spec's `Datetime.parse` into scope for the executable `#eval` examples
-- below. The definition itself is shown from source via the `anchor` block above.
open Cedar.Spec.Ext Cedar.Spec.Ext.Datetime
```

Each of the five grammar forms parses to its epoch-millisecond value; grammar or constraint violations are rejected:

```lean (name := dt1)
#eval Datetime.parse "2024-01-15"                     -- date-only
```
```leanOutput dt1
some { val := { toUInt64 := 1705276800000 } }
```

```lean (name := dt2)
#eval Datetime.parse "2024-01-15T10:30:45.123Z"       -- UTC with milliseconds
```
```leanOutput dt2
some { val := { toUInt64 := 1705314645123 } }
```

```lean (name := dt3)
#eval Datetime.parse "2024-01-15T10:30:45+0530"       -- explicit offset
```
```leanOutput dt3
some { val := { toUInt64 := 1705294845000 } }
```

```lean (name := dt4)
#eval Datetime.parse "2024-02-30T00:00:00Z"           -- rejected: no Feb 30
```
```leanOutput dt4
none
```

```lean (name := dt5)
#eval Datetime.parse "2024-01-15T10:30:60Z"           -- rejected: leap second
```
```leanOutput dt5
none
```

```lean (name := dt6)
#eval Datetime.parse "10000-01-01"
-- rejected: format maximum is year 9999
```
```leanOutput dt6
none
```

# Soundness and Completeness

The parser is characterized by the same two guarantees as the decimal and duration parsers, stated against `IsWfDatetime` and `computeValue`. Those two are hand-written and reasoned about directly; `Datetime.parse` instead delegates to `Std.Time.GenericFormat.parse`. The extra work is a parser-inversion library that evaluates `Std.Time`'s combinator parsers once and shows a successful parse is exactly the rendering of well-formed witnessing components — reducing both proofs to reasoning about components rather than the parser's recursion.

_Soundness_: whenever parsing succeeds, the input is well-formed and `computeValue` yields exactly the returned datetime's value.

{docstring parse_sound}

_Completeness_ is the converse: every well-formed string whose computed value is `some d.val.toInt` is accepted as that datetime.

{docstring parse_complete}

Together they characterize failure completely — the parser rejects exactly the strings that are malformed or whose computed value overflows `Int64`:

{docstring parse_eq_none_iff}

For datetimes the overflow branch is vacuous: the grammar's range bound (from the _Grammar_ section) lies well inside `Int64`, so the characterization sharpens to reject _exactly_ the malformed strings:

{docstring parse_eq_none_iff_not_wf}

# Canonical String Representation

`Datetime` stores an arbitrary `Int64` millisecond value, but the grammar only spells years `0000`–`9999`, so — unlike the decimal and duration `toString`, which are total — datetime serialization is *partial*. `toString?` returns `none` for any value outside the representable interval and otherwise emits the most explicit grammar form, `YYYY-MM-DDTHH:mm:ss.SSS±HHMM`, always normalizing the instant to a `+0000` UTC offset:

{docstring toString?}

For example, every representable instant renders with an explicit millisecond field and a UTC offset; a parsed `+0530` offset comes back as the equivalent UTC time:

```lean (name := ser1)
#eval (Datetime.parse "2024-01-15T10:30:45+0530").bind toString?
```
```leanOutput ser1
some "2024-01-15T05:00:45.000+0000"
```

Values beyond the representable interval have no literal (the `datetime.offset(duration)` operator can reach them, as noted in the _Grammar_ section), so they do not serialize:

{docstring toString?_eq_none_of_not_representable}

`normalize` composes parsing and serialization — it accepts any valid string and returns its canonical form. Because serialization is partial, the re-serialization is a `bind` rather than the total `map` used for decimal and duration:

{docstring normalize}

Serialization is injective on the values it covers: two datetimes with the same (defined) canonical string are equal.

{docstring toString?_injective}

Normalization therefore decides datetime equality, up to the partiality of serialization. The forward direction carries a serializability hypothesis on the parsed values: without it, two distinct parseable-but-unrepresentable instants would both normalize to `none` while their parses differ. A full _serialization-completeness_ result (`parse s = some d → (toString? d).isSome`, needing the `Std.Time` civil-calendar round-trip) would discharge it and recover the unconditional decimal/duration form; the backward direction already holds unconditionally.

{docstring normalize_eq_iff_parse_eq}

# Roundtrip Theorem

Parsing the canonical string representation of any datetime recovers the original value. This is the headline user-facing property — `parse` and `toString?` are mutually inverse wherever `toString?` is defined — and it is what underpins `toString?_injective` above.

{docstring parse_toString_roundtrip}

It is a direct corollary of completeness: a successfully serialized string is well-formed with computed value `d.val.toInt`, so completeness parses it back to `d`. The total-`Option` phrasing packages the same fact without a side hypothesis on definedness:

{docstring bind_parse_toString?}

All theorems above are machine-checked, contain no proof placeholders, and rely only on the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
