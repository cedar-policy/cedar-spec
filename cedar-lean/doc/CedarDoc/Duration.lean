import VersoManual
import CedarDoc.GrammarBlock
import Cedar.Thm.Ext.Duration

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Cedar.Thm.Duration
open CedarDoc

set_option verso.code.warnLineLength 80

-- Source project for `module`/`anchor` code blocks: the sibling `cedar-lean`
-- package, relative to this doc's Lake workspace. These blocks render the real
-- imported definitions (true namespaces and bodies) straight from source.
set_option verso.exampleProject ".."

#doc (Manual) "Duration Parsing" =>

Cedar durations are measured in milliseconds, stored as an `Int64`. A duration literal is a signed sequence of unit-tagged components — days, hours, minutes, seconds, and milliseconds — printed from the largest unit to the smallest. For example, `1d2h30m` denotes one day, two hours, and thirty minutes.

# Grammar

The accepted syntax for duration literals is:

```grammar
grammar
  Duration   ::= ['-'] Components
  Components ::= [Days] [Hours] [Minutes] [Seconds] [Millis]

  Days       ::= Digit⁺ 'd'
  Hours      ::= Digit⁺ 'h'
  Minutes    ::= Digit⁺ 'm'
  Seconds    ::= Digit⁺ 's'
  Millis     ::= Digit⁺ 'ms'
  Digit      ::= '0' | '1' | … | '9'

value
  value(Duration) in milliseconds =
    sign × (d × 86400000 + h × 3600000 + m × 60000
            + s × 1000 + ms)
    where sign        = -1 if '-' is present, else 1
          d, h, m, s, ms = nat value of each component
                           (0 if omitted)

constraints
  - At least one component must be present
  - value(Duration) ∈ [Int64.min, Int64.max]
```

A string is _valid_ if and only if it satisfies both the grammar and the constraints above.

# Formal Specification

We formalize the validity of an input string by the predicate `IsWfDuration` (well-formed syntax of the grammar) and the function `computeValue` (value function). All three numeric grammars phrase well-formedness the same way — the string is the rendering of well-formed components — but where the decimal grammar has a fixed sequence of fields, the duration grammar describes an ordered concatenation of *optional* components, so the specification is phrased over an explicit record of those components.

The building block is again `IsDigits`, the shared `Digit⁺` predicate introduced in the _Decimal Parsing_ chapter.

Each of the five components is optional. `IsWfOptionalQuantity` lifts `IsDigits` to optional strings — an absent component (`none`) is trivially valid, and a present one must be a non-empty digit string:

```anchor IsWfOptionalQuantity (module := Cedar.Thm.Ext.Duration.Grammar)
public def IsWfOptionalQuantity : Option String → Prop
  | none => True
  | some digits => IsDigits digits
```

A `Components` record holds the five optional digit strings, one per time unit:

```anchor Components (module := Cedar.Thm.Ext.Duration.Grammar)
public structure Components where
  days : Option String
  hours : Option String
  minutes : Option String
  seconds : Option String
  milliseconds : Option String
```

Two predicates constrain a record. `nonempty` enforces that at least one component is present — the body cannot be empty:

```anchor nonempty (module := Cedar.Thm.Ext.Duration.Grammar)
public def Components.nonempty (components : Components) : Prop :=
  components.days ≠ none ∨
  components.hours ≠ none ∨
  components.minutes ≠ none ∨
  components.seconds ≠ none ∨
  components.milliseconds ≠ none
```

`quantitiesWf` enforces that every present component is a valid digit quantity:

```anchor quantitiesWf (module := Cedar.Thm.Ext.Duration.Grammar)
public def Components.quantitiesWf
    (components : Components) : Prop :=
  IsWfOptionalQuantity components.days ∧
  IsWfOptionalQuantity components.hours ∧
  IsWfOptionalQuantity components.minutes ∧
  IsWfOptionalQuantity components.seconds ∧
  IsWfOptionalQuantity components.milliseconds
```

`asString` renders a record back to a string by concatenating the present components in order `d h m s ms`, each absent component contributing `""`. This is what ties the abstract record to the concrete grammar's largest-to-smallest ordering:

```anchor asString (module := Cedar.Thm.Ext.Duration.Grammar)
public def Components.asString (components : Components) : String :=
  durationChunk components.days "d" ++
  durationChunk components.hours "h" ++
  durationChunk components.minutes "m" ++
  durationChunk components.seconds "s" ++
  durationChunk components.milliseconds "ms"
```

A body is well-formed exactly when it is the rendering of _some_ record that is both nonempty and has valid quantities. Phrasing well-formedness existentially over `asString` bakes the ordering constraint in for free: a string is well-formed only if it can be produced by concatenating components in the canonical order, so out-of-order strings have no witnessing record:

```anchor IsWfBody (module := Cedar.Thm.Ext.Duration.Grammar)
public def IsWfBody (body : String) : Prop :=
  ∃ components : Components,
    components.nonempty ∧
    components.quantitiesWf ∧
    body = components.asString
```

Well-formedness of the whole string then adds the optional leading `'-'`. That sign is its own production, `Sign ::= ['-']`, and reuses the shared `IsWfSign` predicate from the _Decimal Parsing_ chapter. A duration string is well-formed exactly when it is the rendering of such a sign followed by a well-formed body — the same rendering-existential shape used for the body itself, and for the decimal and datetime grammars:

```anchor IsWfDuration (module := Cedar.Thm.Ext.Duration.Grammar)
public def IsWfDuration (str : String) : Prop :=
  ∃ sign body,
    str = sign ++ body ∧
    IsWfSign sign ∧
    IsWfBody body
```

The value function is defined independently of the parser. `extractTrailingQuantity` peels the natural-number token immediately preceding a given suffix. When the suffix is absent the component is simply not present, so it yields `some (0, s)`; when the suffix is present but its digits are missing or unparseable the string is malformed, so it yields `none` — the same failure structure as the parser's `parseUnit?` (shown in the next section):

```anchor extractTrailingQuantity (module := Cedar.Thm.Ext.Duration.Grammar)
public def extractTrailingQuantity (s : String) (suffix : String) : Option (Nat × String) :=
  if s.endsWith suffix then
    let rest := (s.dropEnd suffix.length).toString
    let digits := rest.toList.reverse.takeWhile Char.isDigit |>.reverse
    match toNat?' (String.ofList digits) with
    | some n => some (n, (rest.dropEnd digits.length).toString)
    | none => none
  else
    some (0, s)
```

`computeBodyValue` extracts each component right-to-left (`ms`, `s`, `m`, `h`, `d`) and combines them into an unsigned millisecond total, failing (`none`) if any present component is unparseable:

```anchor computeBodyValue (module := Cedar.Thm.Ext.Duration.Grammar)
public def computeBodyValue (body : String) : Option Int := do
  let (ms, body) ← extractTrailingQuantity body "ms"
  let (sec, body) ← extractTrailingQuantity body "s"
  let (min, body) ← extractTrailingQuantity body "m"
  let (hr, body) ← extractTrailingQuantity body "h"
  let (day, _) ← extractTrailingQuantity body "d"
  some (↑day * MILLISECONDS_PER_DAY +
    ↑hr * MILLISECONDS_PER_HOUR +
    ↑min * MILLISECONDS_PER_MINUTE +
    ↑sec * MILLISECONDS_PER_SECOND +
    ↑ms)
```

Finally `computeValue` splits off the sign and applies it to the body's value, propagating `none` when the body is structurally unparseable:

```anchor computeValue (module := Cedar.Thm.Ext.Duration.Grammar)
public def computeValue (str : String) : Option Int :=
  let (isNegative, body) := isNegativeDuration str
  computeSignedBodyValue isNegative body
```

# Parser

```lean -show
-- Bring the spec's `Duration` type and `Duration.parse`/`Duration.toString` into
-- scope for the executable `#eval` examples below. The definitions themselves are
-- shown from source via `anchor` blocks, so nothing is redeclared here.
open Cedar.Spec.Ext Cedar.Spec.Ext.Datetime
```

`Duration.parse` returns `some d` when the input string is valid, and `none` otherwise. It first splits off an optional leading `'-'` with `isNegativeDuration`, then hands the remaining body to `parseDuration?` (shown here directly from its source in `Cedar.Spec.Ext.Datetime`):

```anchor parse (module := Cedar.Spec.Ext.Datetime)
public def Duration.parse (str : String) : Option Duration :=
  let (isNegative, restStr) := isNegativeDuration str
  parseDuration? isNegative restStr
```

`parseDuration?` consumes each unit suffix in largest-to-smallest order (`d`, `h`, `m`, `s`, `ms` are peeled from the _right_), accumulates the signed millisecond total, and requires that the body be fully consumed. Because the units are matched in a fixed order, out-of-order strings like `1h30m1d` are rejected:

```anchor parseDuration (module := Cedar.Spec.Ext.Datetime)
def parseDuration? (isNegative : Bool) (str : String) : Option Duration := do
  if str.isEmpty then failure
  let (milliseconds, restStr) ← parseUnit? isNegative str "ms"
  let (seconds, restStr) ← parseUnit? isNegative restStr "s"
  let (minutes, restStr) ← parseUnit? isNegative restStr "m"
  let (hours, restStr) ← parseUnit? isNegative restStr "h"
  let (days, restStr) ← parseUnit? isNegative restStr "d"
  if restStr.isEmpty
  then duration? (days + hours + minutes + seconds + milliseconds)
  else none
```

For example:

```lean (name := ex1)
#eval (Duration.parse "1d2h30m").map Duration.toString    -- valid
```
```leanOutput ex1
some "1d2h30m0s0ms"
```

```lean (name := ex2)
#eval (Duration.parse "-1h30m").map Duration.toString      -- negative
```
```leanOutput ex2
some "-0d1h30m0s0ms"
```

```lean (name := ex3)
#eval Duration.parse "1h30m1d"                             -- out of order
```
```leanOutput ex3
none
```

```lean (name := ex4)
#eval Duration.parse ""                                    -- empty
```
```leanOutput ex4
none
```

# Soundness and Completeness

The parser is characterized by two complementary guarantees stated in terms of the previous formal definitions.

_Soundness_ says that whenever parsing succeeds, the input was genuinely valid: it is well-formed and `computeValue` yields exactly the returned duration's value. (The range constraint is implicit — `d.val.toInt` is always in `Int64` range, since `d.val` is an `Int64`.)

{docstring parse_sound}

_Completeness_ is the converse: every well-formed string whose computed value is `some d.val.toInt` is accepted as that duration. (Again the range constraint is implicit — `d.val.toInt` is always in range.)

{docstring parse_complete}

Together they also give a complete characterization of parsing failure — the parser rejects exactly those strings that are malformed or whose computed value overflows the `Int64` range:

{docstring parse_eq_none_iff}

# Canonical String Representation

`Duration.toString` converts a duration back to a canonical string, maximizing units and printing all five components largest-to-smallest (including zero-valued ones), with a leading `'-'` for negative values:

```anchor toString (module := Cedar.Spec.Ext.Datetime)
public def Duration.toString (d : Duration) : String :=
  let neg := d.val < 0
  let totalMs := d.val.toInt.natAbs
  let days := totalMs / MILLISECONDS_PER_DAY.toNat
  let rem := totalMs % MILLISECONDS_PER_DAY.toNat
  let hours := rem / MILLISECONDS_PER_HOUR.toNat
  let rem := rem % MILLISECONDS_PER_HOUR.toNat
  let minutes := rem / MILLISECONDS_PER_MINUTE.toNat
  let rem := rem % MILLISECONDS_PER_MINUTE.toNat
  let seconds := rem / MILLISECONDS_PER_SECOND.toNat
  let ms := rem % MILLISECONDS_PER_SECOND.toNat
  let body := durationComponent days "d" ++ durationComponent hours "h" ++
    durationComponent minutes "m" ++ durationComponent seconds "s" ++
    durationComponent ms "ms"
  if neg then "-" ++ body else body
```

For example, the canonical string representation of a duration with internal value `93784005` (one day, two hours, three minutes, four seconds, five milliseconds) is `1d2h3m4s5ms`:

```lean (name := ex5)
#eval Duration.toString (⟨93784005⟩ : Duration)
```
```leanOutput ex5
"1d2h3m4s5ms"
```

`normalize` composes parsing and serialization — it accepts any valid string and returns its canonical form:

{docstring normalize}

{docstring toString_injective}

{docstring normalize_eq_iff_parse_eq}

# Roundtrip Theorem

Parsing the canonical string representation of any duration recovers the original value. This is the headline user-facing property — `parse` and `toString` are mutually inverse on durations — and it is what underpins `toString_injective` above.

{docstring parse_toString_roundtrip}

It is a direct corollary of completeness: canonical strings are just a special case of well-formed inputs. The canonical body always has all five components present (so it is trivially nonempty), and its computed value equals the duration's stored value, so `parse_complete` applies. The maximized representation guarantees that no single component's value ever exceeds the `Int64` range, so the roundtrip never overflows.
