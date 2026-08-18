module

public import Cedar.Spec.Ext.Datetime
public import Cedar.Thm.Data.String

import all Cedar.Data.Int64
import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.Datetime
import all Cedar.Thm.Data.String
import all Init.Data.String.Search
import Std.Data.String.ToNat

namespace Cedar.Thm.Duration
open Cedar.Spec.Ext
open Datetime

/-- Apply the duration sign to a natural number: negates if `isNegative`, otherwise coerces. -/
public def signedQuantity (isNegative : Bool) (n : Nat) : Int :=
  if isNegative then Int.negOfNat n else Int.ofNat n

/-- Render an optional duration component as its string representation.
    `none` produces `""`, `some digits` produces `digits ++ suffix`. -/
public def durationChunk (digits? : Option String) (suffix : String) : String :=
  match digits? with
  | none => ""
  | some digits => digits ++ suffix

/-- Render a required duration component as `toString n ++ suffix`. -/
public def durationComponent (n : Nat) (suffix : String) : String :=
  toString n ++ suffix

/-- Lift the `Digit⁺` quantity-token predicate (`IsDigits`) to optional components:
    `none` is trivially valid. -/
-- ANCHOR: IsWfOptionalQuantity
public def IsWfOptionalQuantity : Option String → Prop
  | none => True
  | some digits => IsDigits digits
-- ANCHOR_END: IsWfOptionalQuantity

/-- The five optional digit-string components of a duration body, one per time unit.
    Each field holds `none` (unit absent) or `some digits` (unit present with that value). -/
-- ANCHOR: Components
public structure Components where
  days : Option String
  hours : Option String
  minutes : Option String
  seconds : Option String
  milliseconds : Option String
-- ANCHOR_END: Components

/-- At least one component must be present (the body cannot be empty). -/
-- ANCHOR: nonempty
public def Components.nonempty (components : Components) : Prop :=
  components.days ≠ none ∨
  components.hours ≠ none ∨
  components.minutes ≠ none ∨
  components.seconds ≠ none ∨
  components.milliseconds ≠ none
-- ANCHOR_END: nonempty

/-- Every present component must be a valid duration quantity (nonempty, parseable digits). -/
-- ANCHOR: quantitiesWf
public def Components.quantitiesWf
    (components : Components) : Prop :=
  IsWfOptionalQuantity components.days ∧
  IsWfOptionalQuantity components.hours ∧
  IsWfOptionalQuantity components.minutes ∧
  IsWfOptionalQuantity components.seconds ∧
  IsWfOptionalQuantity components.milliseconds
-- ANCHOR_END: quantitiesWf

/-- Canonical string representation: concatenate present components in order `d h m s ms`.
    Absent components contribute `""`. -/
-- ANCHOR: asString
public def Components.asString (components : Components) : String :=
  durationChunk components.days "d" ++
  durationChunk components.hours "h" ++
  durationChunk components.minutes "m" ++
  durationChunk components.seconds "s" ++
  durationChunk components.milliseconds "ms"
-- ANCHOR_END: asString

/-- Canonical maximized components for a duration value split into days, hours, minutes,
    seconds, and milliseconds. All five fields are present, including zero-valued fields. -/
public def canonicalComponents (days hours minutes seconds ms : Nat) :
    Components :=
  { days := some (toString days)
    hours := some (toString hours)
    minutes := some (toString minutes)
    seconds := some (toString seconds)
    milliseconds := some (toString ms) }

/-- Canonical maximized duration body: `days d`, `hours h`, `minutes m`, `seconds s`,
    and `milliseconds ms`, printed largest-to-smallest. -/
public def canonicalBody (days hours minutes seconds ms : Nat) : String :=
  durationComponent days "d" ++ durationComponent hours "h" ++
    durationComponent minutes "m" ++ durationComponent seconds "s" ++
    durationComponent ms "ms"

/-- A duration body string is well-formed iff it equals `components.asString` for some
    `Components` that is nonempty and has valid quantities. -/
-- ANCHOR: IsWfBody
public def IsWfBody (body : String) : Prop :=
  ∃ components : Components,
    components.nonempty ∧
    components.quantitiesWf ∧
    body = components.asString
-- ANCHOR_END: IsWfBody

/-- A duration string is well-formed iff it is the rendering of an optional `Sign` (`['-']`,
    the shared `IsWfSign`) followed by a well-formed body. Phrasing it as a rendering existential
    over the sign — rather than a disjunction that spells the `"-"` case separately — matches the
    decimal and datetime grammars. -/
-- ANCHOR: IsWfDuration
public def IsWfDuration (str : String) : Prop :=
  ∃ sign body,
    str = sign ++ body ∧
    IsWfSign sign ∧
    IsWfBody body
-- ANCHOR_END: IsWfDuration

/-- Extract the trailing natural-number token immediately before a duration suffix.
    When the suffix is absent the component is simply not present, so this yields `(0, s)`;
    when the suffix is present but the preceding digits are missing or unparseable the string is
    malformed, so this yields `none`. Mirrors the spec's `parseUnit?` failure structure. -/
-- ANCHOR: extractTrailingQuantity
public def extractTrailingQuantity (s : String) (suffix : String) : Option (Nat × String) :=
  if s.endsWith suffix then
    let rest := (s.dropEnd suffix.length).toString
    let digits := rest.toList.reverse.takeWhile Char.isDigit |>.reverse
    match toNat?' (String.ofList digits) with
    | some n => some (n, (rest.dropEnd digits.length).toString)
    | none => none
  else
    some (0, s)
-- ANCHOR_END: extractTrailingQuantity

/-- Compute the unsigned millisecond total of a duration body by extracting each component
    right-to-left (ms, s, m, h, d), failing (`none`) if any present component is unparseable. -/
-- ANCHOR: computeBodyValue
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
-- ANCHOR_END: computeBodyValue

/-- Compute the signed millisecond value: negates the unsigned total when `isNegative`. -/
public def computeSignedBodyValue (isNegative : Bool) (body : String) : Option Int :=
  (computeBodyValue body).map (fun value => if isNegative then -value else value)

/-- Compute the total signed millisecond value of a full duration string, first splitting off the
    sign via `isNegativeDuration`. Returns `none` when the body is structurally unparseable. -/
-- ANCHOR: computeValue
public def computeValue (str : String) : Option Int :=
  let (isNegative, body) := isNegativeDuration str
  computeSignedBodyValue isNegative body
-- ANCHOR_END: computeValue

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed or out-of-range inputs. -/
public def normalize (str : String) : Option String := (Duration.parse str).map Duration.toString

end Cedar.Thm.Duration
