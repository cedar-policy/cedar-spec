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

public import Cedar.Spec.Ext.Datetime
public import Cedar.Thm.Data.String

import all Cedar.Data.Int64
import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.Datetime
import all Cedar.Thm.Data.String

namespace Cedar.Thm.Duration
open Cedar.Spec.Ext
open Datetime

/-! # Duration grammar: definitions

This file contains only grammar-level definitions: the well-formedness predicates and the value
relation. `IsWfDuration` states the syntax, `value` gives the denotation of already identified
components, and `IsDurationValue str v` combines the same witnesses to say that `str` denotes `v`.
The executable extraction machinery used to connect these definitions to `Duration.parse` lives
in `Cedar.Thm.Ext.Duration.Lemmas`. -/

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

/-- Natural-number value of an optional duration quantity. An absent component denotes zero;
    a present well-formed component is read by the shared grammar-level `natOf`. -/
-- ANCHOR: optionalNatOf
public def optionalNatOf : Option String → Nat
  | none => 0
  | some digits => natOf digits
-- ANCHOR_END: optionalNatOf

/-- Unsigned millisecond value of already identified duration components. -/
-- ANCHOR: toMillis
public def Components.toMillis (components : Components) : Int :=
  (optionalNatOf components.days : Int) * MILLISECONDS_PER_DAY +
  (optionalNatOf components.hours : Int) * MILLISECONDS_PER_HOUR +
  (optionalNatOf components.minutes : Int) * MILLISECONDS_PER_MINUTE +
  (optionalNatOf components.seconds : Int) * MILLISECONDS_PER_SECOND +
  optionalNatOf components.milliseconds
-- ANCHOR_END: toMillis

/-- The grammar's value function, applied to an already identified sign and component record. -/
-- ANCHOR: value
public def value (sign : String) (components : Components) : Int :=
  signOf sign * components.toMillis
-- ANCHOR_END: value

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
    the shared `IsWfSign`) followed by a well-formed body. Phrasing it as a rendering
    existential over the sign — rather than a disjunction that spells the `"-"` case
    separately — matches the decimal and datetime grammars. -/
-- ANCHOR: IsWfDuration
public def IsWfDuration (str : String) : Prop :=
  ∃ sign body,
    str = sign ++ body ∧
    IsWfSign sign ∧
    IsWfBody body
-- ANCHOR_END: IsWfDuration

/-- `v` is the value of the duration literal `str`: `str` is the rendering of a well-formed
    optional sign and nonempty component record, and `v` is the weighted millisecond sum assigned
    to those fields by the grammar's value function. -/
-- ANCHOR: IsDurationValue
public def IsDurationValue (str : String) (v : Int) : Prop :=
  ∃ sign components,
    str = sign ++ components.asString ∧
    IsWfSign sign ∧
    components.nonempty ∧
    components.quantitiesWf ∧
    v = value sign components
-- ANCHOR_END: IsDurationValue

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed or out-of-range inputs. -/
public def normalize (str : String) : Option String := (Duration.parse str).map Duration.toString

end Cedar.Thm.Duration
