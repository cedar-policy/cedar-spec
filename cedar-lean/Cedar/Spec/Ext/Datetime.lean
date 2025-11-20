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

import Cedar.Data.Int64
import Std.Time
import Std.Time.Format

/-! This file defines Cedar datetime values and functions. -/

namespace Cedar.Spec.Ext

open Cedar.Data

/--
  A datetime value is measured in milliseconds and constructed from a datetime string.
  A datetime string must be of one of the forms:
    - `YYYY-MM-DD` (date only)
    - `YYYY-MM-DDThh:mm:ssZ` (UTC)
    - `YYYY-MM-DDThh:mm:ss.SSSZ` (UTC with millisecond precision)
    - `YYYY-MM-DDThh:mm:ss(+|-)hhmm` (With timezone offset in hours and minutes)
    - `YYYY-MM-DDThh:mm:ss.SSS(+|-)hhmm` (With timezone offset in hours and minutes and millisecond precision)

  Regardless of the timezone, offset is always normalized to UTC.

  The datetime type does not provide a way to create a datetime from a Unix timestamp.
  One of the readable formats listed above must be used instead.
-/
structure Datetime where
  val : Int64

def Datetime.lt (d₁ d₂ : Datetime) : Bool :=
  d₁.val < d₂.val

def Datetime.le (d₁ d₂ : Datetime) : Bool :=
  d₁.val ≤ d₂.val

instance : LT Datetime where
  lt := fun d₁ d₂ => Datetime.lt d₁ d₂

instance : LE Datetime where
  le := fun d₁ d₂ => Datetime.le d₁ d₂

instance Datetime.decLt (d₁ d₂ : Datetime) : Decidable (d₁ < d₂) :=
  if h : Datetime.lt d₁ d₂ then isTrue h else isFalse h

instance Datetime.decLe (d₁ d₂ : Datetime) : Decidable (d₁ ≤ d₂) :=
  if h : Datetime.le d₁ d₂ then isTrue h else isFalse h

instance : Coe Int64 Datetime where
  coe i := Datetime.mk i

deriving instance Repr, Inhabited, DecidableEq for Datetime

namespace Datetime

def MAX_OFFSET_SECONDS: Nat := 86400

def DateOnly : Std.Time.GenericFormat .any := datespec("yyyy-MM-dd")
def DateUTC : Std.Time.GenericFormat .any := datespec("yyyy-MM-dd'T'HH:mm:ss'Z'")
def DateUTCWithMillis : Std.Time.GenericFormat .any := datespec("yyyy-MM-dd'T'HH:mm:ss.SSS'Z'")
def DateWithOffset : Std.Time.GenericFormat .any := datespec("yyyy-MM-dd'T'HH:mm:ssxx")
def DateWithOffsetAndMillis : Std.Time.GenericFormat .any := datespec("yyyy-MM-dd'T'HH:mm:ss.SSSxx")

def datetime? (i: Int) : Option Datetime :=
  Int64.ofInt? i

def dateContainsLeapSeconds (str: String) : Bool :=
  str.length >= 20 && str.get? ⟨17⟩ == some '6' && str.get? ⟨18⟩ == some '0'

/--
  Check that the minutes for the timezone offset are in bounds (<60). We
  separately check that the whole offset is less than `MAX_OFFSET_SECONDS` which
  ensures that the hour component is in bounds. The timezone offset does not
  have a seconds component.
-/
def tzOffsetMinsLt60 (str : String) : Bool :=
  -- Short string is `DateOnly`, so no offset
  str.length <= 10 ||
  -- Ends in `Z` is either `DateUTC` or `DateUTCWithMillis`, so no offset
  str.endsWith "Z" ||
  -- `DateWithOffset` or `DateWithOffsetAndMillis` offset is last 4 chars.
  -- Minutes component is last two chars.
  match (str.takeRight 2).toNat? with
  | .some minsOffset => minsOffset < 60
  | .none => false

/--
  Workaround an issue in the datetime library by checking that the year, month,
  day, hour, minute, and second components of the datetime string are not longer
  than expected.  https://github.com/leanprover/lean4/issues/7478
-/
def checkComponentLen (str : String) : Bool :=
  match str.split (· == 'T') with
  | [date] => checkDateComponentLen date
  | [date, timeMsOffset] => checkDateComponentLen date && checkTimeMsOffsetComponentLen timeMsOffset
  | _ => false
  where
    checkDateComponentLen (str : String) : Bool :=
      match str.split (· == '-') with
      | [year, month, day] => year.length == 4 && month.length == 2 && day.length == 2
      | _ => false
    checkTimeMsOffsetComponentLen (str : String) : Bool :=
      match str.split (λ c => c == '.' || c == '+' || c == '-' || c == 'Z') with
      | time :: _ => checkTimeLen time
      | _ => false
    checkTimeLen (str : String) : Bool :=
      match str.split (· == ':') with
      | [h, m, s] => h.length == 2 && m.length == 2 && s.length == 2
      | _ => false

def parse (str: String) : Option Datetime := do
  if dateContainsLeapSeconds str then failure
  if !checkComponentLen str then failure
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

abbrev datetime := parse

/--
  A duration value is measured in milliseconds and constructed from a duration string.
  A duration string is a concatenated sequence of quantity-unit pairs where the quantity
  is a natural number and unit is one of the following:
    - `d` (for days)
    - `h` (for hours)
    - `m` (for minutes)
    - `s` (for seconds)
    - `ms` (for milliseconds)

  Duration strings are required to be ordered from largest unit to smallest
  unit, and contain one quantity per unit. Units with zero quantity may be
  omitted.

  A duration may be negative. Negative duration strings must begin with `-`.
-/
structure Duration where
  val : Int64

deriving instance Repr, Inhabited, DecidableEq for Duration

def Duration.lt (d₁ d₂ : Duration) : Bool :=
  d₁.val < d₂.val

def Duration.le (d₁ d₂ : Duration) : Bool :=
  d₁.val ≤ d₂.val

instance : LT Duration where
  lt := fun d₁ d₂ => Duration.lt d₁ d₂

instance : LE Duration where
  le := fun d₁ d₂ => Duration.le d₁ d₂

instance Duration.decLt (d₁ d₂ : Duration) : Decidable (d₁ < d₂) :=
  if h : Duration.lt d₁ d₂ then isTrue h else isFalse h

instance Duration.decLe (d₁ d₂ : Duration) : Decidable (d₁ ≤ d₂) :=
  if h : Duration.le d₁ d₂ then isTrue h else isFalse h

instance : Coe Int64 Duration where
  coe i := Duration.mk i

def MILLISECONDS_PER_SECOND: Int := 1000
def MILLISECONDS_PER_MINUTE: Int := 60000
def MILLISECONDS_PER_HOUR: Int := 3600000
def MILLISECONDS_PER_DAY: Int := 86400000

----- Definitions -----

def duration? (i: Int) : Option Duration :=
  Int64.ofInt? i

def Duration.neg? (d : Duration) : Option Duration :=
  d.val.neg?

def durationUnits? (n: Int) (suffix: String) : Option Int :=
  match Int64.ofInt? n with
  | none => none
  | some i =>
    match suffix with
    | "ms" => some i
    | "s" => some (i * MILLISECONDS_PER_SECOND)
    | "m" => some (i * MILLISECONDS_PER_MINUTE)
    | "h" => some (i * MILLISECONDS_PER_HOUR)
    | "d" => some (i * MILLISECONDS_PER_DAY)
    | _ => none

def unitsToMilliseconds (days hours minutes second milliseconds: Int) : Int :=
  days * MILLISECONDS_PER_DAY +
  hours * MILLISECONDS_PER_HOUR +
  minutes * MILLISECONDS_PER_MINUTE +
  second * MILLISECONDS_PER_SECOND +
  milliseconds

def isNegativeDuration (str: String) : Bool × String :=
  match str.front with
  | '-' => (true, str.drop 1)
  | _   => (false, str)

def parseUnit? (isNegative : Bool) (str : String) (suffix : String) : Option (Int × String) :=
  if str.endsWith suffix
  then
    let newStr := str.dropRight suffix.length
    let newStrList := newStr.toList
    let digits := ((newStrList.reverse).takeWhile Char.isDigit).reverse
    if digits.isEmpty
    then none
    else do
      let nUnsignedUnits ← String.toNat? (String.mk digits)
      let units ← if isNegative
        then durationUnits? (Int.negOfNat nUnsignedUnits) suffix
        else durationUnits? (Int.ofNat nUnsignedUnits) suffix
      some (units, newStr.dropRight digits.length)
  else
    some (0, str)

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

def Duration.parse (str : String) : Option Duration :=
  let (isNegative, restStr) := isNegativeDuration str
  parseDuration? isNegative restStr

deriving instance Repr for Duration

abbrev duration := Duration.parse

def offset (datetime: Datetime) (duration: Duration) : Option Datetime :=
  Int64.add? datetime.val duration.val

def durationSince (datetime other: Datetime) : Option Duration :=
  Int64.sub? datetime.val other.val

def toDate (datetime: Datetime) : Option Datetime :=
  let millisPerDayI64 := Int64.ofIntChecked MILLISECONDS_PER_DAY (by decide)
  if datetime.val >= 0
  then datetime? (millisPerDayI64 * (datetime.val.div millisPerDayI64))
  else if datetime.val.mod millisPerDayI64 == 0
       then datetime
       else datetime? (((datetime.val.div millisPerDayI64) - 1) * millisPerDayI64)

def toTime (datetime: Datetime) : Duration :=
  let millisPerDayI64 := Int64.ofIntChecked MILLISECONDS_PER_DAY (by decide)
  if datetime.val >= 0
  then datetime.val.mod millisPerDayI64
  else let rem := datetime.val.mod millisPerDayI64
       if rem == 0
       then rem
       else (rem + millisPerDayI64)

def Duration.toMilliseconds (duration: Duration) : Int64 :=
  duration.val

def Duration.toSeconds (duration: Duration) : Int64 :=
  duration.toMilliseconds / 1000

def Duration.toMinutes (duration: Duration) : Int64 :=
  duration.toSeconds / 60

def Duration.toHours (duration: Duration) : Int64 :=
  duration.toMinutes / 60

def Duration.toDays (duration: Duration) : Int64 :=
  duration.toHours / 24

end Datetime
