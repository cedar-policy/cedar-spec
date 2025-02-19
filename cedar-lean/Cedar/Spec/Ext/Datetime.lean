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

deriving instance Repr, Inhabited, DecidableEq for Datetime

-- instance : Ord Datetime where
--   compare a b := Int64.compare d₁.val d₂.val

-- abbrev Datetime := Int64

namespace Datetime

def MAX_OFFSET_SECONDS: Nat := 86400

def DateOnly : Std.Time.GenericFormat .any := datespec("uuuu-MM-dd")
def DateUTC : Std.Time.GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss'Z'")
def DateUTCWithMillis : Std.Time.GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss.SSS'Z'")
def DateWithOffset : Std.Time.GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ssxx")
def DateWithOffsetAndMillis : Std.Time.GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss.SSSxx")

def datetime? (i: Int) : Option Datetime :=
  Int64.ofInt? i |>.map Datetime.mk

def dateContainsLeapSeconds (str: String) : Bool :=
  str.length >= 20 && str.get? ⟨17⟩ == some '6' && str.get? ⟨18⟩ == some '0'

def parse (str: String) : Option Datetime := do
  if dateContainsLeapSeconds str then failure
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

def MILLISECONDS_PER_SECOND: Int := 1000
def MILLISECONDS_PER_MINUTE: Int := 60000
def MILLISECONDS_PER_HOUR: Int := 360000
def MILLISECONDS_PER_DAY: Int := 86400000

----- Definitions -----

def duration? (i: Int) : Option Duration :=
  Int64.ofInt? i |>.map Duration.mk

def Duration.neg? (d : Duration) : Option Duration :=
  d.val.neg? |>.map Duration.mk

def durationUnits? (n: Nat) (suffix: String) : Option Int :=
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

def parseUnit? (str : String) (suffix : String) : Option (Int × String) :=
  if str.endsWith suffix
  then
    let newStr := str.dropRight suffix.length
    let newStrList := newStr.toList
    let digits := ((newStrList.reverse).takeWhile Char.isDigit).reverse
    if digits.isEmpty
    then none
    else do
      let units ← durationUnits? (← String.toNat? (String.mk digits)) suffix
      some (units, newStr.dropRight digits.length)
  else
    some (0, str)

def parseUnsignedDuration? (str : String) : Option Duration := do
  if str.isEmpty then failure
  let (milliseconds, restStr) ← parseUnit? str "ms"
  let (seconds, restStr) ← parseUnit? restStr "s"
  let (minutes, restStr) ← parseUnit? restStr "m"
  let (hours, restStr) ← parseUnit? restStr "h"
  let (days, restStr) ← parseUnit? restStr "d"
  if restStr.isEmpty
  then duration? (days + hours + minutes + seconds + milliseconds)
  else none

def Duration.parse (str : String) : Option Duration :=
  let (isNegative, restStr) := isNegativeDuration str
  match parseUnsignedDuration? restStr with
  | some duration =>
    if isNegative
    then duration.neg?
    else some duration
  | none => none

deriving instance Repr for Duration

abbrev duration := Duration.parse

def offset (datetime: Datetime) (duration: Duration) : Option Datetime :=
  Int64.add? datetime.val duration.val |>.map Datetime.mk

def durationSince (datetime other: Datetime) : Option Duration :=
  Int64.sub? datetime.val other.val |>.map Duration.mk

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
  then Duration.mk (datetime.val.mod millisPerDayI64)
  else let rem := datetime.val.mod millisPerDayI64
       if rem == 0
       then Duration.mk rem
       else Duration.mk (rem + millisPerDayI64)

end Datetime
