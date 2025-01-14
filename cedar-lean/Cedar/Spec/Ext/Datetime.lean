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

/-! This file defines Cedar datetime values and functions. -/

namespace Cedar.Spec.Ext

open Cedar.Data

namespace Datetime

/--
  A datetime value is measured in milliseconds and constructed from a datetime string.
  A datetime string must be of one of the forms:
  - `YYYY-MM-DD` (date only)
  - `YYYY-MM-DDThh:mm:ssZ` (UTC)
  - `YYYY-MM-DDThh:mm:ss.SSSZ` (UTC with millisecond precision)
  - `YYYY-MM-DDThh:mm:ss(+|-)hhmm` (With timezone offset in hours and minutes)
  - `YYYY-MM-DDThh:mm:ss.SSS(+|-)hhmm` (With timezone offset in hours and minutes and millisecond precision)
-/
abbrev Datetime := Int64

def DateOnly : Std.Time.GenericFormat .any := datespec("uuuu-MM-dd")
def DateUTC : Std.Time.GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss'Z'")
def DateUTCWithMillis : Std.Time.GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss.SSS'Z'")
def DateWithOffset : Std.Time.GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ssxx")
def DateWithOffsetAndMillis : Std.Time.GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss.SSSxx")

abbrev datetime? := Int64.ofInt?

def parse (str: String) : Option Datetime :=
  let parseFun := match str.length with
  | 10 => DateOnly.parse
  | 20 => DateUTC.parse
  | 24 => if str.get? ⟨23⟩ == some 'Z'
          then DateUTCWithMillis.parse
          else DateWithOffset.parse
  | 28 => DateWithOffsetAndMillis.parse
  | _ => (fun _ => Except.error "invalid string length")

  let datetime := parseFun str
  match datetime with
  | Except.ok val => datetime? val.toTimestamp.toMillisecondsSinceUnixEpoch.toInt
  | _ => none

#eval DateOnly.parse "2022-10-10"
#eval DateUTC.parse "2022-10-10T00:00:00Z"
#eval DateUTCWithMillis.parse "2022-10-10T03:35:00.001Z"
#eval DateWithOffset.parse "2022-10-10T03:35:00+0500"
#eval DateWithOffsetAndMillis.parse "2022-10-10T03:35:00.000+0500"

#eval parse "2022-10-10"
#eval parse "2022-10-10T00:00:00Z"
#eval parse "2022-10-10T03:35:00.001Z"
#eval parse "2022-10-10T03:35:00+0500"
#eval parse "2022-10-10T03:35:00.000+0500"

#eval "2022-10-10".length
#eval "2022-10-10T00:00:00Z".length
#eval "2022-10-10T03:35:00.001Z".length
#eval "2022-10-10T03:35:00+05:00".length
#eval "2022-10-10T03:35:00.000+05:00".length
-- #eval (parse "1969-12-31") == (Int64.ofInt (-86400000 :Int))
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
abbrev Duration := Int64

def MILLISECONDS_PER_SECOND: Int := 1000
def MILLISECONDS_PER_MINUTE: Int := 60000
def MILLISECONDS_PER_HOUR: Int := 360000
def MILLISECONDS_PER_DAY: Int := 86400000

----- Definitions -----

abbrev duration? := Int64.ofInt?

def durationUnits? (n: Nat) (suffix: String) : Option Duration :=
  match Int64.ofInt? n with
  | none => none
  | some i =>
    match suffix with
    | "ms" => duration? i
    | "s" => duration? (i * MILLISECONDS_PER_SECOND)
    | "m" => duration? (i * MILLISECONDS_PER_MINUTE)
    | "h" => duration? (i * MILLISECONDS_PER_HOUR)
    | "d" => duration? (i * MILLISECONDS_PER_DAY)
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

def parseUnit? (str : String) (suffix : String) : Option (Duration × String) :=
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
    some (⟨0, (by decide)⟩, str)

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
    then Int64.neg? duration
    else some duration
  | none => none

deriving instance Repr for Duration

abbrev duration := Duration.parse

end Datetime
