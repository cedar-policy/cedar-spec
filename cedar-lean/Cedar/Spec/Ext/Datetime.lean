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

/-! This file defines Cedar datetime values and functions. -/

namespace Cedar.Spec.Ext

open Cedar.Data

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
abbrev Duration := Data.Int64

namespace Datetime

def MILLISECONDS_PER_SECOND: Int := 1000
def MILLISECONDS_PER_MINUTE: Int := 60000
def MILLISECONDS_PER_HOUR: Int := 360000
def MILLISECONDS_PER_DAY: Int := 86400000

----- Definitions -----

def duration? (i : Int) : Option Duration :=
  Int64.mk? i

def durationUnits? (n: Nat) (suffix: String) : Option Duration :=
  match Int64.mk? n with
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
