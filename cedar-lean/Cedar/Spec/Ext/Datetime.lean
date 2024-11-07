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
  DESCRIBE DATETIME AND DURATION HERE
-/
abbrev Duration := Int64

namespace Datetime

def MILLISECONDS_PER_SECOND: Int := 1000
def MILLISECONDS_PER_MINUTE: Int := 60000
def MILLISECONDS_PER_HOUR: Int := 360000
def MILLISECONDS_PER_DAY: Int := 86400000

def duration? (i : Int) : Option Duration :=
  Int64.mk? i

def durationUnits? (i: Int) (suffix: String) : Option Duration :=
  match suffix with
  | "ms" => duration? i
  | "s" => duration? (i * MILLISECONDS_PER_SECOND)
  | "m" => duration? (i * MILLISECONDS_PER_MINUTE)
  | "h" => duration? (i * MILLISECONDS_PER_HOUR)
  | "d" => duration? (i * MILLISECONDS_PER_DAY)
  | _ => none

def isNegativeDuration (str: String) : Bool × String :=
  match str.front with
  | '-' => (true, str.drop 1)
  | _   => (false, str)


def addOptionDurations (a b : Option Duration) : Option Duration :=
  match a, b with
  | some durationA, some durationB => some (Int64.add? durationA durationB).get!
  | some duration, none => some duration
  | none, some duration => some duration
  | none, none => none

def parseUnit? (str : String) (suffix: String) : Option Duration × String :=
  if str.endsWith suffix
  then
    let new_str := str.dropRight suffix.length
    let new_str_list := new_str.toList
    let digits := ((new_str_list.reverse).takeWhile Char.isDigit).reverse
    if digits.isEmpty
    then (none, str)
    else (durationUnits? (String.mk digits).toInt! suffix, new_str.dropRight digits.length)
  else (none, str)

def parseUnsignedDuration? (str : String) : Option Duration :=
  let (milliseconds, rest) := parseUnit? str "ms"
  let (seconds, rest) := parseUnit? rest "s"
  let (minutes, rest) := parseUnit? rest "m"
  let (hours, rest) := parseUnit? rest "h"
  let (days, rest) := parseUnit? rest "d"
  if rest.isEmpty
  then
    [days, hours, minutes, seconds, milliseconds].foldl (addOptionDurations · ·) none
  else none


def parse (str : String) : Option Duration :=
  let (isNegative, rest) := isNegativeDuration str
  match parseUnsignedDuration? rest with
  | some duration =>
    if isNegative then
      Int64.neg? duration
    else
      some duration
  | none => none

deriving instance Repr for Duration

#eval parse "-1d1s"
#eval Int64.mk? 500
#eval parseUnit? "12m" "m"
#eval parseUnit? "12s" "s"
#eval parseUnit? "12ms" "ms"

-- abbrev duration := parse

end Datetime
