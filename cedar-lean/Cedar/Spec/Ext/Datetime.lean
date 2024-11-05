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

def duration_in? (i: Int) (suffix: String) : Option Duration :=
  match suffix with
  | "ms" => duration? i
  | "s" => duration? (i * MILLISECONDS_PER_SECOND)
  | "m" => duration? (i * MILLISECONDS_PER_MINUTE)
  | "h" => duration? (i * MILLISECONDS_PER_HOUR)
  | "d" => duration? (i * MILLISECONDS_PER_DAY)
  | _ => none

def is_negative (str: String) : Bool × String :=
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
  let chars := str.toList
  let (char_digits, rest) := chars.span Char.isDigit
  if char_digits.isEmpty
  then (none, str)
  else
    let rest_str := String.mk rest
    if rest_str.startsWith suffix
    then (duration_in? (String.mk char_digits).toInt! suffix, rest_str.drop suffix.length)
    else (none, str)

def parseDur? (str : String) : Option Duration :=
  let (days, rest) := parseUnit? str "d"
  let (hours, rest) := parseUnit? rest "h"
  let (minutes, rest) := parseUnit? rest "m"
  let (seconds, rest) := parseUnit? rest "s"
  let (milliseconds, rest) := parseUnit? rest "ms"
  if rest.isEmpty
  then
    [days, hours, minutes, seconds, milliseconds].foldl (addOptionDurations · ·) none
  else none


def parse (str : String) : Option Duration :=
  let (is_neg, new_str) := is_negative str
  match parseDur? new_str with
  | some duration =>
    if is_neg then
      Int64.neg? duration
    else
      some duration
  | none => none

deriving instance Repr for Duration

#eval parse "1d1ms"
#eval Int64.mk? 500
#eval parseUnit? "12m" "m"
#eval parseUnit? "12s" "s"
#eval parseUnit? "12ms" "ms"

-- abbrev duration := parse

end Datetime
