/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

/-! This file defines Cedar decimal values and functions. -/

namespace Cedar.Spec.Ext

open Cedar.Data

/--
A decimal number consists of an integer part and a fractional part.
The former is the integer number before the decimal point.
The latter is the decimal number minus its integer part.
For instance, 10.234 is a decimal number. Its integer part is 10 and its fractional part is 0.234
We restrict the number of the digits after the decimal point to 4.
-/

def DECIMAL_DIGITS : Nat := 4

abbrev Decimal := Int64

namespace Decimal

----- Definitions -----

def decimal? (i : Int) : Option Decimal :=
  Int64.mk? i

def parse (str : String) : Option Decimal :=
  match str.split (· = '.') with
  | ["-", _] => .none -- String.toInt? "-" == some 0
  | [left, right] =>
    let rlen := right.length
    if 0 < rlen ∧ rlen ≤ DECIMAL_DIGITS
    then
      match String.toInt? left, String.toNat? right with
      | .some l, .some r =>
        let l' := l * (Int.pow 10 DECIMAL_DIGITS)
        let r' := r * (Int.pow 10 (DECIMAL_DIGITS - rlen))
        let i  := if l ≥ 0 then l' + r' else l' - r'
        decimal? i
      | _, _ => .none
    else .none
  | _ => .none

def unParse (d : Decimal) : String :=
  let neg   := d < (0 : Int)
  let d     := d.natAbs
  let left  := d / (Nat.pow 10 DECIMAL_DIGITS)
  let right := d % (Nat.pow 10 DECIMAL_DIGITS)
  let right :=
    -- this is not generalized for arbitrary DECIMAL_DIGITS
    if right < 10 then ".000" ++ ToString.toString right
    else if right < 100 then ".00" ++ ToString.toString right
    else if right < 1000 then ".0" ++ ToString.toString right
    else "." ++ ToString.toString right
  (if neg then "-" else "") ++ ToString.toString left ++ right

theorem test1 : unParse ((parse "3.14").get!) = "3.1400" := by decide
theorem test2 : unParse ((parse "11.0003").get!) = "11.0003" := by decide
theorem test3 : unParse ((parse "11.003").get!) = "11.0030" := by decide
theorem test4 : unParse ((parse "11.3000").get!) = "11.3000" := by decide
theorem test5 : unParse ((parse "123.0").get!) = "123.0000" := by decide
theorem test6 : unParse ((parse "-123.0").get!) = "-123.0000" := by decide
theorem test7 : unParse ((parse "-3.14").get!) = "-3.1400" := by decide
theorem test8 : unParse ((parse "-11.0003").get!) = "-11.0003" := by decide

abbrev decimal := parse

end Decimal

end Cedar.Spec.Ext
