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

/-! This file defines Cedar decimal values and functions. -/

namespace Cedar.Spec.Ext

/--
A decimal number consists of an integer part and a fractional part.
The former is the integer number before the decimal point.
The latter is the decimal number minus its integer part.
For instance, 10.234 is a decimal number. Its integer part is 10 and its fractional part is 0.234
We restrict the number of the digits after the decimal point to 4.
-/

def DECIMAL_DIGITS : Nat := 4
def DECIMAL_MIN : Int := -9223372036854775808
def DECIMAL_MAX : Int :=  9223372036854775807

abbrev Decimal := { i : Int // DECIMAL_MIN ≤ i ∧ i ≤ DECIMAL_MAX }

namespace Decimal

----- Definitions -----

def decimal? (i : Int) : Option Decimal :=
  if h : DECIMAL_MIN ≤ i ∧ i ≤ DECIMAL_MAX
  then .some (Subtype.mk i h)
  else .none

def parse (str : String) : Option Decimal :=
  match str.split (· = '.') with
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

abbrev decimal := parse

def lt (d₁ d₂ : Decimal) : Bool := d₁.1 < d₂.1

def le (d₁ d₂ : Decimal) : Bool := d₁.1 ≤ d₂.1

----- Derivations -----

instance : Inhabited Decimal where
  default := Subtype.mk 0 (by simp)

instance : LT Decimal where
  lt := fun d₁ d₂ => Decimal.lt d₁ d₂

instance : LE Decimal where
  le := fun d₁ d₂ => Decimal.le d₁ d₂

instance decLt (d₁ d₂ : Decimal) : Decidable (d₁ < d₂) :=
if h : Decimal.lt d₁ d₂ then isTrue h else isFalse h

instance decLe (d₁ d₂ : Decimal) : Decidable (d₁ ≤ d₂) :=
if h : Decimal.le d₁ d₂ then isTrue h else isFalse h

end Decimal

end Cedar.Spec.Ext
