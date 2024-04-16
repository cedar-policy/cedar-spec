/-
 Copyright Cedar Contributors. All Rights Reserved.

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

import Cedar.Data.LT

/-!
This file defines a signed 64-bit integer datatype similar to Rust's `i64`.
-/

namespace Cedar.Data

def INT64_MIN : Int := -9223372036854775808
def INT64_MAX : Int :=  9223372036854775807

abbrev Int64 := { i : Int // INT64_MIN ≤ i ∧ i ≤ INT64_MAX }

instance : Inhabited Int64 where
  default := Subtype.mk 0 (by decide)


namespace Int64

----- Definitions -----

def mk (i : Int) (h : INT64_MIN ≤ i ∧ i ≤ INT64_MAX) : Int64 :=
  Subtype.mk i h

def mk? (i : Int) : Option Int64 :=
  if h : INT64_MIN ≤ i ∧ i ≤ INT64_MAX
  then .some (mk i h)
  else .none

def lt (i₁ i₂ : Int64) : Bool := i₁.1 < i₂.1

def le (i₁ i₂ : Int64) : Bool := i₁.1 ≤ i₂.1

def add? (i₁ i₂ : Int64) : Option Int64 := mk? (i₁.1 + i₂.1)

def sub? (i₁ i₂ : Int64) : Option Int64 := mk? (i₁.1 - i₂.1)

def mul? (i₁ i₂ : Int64) : Option Int64 := mk? (i₁.1 * i₂.1)

def neg? (i₁ : Int64) : Option Int64 := mk? (- i₁.1)

----- Derivations -----
instance : LT Int64 where
  lt := fun i₁ i₂ => Int64.lt i₁ i₂

instance : LE Int64 where
  le := fun i₁ i₂ => Int64.le i₁ i₂

instance int64Lt (i₁ i₂ : Int64) : Decidable (i₁ < i₂) :=
if h : Int64.lt i₁ i₂ then isTrue h else isFalse h

instance int64Le (i₁ i₂ : Int64) : Decidable (i₁ ≤ i₂) :=
if h : Int64.le i₁ i₂ then isTrue h else isFalse h

theorem ext_iff {i₁ i₂ : Int64} : i₁ = i₂ ↔ i₁.1 = i₂.1 := by
  cases i₁; cases i₂; simp

theorem lt_def {i₁ i₂ : Int64} : i₁ < i₂ ↔ i₁.1 < i₂.1 := by
  simp [LT.lt, Int64.lt]

theorem le_def {i₁ i₂ : Int64} : i₁ ≤ i₂ ↔ i₁.1 ≤ i₂.1 := by
  simp [LE.le, Int64.le]

deriving instance Repr, DecidableEq for Int64

instance strictLT : StrictLT Int64 where
  asymmetric a b   := by
    simp [Int64.lt_def]
    omega
  transitive a b c := by
    simp [Int64.lt_def]
    omega
  connected  a b   := by
    simp [Int64.lt_def, Int64.ext_iff]
    omega

end Int64


end Cedar.Data
