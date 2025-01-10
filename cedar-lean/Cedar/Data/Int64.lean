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

import Cedar.Data.LT

/-!
This file defines a signed 64-bit integer datatype similar to Rust's `i64`
by adding checked arithmetic operations to Lean's Int64 datatype.
-/

namespace Int64

def MIN : Int := -9223372036854775808
def MAX : Int :=  9223372036854775807

----- Definitions -----

def ofIntChecked (i : Int) (_ : MIN ≤ i ∧ i ≤ MAX) : Int64 :=
  Int64.ofInt i

def ofInt? (i : Int) : Option Int64 :=
  if h : MIN ≤ i ∧ i ≤ MAX
  then .some (ofIntChecked i h)
  else .none

def add? (i₁ i₂ : Int64) : Option Int64 := ofInt? (i₁.toInt + i₂.toInt)

def sub? (i₁ i₂ : Int64) : Option Int64 := ofInt? (i₁.toInt - i₂.toInt)

def mul? (i₁ i₂ : Int64) : Option Int64 := ofInt? (i₁.toInt * i₂.toInt)

def neg? (i₁ : Int64) : Option Int64 := ofInt? (- i₁.toInt)

def natAbs (i₁ : Int64) : Nat := i₁.toInt.natAbs

----- Derivations -----

theorem ext_iff {i₁ i₂ : Int64} : i₁ = i₂ ↔ i₁.toInt = i₂.toInt := by
  constructor <;> intro h₁
  · simp only [h₁]
  · cases i₁ ; cases i₂ ; rename_i i₁ i₂
    simp only [mk.injEq]
    simp only [toInt, BitVec.toInt_inj, Int64.toBitVec, UInt64.toBitVec_inj] at h₁
    exact h₁

theorem lt_def {i₁ i₂ : Int64} : i₁ < i₂ ↔ i₁.toInt < i₂.toInt := by
  simp [LT.lt, Int64.lt, BitVec.slt, Int64.toInt]

theorem le_def {i₁ i₂ : Int64} : i₁ ≤ i₂ ↔ i₁.toInt ≤ i₂.toInt := by
  simp [LE.le, Int64.le, BitVec.sle, Int64.toInt]

deriving instance Repr for Int64

instance strictLT : Cedar.Data.StrictLT Int64 where
  asymmetric a b   := by
    simp [Int64.lt_def]
    omega
  transitive a b c := by
    simp [Int64.lt_def]
    omega
  connected  a b   := by
    simp [Int64.lt_def, Int64.ext_iff]
    omega

instance : Coe Int64 Int where
  coe i := i.toInt

end Int64
