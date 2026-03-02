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

module

public import Cedar.Data.LT

/-!
This file defines a signed 64-bit integer datatype similar to Rust's `i64`
by adding checked arithmetic operations to Lean's Int64 datatype.
-/

namespace Int64

@[expose]
public def MIN : Int := -9223372036854775808
@[expose]
public def MAX : Int :=  9223372036854775807

----- Definitions -----

public def ofIntChecked (i : Int) (_ : MIN ≤ i ∧ i ≤ MAX) : Int64 :=
  Int64.ofInt i

public def ofInt? (i : Int) : Option Int64 :=
  if h : MIN ≤ i ∧ i ≤ MAX
  then .some (ofIntChecked i h)
  else .none

public def add? (i₁ i₂ : Int64) : Option Int64 := ofInt? (i₁.toInt + i₂.toInt)

public def sub? (i₁ i₂ : Int64) : Option Int64 := ofInt? (i₁.toInt - i₂.toInt)

public def mul? (i₁ i₂ : Int64) : Option Int64 := ofInt? (i₁.toInt * i₂.toInt)

public def neg? (i₁ : Int64) : Option Int64 := ofInt? (- i₁.toInt)

public def natAbs (i₁ : Int64) : Nat := i₁.toInt.natAbs

----- Derivations -----

theorem ext_iff {i₁ i₂ : Int64} : i₁ = i₂ ↔ i₁.toInt = i₂.toInt := by
  constructor <;> intro h₁
  · simp only [h₁]
  · cases i₁ ; cases i₂ ; rename_i i₁ i₂
    apply Int64.toBitVec.inj
    simp only [toInt, BitVec.toInt_inj] at h₁
    exact h₁

theorem lt_def_toInt {i₁ i₂ : Int64} : i₁ < i₂ ↔ i₁.toInt < i₂.toInt := by
  simp only [LT.lt, Int64.lt, BitVec.slt, toInt_toBitVec, decide_eq_true_eq]

theorem le_def_toInt {i₁ i₂ : Int64} : i₁ ≤ i₂ ↔ i₁.toInt ≤ i₂.toInt := by
  simp only [LE.le, Int64.le, BitVec.sle, toInt_toBitVec, decide_eq_true_eq]

deriving instance Repr for Int64

public instance strictLT : Cedar.Data.StrictLT Int64 where
  asymmetric a b   := by
    simp [Int64.lt_def_toInt]
    omega
  transitive a b c := by
    simp [Int64.lt_def_toInt]
    omega
  connected  a b   := by
    simp [Int64.lt_def_toInt, Int64.ext_iff]
    omega

public instance : Coe Int64 Int where
  coe i := i.toInt

end Int64
