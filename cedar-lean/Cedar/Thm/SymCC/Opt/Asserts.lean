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

import Cedar.SymCC

namespace Cedar.Thm

open Cedar.Spec Cedar.SymCC

/--
A notion of equivalence for `Asserts`, suited to the purposes of Cedar.Thm.SymCC.Opt.
-/
inductive Asserts.Equiv : Asserts → Asserts → Prop where
  -- `Asserts` are equivalent to themselves
  | rfl (a : Asserts) : Equiv a a
  -- `Asserts` are also equivalent if constant-false appears in both lists, regardless of what else does or does not appear in the `Asserts`
  | constantFalse {a₁ a₂ : Asserts} (h₁ : .prim (.bool false) ∈ a₁) (h₂ : .prim (.bool false) ∈ a₂) : Equiv a₁ a₂

infix:50 " ~ " => Asserts.Equiv

-- lifting the `~` notation to work on `Except ε Asserts`
def ResultAssertsEquiv (res₁ res₂ : Except ε Asserts) : Prop :=
  match res₁, res₂ with
  | .ok a₁,    .ok a₂    => Asserts.Equiv a₁ a₂
  | .error e₁, .error e₂ => e₁ = e₂
  | _,         _         => false
infix:50 " ~ " => ResultAssertsEquiv

/--
Symmetry for Asserts.Equiv
-/
theorem Asserts.Equiv.symm {a₁ a₂ : Asserts} :
  a₁ ~ a₂ → a₂ ~ a₁
:= by
  intro heqv ; cases heqv
  case rfl => apply Asserts.Equiv.rfl
  case constantFalse h₁ h₂ => apply Asserts.Equiv.constantFalse h₂ h₁

/--
Equivalent `Asserts` produce the same output in `checkUnsatAsserts`
-/
theorem Asserts.Equiv.checkUnsatAsserts {a₁ a₂ : Asserts} {εnv : SymEnv} :
  a₁ ~ a₂ →
  checkUnsatAsserts a₁ εnv = checkUnsatAsserts a₂ εnv
:= by
  simp [SymCC.checkUnsatAsserts]
  intro heqv ; cases heqv
  case rfl => rfl
  case constantFalse h₁ h₂ => simp [h₁, h₂]

/--
Equivalent `Asserts` produce the same output in `checkSatAsserts`
-/
theorem Asserts.Equiv.checkSatAsserts {a₁ a₂ : Asserts} (εnv : SymEnv) :
  a₁ ~ a₂ →
  checkSatAsserts a₁ εnv = checkSatAsserts a₂ εnv
:= by
  simp [SymCC.checkSatAsserts]
  intro heqv ; cases heqv
  case rfl => rfl
  case constantFalse h₁ h₂ => simp [h₁, h₂]

/--
Equivalent `Asserts` produce the same output in `satAsserts?`
-/
theorem Asserts.Equiv.satAsserts? {a₁ a₂ : Asserts} (ps : Policies) (εnv : SymEnv) :
  a₁ ~ a₂ →
  satAsserts? ps a₁ εnv = satAsserts? ps a₂ εnv
:= by
  intro heqv
  simp [SymCC.satAsserts?, Asserts.Equiv.checkSatAsserts εnv heqv]
