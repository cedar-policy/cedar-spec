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

import Cedar.Data
import Cedar.Spec

/-!
This file contains generic utility functions shared by `SymCC` modules.
-/

@[inline] def BitVec.width {n : Nat} (_ : BitVec n) : Nat := n

def BitVec.signedMin (n : Nat) : Int := - 2 ^ (n-1)

def BitVec.signedMax (n : Nat) : Int := 2 ^ (n-1) - 1

def BitVec.overflows (n : Nat) (i : Int) : Bool :=
  i < (BitVec.signedMin n) ||
  i > (BitVec.signedMax n)

namespace Cedar.SymCC

open Cedar.Data

abbrev EntityTag (α) := Map String α

abbrev EntityTag.mk {α} (entity tag : α) : EntityTag α :=
  Map.mk [("entity", entity), ("tag", tag)]

abbrev EntityTag.wf {α} : EntityTag α → Bool
  | .mk _ _ => true
  | _       => false

end Cedar.SymCC
