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

import Cedar.Thm.SymCC.Data
import Cedar.Thm.SymCC.Term.PE

/-!
This file contains useful definitions and theorems for comparing
booleans to terms.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

instance : Same Bool Term where
  same b t := t = Term.bool b

theorem same_bool_def {b : Bool} {t : Term} :
  b ∼ t ↔ t = Term.bool b
:= by simp only [Same.same]

theorem same_bool_not_true_implies_false {b : Bool} {t : Term} :
  b ∼ t →
  not t = .bool true →
  b = false
:= by
  intro h₁ h₂
  rw [same_bool_def] at h₁
  rw [h₁] at h₂
  cases b
  case false => rfl
  case true => simp only [pe_not_true, Term.prim.injEq, TermPrim.bool.injEq, Bool.false_eq_true] at h₂

theorem same_bool_not_not_true_implies_true {b : Bool} {t : Term} :
  b ∼ t →
  ¬ not t = .bool true →
  b = true
:= by
  intro h₁ h₂
  rw [same_bool_def] at h₁
  rw [h₁] at h₂
  cases b
  case false => simp only [pe_not_false, not_true_eq_false] at h₂
  case true  => rfl

end Cedar.Thm
