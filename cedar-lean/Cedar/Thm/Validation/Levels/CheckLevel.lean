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

import Cedar.Validation

namespace Cedar.Thm

/-!
This file contains some simple lemmas about the `checkLevel` and `typedAtLevel`
functions that do not need reason about the slicing functions.
-/

open Cedar.Validation

theorem check_level_checked_succ {e : TypedExpr} {n : Nat}
  (h₁ : checkLevel e n)
  : checkLevel e (1 + n)
:= by
  cases e <;> try (simp [checkLevel] at h₁ ; simp [checkLevel])
  case ite | and | or | unaryApp =>
    simp [h₁, check_level_checked_succ]
  case binaryApp op e₀ _ _ =>
    cases op
    case mem | hasTag | getTag =>
      simp only [checkLevel, Bool.and_eq_true, decide_eq_true_eq] at h₁
      unfold checkLevel
      simp only [h₁, check_level_checked_succ, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, and_true]
      constructor
      · omega
      · have h₂ : (1 + n - 1) = (1 + (n - 1)) := by omega
        simp [h₁, h₂, check_level_checked_succ]
    all_goals {
      simp only [checkLevel, Bool.and_eq_true] at h₁
      unfold checkLevel
      simp [h₁, check_level_checked_succ]
    }
  case hasAttr e _ _ | getAttr e _ _ =>
    split at h₁
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h₁ ⊢
      constructor <;> try constructor
      · simp [h₁]
      · omega
      · have h₂ : (1 + n - 1) = (1 + (n - 1)) := by omega
        simp [h₁, h₂, check_level_checked_succ]
    · simp [h₁, check_level_checked_succ]
  -- should be trivial
  case set | call => sorry
  case record => sorry
