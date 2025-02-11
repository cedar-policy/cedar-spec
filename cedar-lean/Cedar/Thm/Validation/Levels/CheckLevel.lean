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

theorem check_level_lit_inversion {p : Spec.Prim} {ty : CedarType} {n : Nat}
  : (checkLevel (.lit p ty) n) = LevelCheckResult.mk true false
:= by simp [checkLevel]

theorem check_level_root_invariant (n n' : Nat) (e : TypedExpr)
  : (checkLevel e n).root = (checkLevel e n').root
:= by
  unfold checkLevel
  cases e <;> simp
  case ite | unaryApp =>
    simp [check_level_root_invariant n n']
  case binaryApp op _ _ _ =>
    cases op
    case mem | getTag | hasTag =>
      simp [check_level_root_invariant (n - 1) (n' - 1)]
    all_goals { simp [check_level_root_invariant n n'] }
  case getAttr e _ _ | hasAttr e _ _ =>
    cases e.typeOf
    case entity =>
      simp [check_level_root_invariant (n - 1) (n' - 1)]
    all_goals { simp [check_level_root_invariant n n'] }
  -- Hopefully should be trivial
  case set es _ | call es _ => sorry
  case record a => sorry

theorem check_level_checked_succ {e : TypedExpr} {n : Nat}
  (h₁ : (checkLevel e n).checked)
  : (checkLevel e (1 + n)).checked
:= by
  cases e <;> try (simp [checkLevel] at h₁ ; simp [checkLevel])
  case ite | and | or | unaryApp =>
    simp [h₁, check_level_checked_succ]
  case binaryApp op e₀ _ _ =>
    cases op <;> (
      simp [checkLevel] at h₁
      simp [checkLevel]
      simp [h₁, check_level_checked_succ]
    )
    case mem | hasTag | getTag =>
      repeat constructor
      · have h₂ := check_level_root_invariant (1 + n - 1) (n - 1)
        simp [h₂, h₁]
      · omega
      · have h₂ : (1 + n - 1) = (1 + (n - 1)) := by omega
        simp [h₁, h₂, check_level_checked_succ]
  case hasAttr e _ _ | getAttr e _ _ =>
    split at h₁
    · simp [checkLevel] at h₁
      simp [checkLevel]
      repeat constructor
      · have h₂ := check_level_root_invariant (1 + n - 1) (n - 1)
        simp [h₂, h₁]
      · omega
      · have h₂ : (1 + n - 1) = (1 + (n - 1)) := by omega
        simp [h₁, h₂, check_level_checked_succ]
    · simp [h₁, check_level_checked_succ]
  -- should be trivial
  case set | call => sorry
  case record => sorry
