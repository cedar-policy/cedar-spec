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

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Types

import Cedar.Thm.Validation.Levels.Basic
import Cedar.Thm.Validation.Levels.CheckLevel
import Cedar.Thm.Validation.Levels.IfThenElse
import Cedar.Thm.Validation.Levels.GetAttr
import Cedar.Thm.Validation.Levels.HasAttr
import Cedar.Thm.Validation.Levels.UnaryApp
import Cedar.Thm.Validation.Levels.BinaryApp
import Cedar.Thm.Validation.Levels.And
import Cedar.Thm.Validation.Levels.Or
import Cedar.Thm.Validation.Levels.Record

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_expr {e : Expr} {n : Nat} {tx : TypedExpr} {c c₁ : Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = Except.ok (tx, c₁))
  (hl : TypedExpr.AtLevel tx n) :
  evaluate e request entities = evaluate e request slice
:= by
  cases e
  case lit => simp [evaluate]
  case var v => cases v <;> simp [evaluate]
  case ite c t e =>
    have ihc := @level_based_slicing_is_sound_expr c
    have iht := @level_based_slicing_is_sound_expr t
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_if hs hc hr ht hl ihc iht ihe
  case and e₁ e₂ =>
    have ih₁ := @level_based_slicing_is_sound_expr e₁
    have ih₂ := @level_based_slicing_is_sound_expr e₂
    exact level_based_slicing_is_sound_and hs hc hr ht hl ih₁ ih₂
  case or e₁ e₂ =>
    have ih₁ := @level_based_slicing_is_sound_expr e₁
    have ih₂ := @level_based_slicing_is_sound_expr e₂
    exact level_based_slicing_is_sound_or hs hc hr ht hl ih₁ ih₂
  case unaryApp op e =>
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_unary_app hs hc hr ht hl ihe
  case binaryApp op e₁ e₂ =>
    have ihe₁ := @level_based_slicing_is_sound_expr e₁
    have ihe₂ := @level_based_slicing_is_sound_expr e₂
    exact level_based_slicing_is_sound_binary_app hs hc hr ht hl ihe₁ ihe₂
  case getAttr e _ =>
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_get_attr hs hc hr ht hl ihe
  case hasAttr e _ =>
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_has_attr hs hc hr ht hl ihe
  case set => sorry -- trivial recursive case maybe a little tricky
  case call => sorry -- should be the same as set
  case record rxs =>
    have ih : ∀ x ∈ rxs, TypedAtLevelIsSound x.snd := by
      intro x hx
      have _ : sizeOf x.snd < sizeOf (Expr.record rxs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        rw [Prod.mk.sizeOf_spec] at h₁
        simp only [Expr.record.sizeOf_spec]
        omega
      exact @level_based_slicing_is_sound_expr x.snd
    exact level_based_slicing_is_sound_record hs hc hr ht hl ih
termination_by e

theorem level_based_slicing_is_sound {p : Policy} {n : Nat} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (htl : typecheckAtLevel p env n = true) :
  evaluate p.toExpr request entities = evaluate p.toExpr request slice
:= by
  simp only [typecheckAtLevel] at htl
  cases ht : typeOf p.toExpr ∅ env <;> (
    rw [ht] at htl
    simp only [Bool.false_eq_true] at htl
  )
  rw [←level_spec] at htl
  have hc := empty_capabilities_invariant request entities
  exact level_based_slicing_is_sound_expr hs hc hr ht htl
