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

import Cedar.Thm.Validation.Levels.CheckLevel
import Cedar.Thm.Validation.Levels.IfThenElse
import Cedar.Thm.Validation.Levels.GetAttr
import Cedar.Thm.Validation.Levels.HasAttr
import Cedar.Thm.Validation.Levels.UnaryApp
import Cedar.Thm.Validation.Levels.And
import Cedar.Thm.Validation.Levels.Or

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound {e : Expr} {tx : TypedExpr} {n : Nat} {c c₁ : Capabilities} {env : Environment} {request : Request} {slice entities : Entities}
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
    have ihc := @level_based_slicing_is_sound c
    have iht := @level_based_slicing_is_sound t
    have ihe := @level_based_slicing_is_sound e
    exact level_based_slicing_is_sound_if hs hc hr ht hl ihc iht ihe
  case and e₁ e₂ =>
    have ih₁ := @level_based_slicing_is_sound e₁
    have ih₂ := @level_based_slicing_is_sound e₂
    exact level_based_slicing_is_sound_and hs hc hr ht hl ih₁ ih₂
  case or e₁ e₂ =>
    have ih₁ := @level_based_slicing_is_sound e₁
    have ih₂ := @level_based_slicing_is_sound e₂
    exact level_based_slicing_is_sound_or hs hc hr ht hl ih₁ ih₂
  case unaryApp op e =>
    have ihe := @level_based_slicing_is_sound e
    exact level_based_slicing_is_sound_unary_app hs hc hr ht hl ihe
  case binaryApp => sorry -- includes tags cases which should follow the attr cases and `in` case which might be tricky
  case getAttr e _ =>
    have ihe := @level_based_slicing_is_sound e
    exact level_based_slicing_is_sound_get_attr hs hc hr ht hl ihe
  case hasAttr e _ =>
    have ihe := @level_based_slicing_is_sound e
    exact level_based_slicing_is_sound_has_attr hs hc hr ht hl ihe
  case set => sorry -- trivial recursive case maybe a little tricky
  case record => sorry -- likely to be tricky. Record cases are always hard, and here there might be an odd interaction with attribute access
  case call => sorry -- should be the same as set
