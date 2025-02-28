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

import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Levels.CheckLevel

namespace Cedar.Thm

/-!
Basic definitions for levels proof
-/

open Cedar.Spec
open Cedar.Validation

def TypedAtLevelIsSound (e : Expr) : Prop := ∀ {n nmax : Nat} {tx : TypedExpr} {c c₁ : Capabilities} {env :Environment} {request : Request} {entities slice : Entities},
  nmax >= n →
  slice = entities.sliceAtLevel request nmax→
  CapabilitiesInvariant c request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c env = Except.ok (tx, c₁) →
  TypedExpr.AtLevel tx n nmax →
  evaluate e request entities = evaluate e request slice

theorem mapm_eval_congr_entities {xs : List Expr} {request : Request} {entities slice : Entities}
  (he : ∀ (x : Expr), x ∈ xs → evaluate x request entities = evaluate x request slice) :
  List.mapM (fun x => evaluate x request entities) xs = List.mapM (fun x => evaluate x request slice) xs
:= by
  cases xs
  case nil => simp
  case cons x xs =>
    simp only [List.mapM_cons, bind_pure_comp]
    rw [he x (by simp)]
    have he' : ∀ (x : Expr), x ∈ xs → evaluate x request entities = evaluate x request slice := by
      intros x' hx'
      replace hx' : x' ∈ x :: xs := by simp [hx']
      exact he x' hx'
    cases evaluate x request slice <;> simp only [Except.bind_err, Except.bind_ok]
    have ih := mapm_eval_congr_entities he'
    rw [ih]
