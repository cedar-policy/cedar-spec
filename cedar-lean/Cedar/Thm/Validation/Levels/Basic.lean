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

def TypedAtLevelIsSound (e : Expr) : Prop := ∀ {n : Nat} {tx : TypedExpr} {c c₁ : Capabilities} {env :Environment} {request : Request} {entities slice : Entities},
  slice = entities.sliceAtLevel request n →
  CapabilitiesInvariant c request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c env = Except.ok (tx, c₁) →
  tx.AtLevel env n →
  evaluate e request entities = evaluate e request slice
