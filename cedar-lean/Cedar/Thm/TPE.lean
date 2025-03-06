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

import Cedar.TPE
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm.TPE
open Cedar.Thm

def TypedExpr.WellTyped : TypedExpr → Environment → Prop := sorry

theorem well_typed_expr_cannot_go_wrong {env : Environment} {req : Request} {es : Entities} (x : TypedExpr) :
  TypedExpr.WellTyped x env → ∃ v, EvaluatesTo x.toExpr req es v ∧ InstanceOfType v x.typeOf := by sorry

theorem partialEvaluate_is_sound {c₁ c₂ : Capabilities}
  (x : TypedExpr)
  (req₁ : Request)
  (es₁ : Entities)
  (req₂ : PartialRequest)
  (es₂ : PartialEntities)
  (env : Environment) :
  TypedExpr.WellTyped x evn →
  RequestAndEntitiesMatchEnvironment env req₁ es₁ →
  PartialRequestAndEntitiesMatchEnvironment env req₂ es₂ →
  IsConsistent env req₁ es₁ req₂ es₂ →
  (Spec.evaluate x.toExpr req₁ es₁).toOption = (Residual.evaluate (Cedar.TPE.evaluate x req₂ es₂) req e).toOption
:= by
  sorry

end Cedar.Thm
