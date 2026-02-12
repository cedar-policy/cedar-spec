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

import Cedar.Thm.WellTyped.Residual
import Cedar.Thm.WellTyped.Expr.Typechecking
import Cedar.TPE.Residual
import Cedar.Thm.TPE.Conversion
import Cedar.Data.Map

/-!
This file contains well-typedness theorems of `TypedExpr`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Validation
open Cedar.Spec
open Cedar.Spec.Ext
open Cedar.TPE
open Cedar.Data

/-- Successful evaluation of a well-typed expression should produce a value
of corresponding type. -/
theorem well_typed_is_sound {ty : TypedExpr} {v : Value} {env : TypeEnv} {request : Request} {entities : Entities} :
  InstanceOfWellFormedEnvironment request entities env →
  TypedExpr.WellTyped env ty →
  evaluate ty.toExpr request entities = .ok v →
  InstanceOfType env v ty.typeOf
:= by
  intro h₁ h₂ h₃
  rw [conversion_preserves_evaluation] at h₃
  replace h₂ := conversion_preserves_typedness h₂
  rw [conversion_preserves_typeof]
  exact residual_well_typed_is_sound h₁ h₂ h₃

end Cedar.Thm
