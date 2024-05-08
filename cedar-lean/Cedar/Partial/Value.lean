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

import Cedar.Partial.Expr
import Cedar.Spec.Value

/-!
This file defines Cedar partial values.
-/

namespace Cedar.Partial

inductive Value where
  | value (v : Spec.Value)
  | residual (r : Partial.Expr)

deriving instance Repr, DecidableEq, Inhabited for Value

def Value.asPartialExpr (v : Partial.Value) : Partial.Expr :=
  match v with
  | .value v    => v.asPartialExpr
  | .residual r => r

instance : Coe Spec.Value Partial.Value where
  coe := Partial.Value.value

end Cedar.Partial
