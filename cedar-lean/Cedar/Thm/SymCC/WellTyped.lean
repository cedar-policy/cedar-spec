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

import Cedar.Thm.SymbolicCompilation

/-! This file contains some results about `wellTypedPolicies` and `wellTypedPolicy`. -/

namespace Cedar.Thm

open Spec SymCC Validation

/-
Given `wellTypedPolicy p Γ = .some p'`
WTS:
- `env.StronglyWellFormedForPolicy p → env.StronglyWellFormedForPolicy p'`

Given wellTypedPolicies ps Γ = .some ps'
- `env.StronglyWellFormedForPolicies ps → env.StronglyWellFormedForPolicies ps'`
- `evaluate p.toExpr env.request env.entities = evaluate p'.toExpr env.request env.entities`
- `Spec.isAuthorized env.request env.entities ps = Spec.isAuthorized env.request env.entities ps'`
-/

end Cedar.Thm
