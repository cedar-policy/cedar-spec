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

import CedarGen.Relational.ExprGenWeights

/-! # Generator for well-typed expressions, balanced

`HasType` derived with Specimen, given the environment, capabilities and type, under
`ExprGen.Balanced`'s weights: it raises the rules Specimen otherwise rarely picks (tags, record and
set literals, `isEmpty`, attribute access and extension calls). `open` the namespace to use it. -/

namespace Cedar.Validation.Relational.ExprGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Scoring Schedules

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

namespace Balanced
set_option specimen.parallelCodegen true in
set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.weightModifier "Cedar.Validation.Relational.ExprGen.favorStructure" in
set_option specimen.precomputeWeights true in
scoped derive_mutual
  generator (fun env c ty => ∃ x cout, HasType true true x c env ty cout)
end Balanced

end Cedar.Validation.Relational.ExprGen
