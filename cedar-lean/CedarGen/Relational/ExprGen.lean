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
import Specimen.Correctness.Workers
import Specimen.Correctness.CompleteOf
import CedarGen.Relational.InstanceComplete

/-! # Generators for well-typed expressions

`HasType` derived with Specimen, given the environment, capabilities and type, with `scoped
derive_mutual` (open the namespace to use its generator). `ExprGen.RequestVars` favours the request
variables, which policies need for their type checks to depend on the environment;
`ExprGenBalanced` does not. Every definition the derivation emits is proved sound and complete in
`CedarGenProof.ExprGen`. -/

namespace Cedar.Validation.Relational.ExprGen

open Cedar.Spec Cedar.Data Cedar.Validation Scoring Schedules

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option maxErrors 100000
set_option specimen.prefixSearch true

namespace RequestVars
set_option specimen.sizeSplit false in
set_option specimen.deriveFloors false in
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.deferComplete true in
set_option specimen.deferSound true in
set_option specimen.completeAllSorts true in
set_option specimen.plainBinds true in
set_option specimen.parallelCodegen true in
set_option specimen.scoreType "Scoring.InversionAwareScore" in
set_option specimen.weightModifier "Cedar.Validation.Relational.ExprGen.favorRequestVars" in
set_option specimen.precomputeWeights true in
scoped derive_mutual
  generator (fun env c ty => ∃ x cout, HasType true true x c env ty cout)
end RequestVars

end Cedar.Validation.Relational.ExprGen

#specimen_blocks


#specimen_prepare_proofs
