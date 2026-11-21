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

import CedarGen.Relational.SchemaGenFLaws

/-! # The flagged schema generator, derived

`GenTypeEnvF` derived with Specimen, sound and complete (`specimen.emitSound`,
`specimen.emitComplete`), delegating to the producers of `SchemaGenFLaws`. -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.Validation.Relational.Schema
open Scoring Schedules

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-! ## Weights -/

/-- Lists of names and actions grow with the size; record attributes and the rarely needed free
parent lists less. -/
def favorSchemaF (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  match ctorName with
  | .str (.str _ "RawNames") "cons"       => baseWeight * 64 + 1
  | .str (.str _ "RawUids") "cons"        => baseWeight * 64 + 1
  | .str (.str _ "KindOf") "std"          => baseWeight * 4 + 1
  | .str (.str _ "AppliesF") "cons"       => baseWeight * 2 + 1
  | .str (.str _ "AppliesBounded") "cons" => baseWeight * 2 + 1
  | .str (.str _ "ParentsF") "denseStdT"  => baseWeight * 8 + 1
  | .str (.str _ "ParentsF") "denseStdF"  => baseWeight * 4 + 1
  | .str (.str _ "ParentsF") "denseAllF"  => baseWeight * 4 + 1
  | .str (.str _ "AParents") "denseLowerT" => baseWeight * 8 + 1
  | .str (.str _ "AParents") "denseLowerF" => baseWeight * 4 + 1
  | .str (.str _ "AParents") "denseAllF"  => baseWeight * 4 + 1
  | .str (.str _ "ActsR") "cons"          => baseWeight * 2 + 1
  | .str (.str _ "CloseEnts") "keep"      => baseWeight * 8 + 1
  | _                                     => baseWeight

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.precomputeWeights true in
set_option specimen.weightModifier "Cedar.Validation.Relational.SchemaGen.favorSchemaF" in
set_option specimen.emitSound true in
set_option specimen.emitComplete true in
set_option specimen.reportPhaseTimers true in
derive_mutual
  generator (fun m a e d c n i budget => ∃ r env, GenTypeEnvF m a e d c n i r budget env)

end Cedar.Validation.Relational.SchemaGen
