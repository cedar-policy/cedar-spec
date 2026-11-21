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

import CedarGen.Relational.InstanceLaws
import Specimen.Basalt
import Specimen.Correctness.FloorOf

/-! # Weightings for the expression generators

The weight modifiers `ExprGen` (`RequestVars`) and `ExprGenBalanced` (`Balanced`) derive `HasType`
under, in a module of their own so that the two derivations build in parallel. -/

namespace Cedar.Validation.Relational.ExprGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Scoring Schedules

def favorStructure (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  match ctorName with
  | .str _ "hasTagAnyBool" | .str _ "hasTagTt" | .str _ "hasTagFf" | .str _ "getTag" =>
    baseWeight * 2 + 1
  | .str (.str _ "HasType") "record"     => baseWeight * 8 + 1
  | .str (.str _ "HasTypeRecord") "cons" => baseWeight * 6 + 1
  | .str _ "unaryAppIsEmpty"             => baseWeight * 10 + 1
  | .str _ "binaryAppEqLitSame" | .str _ "binaryAppEqLitDiff" => max 1 (baseWeight / 2)
  | .str _ "getAttrEntity" | .str _ "getAttrRecord" => baseWeight * 2 + 1
  | .str (.str _ "HasType") "set"        => baseWeight * 3 + 1
  | .str _ "callExt"                     => baseWeight * 2 + 1
  | _                                    => baseWeight

def favorRequestVars (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  match ctorName with
  | .str _ "varPrincipal" | .str _ "varResource" | .str _ "varContext" => baseWeight * 6 + 1
  | .str _ "getAttrEntity" | .str _ "hasAttrEntity" => baseWeight * 4 + 1
  | .str _ "getAttrRecord" | .str _ "hasAttrRecord" => baseWeight * 3 + 1
  | .str _ "hasTagAnyBool" | .str _ "hasTagTt" | .str _ "hasTagFf" | .str _ "getTag" =>
    baseWeight * 2 + 1
  | .str (.str _ "HasType") "record"     => baseWeight * 8 + 1
  | .str (.str _ "HasTypeRecord") "cons" => baseWeight * 6 + 1
  | .str _ "unaryAppIsEmpty"             => baseWeight * 10 + 1
  | .str _ "binaryAppEqLitSame" | .str _ "binaryAppEqLitDiff" => max 1 (baseWeight / 2)
  | .str (.str _ "HasType") "set"        => baseWeight * 3 + 1
  | .str _ "callExt"                     => baseWeight * 2 + 1
  | _                                    => baseWeight

end Cedar.Validation.Relational.ExprGen
