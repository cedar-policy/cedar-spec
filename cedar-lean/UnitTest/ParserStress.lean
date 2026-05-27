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

import Cedar.Frontend.Parser
import UnitTest.Run

/-! This file defines stress tests for parsing large policies and expressions. -/

namespace UnitTest.ParserStress

open UnitTest Cedar.Spec.Cst.Parser

private def testParseFileOk (name : String) (path : String) (numPolicies : Nat) : TestCase IO :=
  test name ⟨fun _ => do
    let input ← IO.FS.readFile path
    match parse input with
    | .ok ps => checkEq ps.ps.length numPolicies
    | .error e => pure (.error s!"parse failed: {e}")⟩

private def testParseOk (name : String) (input : String) (numPolicies : Nat) : TestCase IO :=
  test name ⟨fun _ => match parse input with
    | .ok ps => checkEq ps.ps.length numPolicies
    | .error e => pure (.error s!"parse failed: {e}")⟩

def testsForStressFile :=
  suite "ParserStress.File"
  [
    testParseFileOk "stress.cedar"
      "UnitTest/parser_tests/stress.cedar" 20
  ]

def testsForLargeExpressions :=
  suite "ParserStress.LargeExpressions"
  [
    testParseOk "50-element set"
      ("permit(principal, action, resource) when { [" ++
       String.intercalate ", " (List.range 50 |>.map toString) ++
       "].contains(context.x) };") 1,
    testParseOk "30-field record"
      ("permit(principal, action, resource) when { {" ++
       String.intercalate ", " (List.range 30 |>.map fun i => s!"f{i}: {i}") ++
       "} == context.x };") 1,
    testParseOk "30-element action list"
      ("permit(principal, action in [" ++
       String.intercalate ", " (List.range 30 |>.map fun i => s!"Action::\"{i}\"") ++
       "], resource);") 1,
    testParseOk "30-deep member access"
      ("permit(principal, action, resource) when { context" ++
       String.join (List.replicate 30 ".x") ++
       " == \"deep\" };") 1,
    testParseOk "20-deep nested parens"
      ("permit(principal, action, resource) when { " ++
       String.join (List.replicate 20 "(") ++
       "context.x" ++
       String.join (List.replicate 20 ")") ++
       " == 1 };") 1,
    testParseOk "15 when/unless clauses"
      ("permit(principal, action, resource)" ++
       String.join (List.range 10 |>.map fun _ => " when { true }") ++
       String.join (List.range 5 |>.map fun _ => " unless { false }") ++
       ";") 1,
    testParseOk "20 annotations"
      (String.join (List.range 20 |>.map fun i => s!"@a{i}(\"v{i}\")\n") ++
       "permit(principal, action, resource);") 1
  ]

def tests : List (TestSuite IO) :=
  [testsForStressFile,
   testsForLargeExpressions]

end UnitTest.ParserStress
