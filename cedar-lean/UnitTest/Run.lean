/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Std

/-! This file defines simple utilities for unit testing. -/

namespace UnitTest

def pass : IO Bool := pure true

def fail (name : String) (message : String) : IO Bool := do
  IO.println "--------------------"
  IO.println s!"FAILED: {name}"
  IO.println message
  IO.println "--------------------"
  pure false

def checkEq {α} [DecidableEq α] [Repr α] (actual expected : α) (name : String) : IO Bool :=
  if actual = expected
  then pass
  else fail name s!"actual: {reprArg actual}\nexpected: {reprArg expected}"

structure TestCase where
  name : String
  exec : String → IO Bool

structure TestSuite where
  name  : String
  tests : List TestCase

def test (name : String) (exec : String → IO Bool) : TestCase :=
  TestCase.mk name exec

def suite (name : String) (tests : List TestCase) : TestSuite :=
  TestSuite.mk name tests

/--
Runs the test case and returns true if the tests passes.
Otherwise prints the error message and returns false.
-/
def TestCase.run (case : TestCase) : IO Bool := case.exec case.name

/--
Runs the test suite, prints the stats, and returns the number of
failed test cases.
-/
def TestSuite.run (suite : TestSuite) : IO Nat := do
  IO.println "===================="
  IO.println s!"Running {suite.name}"
  let outcomes ← suite.tests.mapM TestCase.run
  let total := outcomes.length
  let successes := outcomes.count true
  let failures := total - successes
  IO.println s!"{successes} success(es) {failures} failure(s) {total} test(s) run"
  pure failures

/--
Runs all the given test suites and prints the stats.
-/
def TestSuite.runAll (suites : List TestSuite) : IO UInt32 := do
  let outcomes ← suites.mapM TestSuite.run
  let total := suites.foldl (fun n ts => n + ts.tests.length) 0
  let failures := outcomes.foldl (· + ·) 0
  let successes := total - failures
  IO.println "====== TOTAL ======="
  IO.println s!"{successes} success(es) {failures} failure(s) {total} test(s) run"
  pure (UInt32.ofNat failures)

end UnitTest
