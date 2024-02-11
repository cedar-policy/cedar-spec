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

variable [Monad m] [MonadLiftT IO m]

abbrev TestResult := Except String Unit

def checkEq {α} [DecidableEq α] [Repr α] (actual expected : α) : m TestResult :=
  if actual = expected
  then return .ok ()
  else return .error s!"actual: {reprArg actual}\nexpected: {reprArg expected}"

structure TestCase (m) [Monad m] [MonadLiftT IO m] extends Thunk (m TestResult) where
  name : String

structure TestSuite (m) [Monad m] [MonadLiftT IO m] where
  name  : String
  tests : List (TestCase m)

def test (name : String) (exec : Thunk (m TestResult)) : TestCase m :=
  TestCase.mk exec name

def suite (name : String) (tests : List (TestCase m)) : TestSuite m :=
  TestSuite.mk name tests

/--
Runs the test case and returns true if the tests passes.
Otherwise prints the error message and returns false.
-/
def TestCase.run (case : TestCase m) : m Bool := do
  match (← case.get) with
  | .ok _      =>
    return true
  | .error msg =>
    IO.println "--------------------"
    IO.println s!"FAILED: {case.name}"
    IO.println msg
    IO.println "--------------------"
    return false

/--
Runs the test suite, prints the stats, and returns the number of
failed test cases.
-/
def TestSuite.run (suite : TestSuite m) : m Nat := do
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
def TestSuite.runAll (suites : List (TestSuite m)) : m UInt32 := do
  let outcomes ← suites.mapM TestSuite.run
  let total := suites.foldl (fun n ts => n + ts.tests.length) 0
  let failures := outcomes.foldl (· + ·) 0
  let successes := total - failures
  IO.println "====== TOTAL ======="
  IO.println s!"{successes} success(es) {failures} failure(s) {total} test(s) run"
  pure (UInt32.ofNat failures)

end UnitTest
