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

import SymTest.Arith
import SymTest.Datetime
import SymTest.Decimal
import SymTest.Has
import SymTest.In
import SymTest.IPAddr
import SymTest.Like
import SymTest.Tags
import SymTest.Solver
import SymTest.WellTyped
import SymTest.Decoder
import SymTest.Verifier

open UnitTest Cedar.SymCC SymTest

private def UnitTest.TestCase.liftToSolverM (t : TestCase IO) : TestCase SolverM :=
  ⟨t.map liftM, t.name⟩

private def UnitTest.TestSuite.liftToSolverM (t : TestSuite IO) : TestSuite SolverM :=
  ⟨t.name, t.tests.map TestCase.liftToSolverM⟩

private def tests :=
  Arith.tests ++
  Has.tests ++
  Like.tests ++
  In.tests ++
  Decimal.tests ++
  IPAddr.tests ++
  Datetime.tests ++
  Tags.tests ++
  (Solver.tests.map TestSuite.liftToSolverM) ++
  WellTyped.tests ++
  (Decoder.tests.map TestSuite.liftToSolverM) ++
  Verifier.tests

/--
To run these tests, your environment must set the CVC5
variable to point to a cvc5 binary, version 1.1.1 or later.
The variable should give the absolute path to the binary.
-/
def main : IO UInt32 := do
  TestSuite.runAll tests |>.run (← Solver.cvc5)
