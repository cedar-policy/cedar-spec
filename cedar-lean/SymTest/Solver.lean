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

import SymTest.Util

/-!
This file contains unit tests that show how to create and use a Solver that
captures issued SMTLib commands to a file or buffer but does not actually perform
any solving.
-/

namespace SymTest.Solver

open Cedar SymCC UnitTest

def checkAssertBoolScript (b : Bool) : String :=
  s!"(reset)\n(set-option :produce-models true)\n(assert {if b then "true" else "false"})\n(check-sat)\n"

def checkAssertBool (b : Bool) : SolverM Decision := do
  Solver.reset
  Solver.setOptionProduceModels true
  Solver.assert (if b then "true" else "false")
  Solver.checkSat

def testAssertBoolToBuffer (b : Bool) : TestCase IO :=
  test "Check Solver.bufferWriter captures commands" ⟨λ _ => do
    let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
    let decision ← checkAssertBool b |>.run (← Solver.bufferWriter buffer)
    let script := (String.fromUTF8? (← ST.Ref.get buffer).data).getD ""
    checkEq (decision, script) (.unknown, (checkAssertBoolScript b))
  ⟩

def testAssertBoolToFile (b : Bool) : TestCase IO :=
  test "Check Solver.fileWriter captures commands" ⟨λ _ => do
    let (h, path) ← IO.FS.createTempFile
    let decision ← checkAssertBool b |>.run (← Solver.fileWriter h)
    h.rewind
    let script ← h.readToEnd
    IO.FS.removeFile path
    checkEq (decision, script) (.unknown, (checkAssertBoolScript b))
  ⟩

def getModelBool (b : Bool) : SolverM String := do
  let _ ← checkAssertBool b
  Solver.getModel

def testGetModelBoolForBuffer (b : Bool) : TestCase IO :=
  test "Check Solver.bufferWriter errors on getModel" ⟨λ _ => do
    let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
    try
      let s ← getModelBool b |>.run (← Solver.bufferWriter buffer)
      checkEq s ""
    catch
      | .userError msg => checkEq msg "Cannot get model unless after a SAT response."
      | err            => checkEq "IO.userError" err.toString
  ⟩

def testGetEmptyModelForCVC5 : TestCase IO :=
  test "Check Solver.cvc5.getModel for a trivially SAT formula with no variables" ⟨λ _ => do
    let s ← getModelBool true |>.run (← Solver.cvc5)
    -- normalize line endings for cross-platform compatibility
    let normalized := s.replace "\r\n" "\n"
    checkEq normalized "(\n)\n"
  ⟩

def testGetModelErrorForCVC5 : TestCase IO :=
  test "Check Solver.cvc5.getModel for a SAT formula" ⟨λ _ => do
    try
      let s ← getModelBool false |>.run (← Solver.cvc5)
      checkEq s ""
    catch
      | .userError msg => checkEq (msg.startsWith "Unrecognized") true
      | err            => checkEq "IO.userError" err.toString
  ⟩

def testCheckSatWithCRLF : TestCase IO :=
  test "Check Solver.checkSat handles Windows CRLF" ⟨λ _ => do
    let (hIn, pathIn) ← IO.FS.createTempFile
    let (hOut, pathOut) ← IO.FS.createTempFile
    hOut.putStr "sat\r\n"
    hOut.rewind
    let testSolver : Solver := {
      smtLibInput  := IO.FS.Stream.ofHandle hIn,
      smtLibOutput := some (IO.FS.Stream.ofHandle hOut)
    }
    let decision ← Solver.checkSat |>.run testSolver
    IO.FS.removeFile pathIn
    IO.FS.removeFile pathOut
    checkEq decision .sat
  ⟩

def testGetModelWithCRLF : TestCase IO :=
  test "Check Solver.getModel handles Windows CRLF" ⟨λ _ => do
    let (hIn, pathIn) ← IO.FS.createTempFile
    let (hOut, pathOut) ← IO.FS.createTempFile
    hOut.putStr "(\r\n  define-fun x () Int 1\r\n)\r\n"
    hOut.rewind
    let testSolver : Solver := {
      smtLibInput  := IO.FS.Stream.ofHandle hIn,
      smtLibOutput := some (IO.FS.Stream.ofHandle hOut)
    }
    let model ← Solver.getModel |>.run testSolver
    IO.FS.removeFile pathIn
    IO.FS.removeFile pathOut
    checkEq model "(\r\n  define-fun x () Int 1\r\n)\r\n"
  ⟩

def testsForCRLF :=
  suite "Solver.CRLF_Compatibility" [
    testCheckSatWithCRLF,
    testGetModelWithCRLF
  ]

def testsForBuffers :=
  suite "Solver.buffers" [
    testAssertBoolToBuffer true,
    testAssertBoolToBuffer false,
    testGetModelBoolForBuffer true,
    testGetModelBoolForBuffer false
  ]

def testsForFiles :=
  suite "Solver.files" [
    testAssertBoolToFile true
  ]

def testsForCVC5 :=
  suite "Solver.cvc5" [
    testGetEmptyModelForCVC5,
    testGetModelErrorForCVC5
  ]

def tests := [
  testsForBuffers,
  testsForFiles,
  testsForCVC5,
  testsForCRLF
]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end SymTest.Solver
