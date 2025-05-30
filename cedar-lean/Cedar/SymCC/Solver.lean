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

import Lean.Data.Json

/-!
This file defines a simple interface to an SMT solver running in a separate
process. Callers communicate with the solver by issuing commands with
s-expressions encoded as strings. The interface is based on
[lean-smt](https://github.com/ufmg-smite/lean-smt/).

Currently, we support only CVC5. The function `cvc5` creates a fresh CVC5 solver
process. This function assumes that the environment variable `CVC5` contains the
absolute path to the CVC5 executable.
-/

namespace Cedar.SymCC

inductive Decision where
  | sat
  | unsat
  | unknown
deriving DecidableEq, Repr

instance : Lean.ToJson Decision where
  toJson d := match d with
    | .sat => "sat"
    | .unsat => "unsat"
    | .unknown => "unknown"

/--
 A Solver is an interpreter for SMTLib scripts, which are passed to the solver
 via its `smtLibInput` stream. Solvers optionally have an `smtLibOutput` stream
 to which they print the results of executing the commands received on the input
 stream. We assume that both the input and output streams conform to the SMTLib
 standard: the inputs are SMTLib script commands encoded as s-expressions, and
 the outputs are the s-expressions whose shape is determined by the standard for
 each command. We don't have an error stream here, since we configure solvers to
 run in quiet mode and not print anything to the error stream.
-/
structure Solver where
  smtLibInput : IO.FS.Stream
  smtLibOutput : Option IO.FS.Stream

abbrev SolverM (α) := ReaderT Solver IO α

def SolverM.run (solver : Solver) (x : SolverM α) : IO α := ReaderT.run x solver

namespace Solver

/--
  Returns a Solver for the given path and arguments. This function expects
  `path` to point to an SMT solver executable, and `args` to specify valid
  arguments to that solver.
-/
def spawn (path : String) (args : Array String) : IO Solver := do
  let proc ← IO.Process.spawn {
    stdin  := .piped
    stdout := .piped
    stderr := .piped
    cmd    := path
    args   := args
  }
  return ⟨IO.FS.Stream.ofHandle proc.stdin, IO.FS.Stream.ofHandle proc.stdout⟩

/--
  Returns an instance of the CVC5 solver that is backed by the executable
  specified in the environment variable "CVC5".
-/
def cvc5 : IO Solver := do
  match (← IO.getEnv "CVC5") with
  | .some path => spawn path ["--quiet", "--lang", "smt"].toArray
  | .none      => throw (IO.userError "CVC5 environment variable not defined.")

/--
  Returns a solver that writes all issued commands to the given stream `s`.
  Commands that produce output, such as `checkSat`, write the command to `s` and
  return values that are sound according to the SMTLIb spec (but generally not
  useful). For example, `Solver.checkSat` returns `Decision.unknown`. This
  function expects `s` to be write-enabled.
-/
def streamWriter (s : IO.FS.Stream) : IO Solver :=
  return ⟨s, .none⟩

/--
  Returns a solver that writes all issued commands to the given file handle `h`.
  Commands that produce output, such as `checkSat`, write the command to `h` and
  return values that are sound according to the SMTLIb spec (but generally not
  useful). For example, `Solver.checkSat` returns `Decision.unknown`. This
  function expects `h` to be write-enabled.
-/
def fileWriter (h : IO.FS.Handle) : IO Solver :=
  return ⟨IO.FS.Stream.ofHandle h, .none⟩

/--
  Returns a solver that writes all issued commands to the given buffer `b`.
  Commands that produce output, such as `checkSat`, write the command to `b` and
  return values that are sound according to the SMTLIb spec (but generally not
  useful). For example, `Solver.checkSat` returns `Decision.unknown`.
-/
def bufferWriter (b : IO.Ref IO.FS.Stream.Buffer) : IO Solver :=
  return ⟨IO.FS.Stream.ofBuffer b, .none⟩

private def emitln (str : String) : SolverM Unit := do
  -- dbg_trace "{str}" -- uncomment to see input sent to the solver
  let solver ← read
  solver.smtLibInput.putStr s!"{str}\n"
  solver.smtLibInput.flush

def setLogic (logic : String) : SolverM Unit :=
  emitln s!"(set-logic {logic})"

def setOption (opt val : String) : SolverM Unit :=
  emitln s!"(set-option {opt} {val})"

def setOptionProduceModels (b : Bool) : SolverM Unit :=
  setOption ":produce-models" (if b then "true" else "false")

def comment (comment : String) : SolverM Unit :=
  let inline := comment.replace "\n" " "
  emitln s!"; {inline}"

def assert (expr : String) : SolverM Unit :=
  emitln s!"(assert {expr})"

def defineFun (id : String) (args : List (String × String)) (type expr : String) : SolverM Unit :=
  let inline := String.intercalate " " (args.map (λ ⟨pᵢ, pₜ⟩ => s!"({pᵢ} {pₜ})"))
  emitln s!"(define-fun {id} ({inline}) {type} {expr})"

def declareConst (id type : String) : SolverM Unit :=
  emitln s!"(declare-const {id} {type})"

def declareFun (id : String) (args : List String) (type : String) : SolverM Unit :=
  let inline := String.intercalate " " args
  emitln s!"(declare-fun {id} ({inline}) {type})"

def declareDatatype (id : String) (params : List String) (constructors : List String) : SolverM Unit :=
  let cInline := "\n  " ++ String.intercalate "\n  " constructors
  let pInline := String.intercalate " " params
  if params.isEmpty
  then emitln s!"(declare-datatype {id} ({cInline}))"
  else emitln s!"(declare-datatype {id} (par ({pInline}) ({cInline})))"

private def readlnD (dflt : String) : SolverM String := do
  match (← read).smtLibOutput with
  | .some stdout => stdout.getLine
  | .none        => pure dflt

def checkSat : SolverM Decision := do
  emitln "(check-sat)"
  match (← readlnD "unknown\n") with
  | "sat\n"     => return Decision.sat
  | "unsat\n"   => return Decision.unsat
  | "unknown\n" => return Decision.unknown
  | other       => throw (IO.userError s!"Unrecognized solver output: {other}")

def reset : SolverM Unit :=
  emitln "(reset)"

def exit : SolverM Unit :=
  emitln "(exit)"

/--
Returns the model from the SMT solver, assuming that `checkSat` produced
a `.sat` decision.  Note that this model extraction procedure assumes that
the model strings follow the CVC5 format, where the model is enclosed in
parentheses that are on a single line by themselves, i.e., opens with the line
`(\n` and closes with the line `)\n`.
-/
def getModel : SolverM String := do
  emitln "(get-model)"
  match (← read).smtLibOutput with
  | some out =>
    match (← out.getLine) with
    | "(\n" =>
      let mut s := ""
      repeat
        match (← out.getLine) with
        | ")\n" => break
        | line  => s := s ++ line
      return "(\n" ++ s ++ ")\n"
    | other => throw (IO.userError s!"Unrecognized solver output: {other}")
  | none    => throw (IO.userError s!"Cannot get model unless after a SAT response.")

end Solver

end Cedar.SymCC
