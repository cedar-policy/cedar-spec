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

import Lean.Data.Json.FromToJson

import Cedar.Spec
import Cedar.Validation
import Cedar.SymCC
import Cedar.SymCCOpt
import CedarProto
import Cedar.TPE
import Protobuf

import CedarFFI.ToJson

/-! This file defines the public interfaces for the Lean implementation.
    The input and output are stringified JSON objects. -/

namespace CedarFFI

open Cedar.Spec
open Cedar.SymCC
open Cedar.TPE
open Cedar.Validation
open Cedar

abbrev FfiM α := ExceptT String IO α

structure Timed (α : Type) where
  data : α
  /-- Duration in nanoseconds -/
  duration : Nat
deriving Lean.ToJson

def runAndTime (f : Unit → α) : BaseIO (Timed α) := do
  let start ← IO.monoNanosNow
  let result := f ()
  let stop ← IO.monoNanosNow
  return {
    data := result,
    duration := stop - start
  }

def runAndTimeIO (f : IO α) : IO (Timed α) := do
  let start ← IO.monoNanosNow
  let result ← f
  let stop ← IO.monoNanosNow
  return {
    data := result,
    duration := stop - start
  }

unsafe def runFfiM {α : Type} [Lean.ToJson α] (m : FfiM α) : String :=
  match unsafeIO m with
  | .error s => toString (Lean.toJson ((.error s!"IO error: {s}") : Except String α))
  | .ok (.error s) => toString (Lean.toJson ((.error s) : Except String α))
  | .ok (.ok r) => toString (Lean.toJson (.ok r : Except String α))

@[export loadProtobufSchema] unsafe def loadProtobufSchema (req: ByteArray) : Except String Schema :=
  ((@Proto.Message.interpret? Proto.Schema) req |>.mapError (s!"failed to parse input: {·}")) >>= (·.toSchema)

--------------------------------- Cedar Evaluation / Validation ---------------------------------

/--
  `req`: binary protobuf for an `AuthorizationRequest`

  returns a string containing JSON
-/
@[export isAuthorized] unsafe def isAuthorizedFFI (req: ByteArray) : String :=
  runFfiM do
    let p ← (@Proto.Message.interpret? AuthorizationRequest) req |>.mapError (s!"failed to parse input: {·}")
    runAndTime (λ () => isAuthorized p.request p.entities p.policies)

/--
  `req`: binary protobuf for a `ValidationRequest`

  returns a string containing JSON
-/
@[export validate] unsafe def validateReqFFI (req : ByteArray) : String :=
  runFfiM do
    let v ← (@Proto.Message.interpret? Proto.ValidationRequest) req |>.mapError (s!"failed to parse input: {·}")
    runAndTime (λ () => validate v.policies v.schema)

/--
  `req`: binary protobuf for a `LevelValidationRequest`

  returns a string containing JSON
-/
@[export levelValidate] unsafe def levelValidateFFI (req : ByteArray) : String :=
  runFfiM do
    let v ← (@Proto.Message.interpret? Proto.LevelValidationRequest) req |>.mapError (s!"failed to parse input: {·}")
    runAndTime (λ () => validateWithLevel v.policies v.schema v.level.level)

/--
  `req`: binary protobuf for an `EvaluationRequest`

  Parses req, evalutes expression, and prints it.
  returns a string encoding either .error err_msg if an error occurs or .ok () upon success
-/
@[export printEvaluation] unsafe def printEvaluationFFI (req: ByteArray) : String :=
  runFfiM do
    let v ← (@Proto.Message.interpret? EvaluationRequest) req |>.mapError (s!"failed to parse input: {·}")
    runAndTimeIO do
      match evaluate v.expr v.request v.entities with
      | .error e =>
        println! s!"evaluate: error during evaluation: {reprStr e}"
      | .ok v =>
        println! "{reprStr v}"

/--
  `req`: binary protobuf for an `EvaluationRequest`

  returns a string containing JSON, indicating whether the Lean evaluation
  result matches the `expected` in the request (where `expected = none`
  indicates the evaluation is expected to produce an error)
-/
@[export checkEvaluate] unsafe def checkEvaluateFFI (req : ByteArray) : String :=
  runFfiM do
    let v ← (@Proto.Message.interpret? EvaluationRequest) req |>.mapError (s!"failed to parse input: {·}")
    runAndTime (λ () =>
      match (evaluate v.expr v.request v.entities), v.expected with
      | .error _, .none => true
      | .ok v₁, .some v₂ => (v₁ == v₂)
      | _, _ => false
    )

/--
  `req`: binary protobuf for an `EntityValidationRequest`

  returns a string containing JSON
-/
@[export validateEntities] unsafe def validateEntitiesFFI (req : ByteArray) : String :=
  runFfiM do
    let v ← (@Proto.Message.interpret? Proto.EntityValidationRequest) req |>.mapError (s!"failed to parse input: {·}")
    let actionEntities := (v.schema.acts.mapOnValues actionSchemaEntryToEntityData)
    let entities := Data.Map.make (v.entities.kvs ++ actionEntities.kvs)
    runAndTime (λ () => validateEntities v.schema entities)

/--
  `req`: binary protobuf for a `RequestValidationRequest`

  returns a string containing JSON
-/
@[export validateRequest] unsafe def validateRequestFFI (req : ByteArray) : String :=
  runFfiM do
    let v ← (@Proto.Message.interpret? Proto.RequestValidationRequest) req |>.mapError (s!"failed to parse input: {·}")
    runAndTime (λ () => validateRequest v.schema v.request)

------------------------------------ Cedar Symbolic Compiler ------------------------------------

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  Upon success returns the original (pre-typecheck) policy and the compiled policy
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) The requestEnv of `req` is not consistent with the schema of `req`
  3.) The policy of `req` is not well-typed for the requestEnv of `req`
-/
def parseCheckPolicyReq (schema : Schema) (req : ByteArray) : Except String (Policy × CompiledPolicy) := do
  let req ← (@Proto.Message.interpret? Proto.CheckPolicyRequest) req |>.mapError (s!"failed to parse input: {·}")
  let policy := req.policy
  let request := req.request
  let env ← match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env => .ok env
  let _ ← env.validateWellFormed |>.mapError (s!"failed to validate environment (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {·}")
  let cp ← CompiledPolicy.compile policy env |>.mapError (s!"failed to compile policy for requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {·}")
  return (policy, cp)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  Upon success returns the original (pre-typecheck) policies and the compiled policyset
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) The requestEnv of `req` is not consistent with the schema of `req`
  3.) Any policy of the policySet of `req` is not well-typed for the requestEnv of `req`
-/
def parseCheckPoliciesReq (schema : Schema) (req : ByteArray) : Except String (Policies × CompiledPolicySet) := do
  let req ← (@Proto.Message.interpret? Proto.CheckPolicySetRequest) req |>.mapError (s!"failed to parse input: {·}")
  let policySet := req.policySet
  let request := req.request
  let env ← match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env => .ok env
  let cpset ← CompiledPolicySet.compile policySet env |>.mapError (s!"failed to validate policy for requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {·}")
  return (policySet, cpset)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  Upon success returns both original (pre-typechecked) policysets and both compiled policysets
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) The requestEnv of `req` is not consistent with the schema of `req`
  3.) Any policy of the source or target PolicySets of `req` is not well-typed for the requestEnv of `req`
-/
def parseComparePolicySetsReq (schema : Schema) (req : ByteArray) : Except String (Policies × Policies × CompiledPolicySet × CompiledPolicySet) := do
  let req ← (@Proto.Message.interpret? Proto.ComparePolicySetsRequest) req |>.mapError (s!"failed to parse input: {·}")
  let srcPolicySet := req.srcPolicySet
  let tgtPolicySet := req.tgtPolicySet
  let request := req.request
  let env ← match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env => .ok env
  let cpSrcPolicySet ← CompiledPolicySet.compile srcPolicySet env |>.mapError (s!"failed to validate src policies for requestEnv (PrincipalType : {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {·}")
  let cpTgtPolicySet ← CompiledPolicySet.compile tgtPolicySet env |>.mapError (s!"failed to validate tgt policies for requestEnv (PrincipalType : {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {·}")
  return (srcPolicySet, tgtPolicySet, cpSrcPolicySet, cpTgtPolicySet)

/--
  `req`: binary protobuf for a `ComparePoliciesRequest`

  Upon success returns both original (pre-typechecked) policies and both compiled policies
-/
def parseComparePoliciesReq (schema : Schema) (req : ByteArray) : Except String (Spec.Policy × Spec.Policy × CompiledPolicy × CompiledPolicy) := do
  let req ← (@Proto.Message.interpret? Proto.ComparePoliciesRequest) req |>.mapError (s!"failed to parse input: {·}")
  let p₁ := req.policy1
  let p₂ := req.policy2
  let request := req.request
  let env ← match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env => .ok env
  let cp₁ ← CompiledPolicy.compile p₁ env |>.mapError (s!"failed to validate first policy for requestEnv (PrincipalType : {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {·}")
  let cp₂ ← CompiledPolicy.compile p₂ env |>.mapError (s!"failed to validate first policy for requestEnv (PrincipalType : {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {·}")
  return (p₁, p₂, cp₁, cp₂)

/--
  `req`: binary protobuf for a `CheckAssertsRequest`

  Upon success returns the `Asserts` and the `SymEnv` that were received
-/
def parseCheckAssertsReq (schema : Schema) (proto : ByteArray) : Except String (Asserts × SymEnv) := do
  let req ← (@Proto.Message.interpret? Proto.CheckAssertsRequest) proto |>.mapError (s!"failed to parse input: {·}")
  let asserts := req.asserts
  let request := req.request
  let env ← match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env => .ok env
  return (asserts, SymEnv.ofTypeEnv env)

/--
  Run `solver` on `vcs` without exposing the IO monad to the calling code
-/
private def safeSolve {α} (solver : IO Solver) (vcs : SolverM α) : IO (Except String α) := do vcs |>.run (←solver)

@[implemented_by safeSolve]
opaque solve {α} (solver : IO Solver) (vcs : SolverM α) : IO (Except String α)

private def safeTimedSolve {α} (solver: IO Solver) (vcs : SolverM α) : IO (Except String (Timed α)) := do
  let result ← runAndTimeIO (solve solver vcs)
  return match result.data with
  | .ok res => .ok ( { data := res, duration := result.duration })
  | .error s => .error s

@[implemented_by safeTimedSolve]
opaque timedSolve {α} (solver : IO Solver) (vcs : SolverM α) : IO (Except String (Timed α))

/--
  Helper function that encodes and runs the solver on the generated VCs. Useful for
  running the File or Buffer based solvers to print or stringify the SMTLib representation
  of the VCs.
-/
private def ignoreOutput (asserts : Asserts) (εnv : SymEnv) : SolverM Unit := do
  if asserts.any (· == false) || asserts.all (· == true) then
    --Solver.reset
    pure ()
  else
    let _ ← Encoder.encode asserts εnv (produceModels := true)
    match (← Solver.checkSat) with
    | .unsat   => pure ()
    | .sat     => pure ()
    | .unknown => pure ()

private def smtLibOf (asserts : Asserts) (εnv : SymEnv) : FfiM (Timed String) := do
  let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
  let solver ← Solver.bufferWriter buffer
  let r ← timedSolve (pure solver) (ignoreOutput asserts εnv)
  let inner_buffer ← buffer.swap ⟨ByteArray.empty, 0⟩
  let data := (String.fromUTF8? inner_buffer.data).getD ""
  return ({ data := data, duration := r.duration } : Timed String)

private def printAsserts (asserts : Asserts) (εnv : SymEnv) : FfiM (Timed Unit) :=
  do
    let stdOut ← IO.getStdout
    let solver ← Solver.streamWriter stdOut
    timedSolve (pure solver) (ignoreOutput asserts εnv)

/-- Collection of FFI functions we want to implement for each SymCC primitive -/
structure SymCCPrimitive where
  /--
  `req`: binary protobuf for the appropriate request shape (depends on
  primitive: `CheckPolicyRequest`, `ComparePoliciesRequest`, etc)

  returns `true` if the solver could prove `req` holds; `false` if the solver could prove `req` does not hold

  Note that the time in the `Timed` includes the encoder and solver but _not_ policy compilation to Term
  -/
  run : Schema → (req : ByteArray) → FfiM (Timed Bool)

  /--
  `req`: binary protobuf for the appropriate request shape (depends on
  primitive: `CheckPolicyRequest`, `ComparePoliciesRequest`, etc)

  returns `none` if the solver could prove `req` holds; `some` if the solver could prove `req` does not hold

  Note that the time in the `Timed` includes the encoder and solver but _not_ policy compilation to Term
  -/
  runWithCex : Schema → (req : ByteArray) → FfiM (Timed (Option Env))

  /--
  `req`: binary protobuf for the appropriate request shape (depends on
  primitive: `CheckPolicyRequest`, `ComparePoliciesRequest`, etc)

  returns the `Asserts` computed for the request (but does not encode them to SMTLib or invoke a solver)

  Note that the time in the `Timed` does _not_ include policy compilation to
  Term, so, the work actually being timed is pretty trivial
  -/
  asserts : Schema → (req : ByteArray) → FfiM (Timed (SymCC.Result Asserts))

  /--
  `req`: binary protobuf for the appropriate request shape (depends on
  primitive: `CheckPolicyRequest`, `ComparePoliciesRequest`, etc)

  returns the SMTLib script computed for the request (but does not invoke a solver)

  Note that the time in the `Timed` includes the encoder but _not_ policy compilation to Term
  -/
  smtLib : Schema → (req : ByteArray) → FfiM (Timed String)

  /--
  `req`: binary protobuf for the appropriate request shape (depends on
  primitive: `CheckPolicyRequest`, `ComparePoliciesRequest`, etc)

  prints the SMTLib-format script to stdout (but does not invoke a solver)

  Note that the time in the `Timed` includes the encoder and printing but _not_ policy compilation to Term
  -/
  printToStdout : Schema → (req : ByteArray) → FfiM (Timed Unit)

/-- a `SymCCPrimitive` which takes a single policy -/
def SymCCPrimitive.singlePolicy
  (solveFn        : CompiledPolicy → SolverM Bool)
  (solveWithCexFn : CompiledPolicy → SolverM (Option Env))
  (verifyFn       : CompiledPolicy → Asserts)
: SymCCPrimitive := {
  run := λ (schema : Schema) (req : ByteArray) => do
    let (_, cp) ← parseCheckPolicyReq schema req
    timedSolve Solver.cvc5 (solveFn cp)
  runWithCex := λ (schema : Schema) (req : ByteArray) => do
    let (_, cp) ← parseCheckPolicyReq schema req
    timedSolve Solver.cvc5 (solveWithCexFn cp)
  asserts := λ (schema : Schema) (req : ByteArray) => do
    let (_, cp) ← parseCheckPolicyReq schema req
    -- for backwards compatibility, we provide a λ that returns Result, even though `verifyFn` returns Asserts directly
    runAndTime (λ () => .ok $ verifyFn cp)
  smtLib := λ (schema : Schema) (req : ByteArray) => do
    let (_, cp) ← parseCheckPolicyReq schema req
    smtLibOf (verifyFn cp) cp.εnv
  printToStdout := λ (schema : Schema) (req : ByteArray) => do
    let (_, cp) ← parseCheckPolicyReq schema req
    printAsserts (verifyFn cp) cp.εnv
}

/-- a `SymCCPrimitive` which takes two policies -/
def SymCCPrimitive.twoPolicy
  (solveFn        : CompiledPolicy → CompiledPolicy → SolverM Bool)
  (solveWithCexFn : CompiledPolicy → CompiledPolicy → SolverM (Option Env))
  (verifyFn       : CompiledPolicy → CompiledPolicy → Asserts)
: SymCCPrimitive := {
  run := λ (schema : Schema) (req : ByteArray) => do
    let (_, _, cp₁, cp₂) ← parseComparePoliciesReq schema req
    timedSolve Solver.cvc5 (solveFn cp₁ cp₂)
  runWithCex := λ (schema : Schema) (req : ByteArray) => do
    let (_, _, cp₁, cp₂) ← parseComparePoliciesReq schema req
    timedSolve Solver.cvc5 (solveWithCexFn cp₁ cp₂)
  asserts := λ (schema : Schema) (req : ByteArray) => do
    let (_, _, cp₁, cp₂) ← parseComparePoliciesReq schema req
    -- for backwards compatibility, we provide a λ that returns Result, even though `verifyFn` returns Asserts directly
    runAndTime (λ () => .ok $ verifyFn cp₁ cp₂)
  smtLib := λ (schema : Schema) (req : ByteArray) => do
    let (_, _, cp₁, cp₂) ← parseComparePoliciesReq schema req
    smtLibOf (verifyFn cp₁ cp₂) cp₁.εnv -- cp₁ and cp₂ will have the same εnv
  printToStdout := λ (schema : Schema) (req : ByteArray) => do
    let (_, _, cp₁, cp₂) ← parseComparePoliciesReq schema req
    printAsserts (verifyFn cp₁ cp₂) cp₁.εnv -- cp₁ and cp₂ will have the same εnv
}

/-- a `SymCCPrimitive` which takes a single policyset -/
def SymCCPrimitive.singlePolicySet
  (solveFn        : CompiledPolicySet → SolverM Bool)
  (solveWithCexFn : CompiledPolicySet → SolverM (Option Env))
  (verifyFn       : CompiledPolicySet → Asserts)
: SymCCPrimitive := {
  run := λ (schema : Schema) (req : ByteArray) => do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    timedSolve Solver.cvc5 (solveFn cpset)
  runWithCex := λ (schema : Schema) (req : ByteArray) => do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    timedSolve Solver.cvc5 (solveWithCexFn cpset)
  asserts := λ (schema : Schema) (req : ByteArray) => do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    -- for backwards compatibility, we provide a λ that returns Result, even though `verifyFn` returns Asserts directly
    runAndTime (λ () => .ok $ verifyFn cpset)
  smtLib := λ (schema : Schema) (req : ByteArray) => do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    smtLibOf (verifyFn cpset) cpset.εnv
  printToStdout := λ (schema : Schema) (req : ByteArray) => do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    printAsserts (verifyFn cpset) cpset.εnv
}

/-- a `SymCCPrimitive` which takes two policysets -/
def SymCCPrimitive.twoPolicySet
  (solveFn        : CompiledPolicySet → CompiledPolicySet → SolverM Bool)
  (solveWithCexFn : CompiledPolicySet → CompiledPolicySet → SolverM (Option Env))
  (verifyFn       : CompiledPolicySet → CompiledPolicySet → Asserts)
: SymCCPrimitive := {
  run := λ (schema : Schema) (req : ByteArray) => do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    timedSolve Solver.cvc5 (solveFn cpset₁ cpset₂)
  runWithCex := λ (schema : Schema) (req : ByteArray) => do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    timedSolve Solver.cvc5 (solveWithCexFn cpset₁ cpset₂)
  asserts := λ (schema : Schema) (req : ByteArray) => do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    -- for backwards compatibility, we provide a λ that returns Result, even though `verifyFn` returns Asserts directly
    runAndTime (λ () => .ok $ verifyFn cpset₁ cpset₂)
  smtLib := λ (schema : Schema) (req : ByteArray) => do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    smtLibOf (verifyFn cpset₁ cpset₂) cpset₁.εnv -- cpset₁ and cpset₂ will have the same εnv
  printToStdout := λ (schema : Schema) (req : ByteArray) => do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    printAsserts (verifyFn cpset₁ cpset₂) cpset₁.εnv -- cpset₁ and cpset₂ will have the same εnv
}

def SymCCPrimitive.neverErrors       := SymCCPrimitive.singlePolicy    checkNeverErrorsOpt       neverErrorsOpt?        verifyNeverErrorsOpt
def SymCCPrimitive.alwaysMatches     := SymCCPrimitive.singlePolicy    checkAlwaysMatchesOpt     alwaysMatchesOpt?      verifyAlwaysMatchesOpt
def SymCCPrimitive.neverMatches      := SymCCPrimitive.singlePolicy    checkNeverMatchesOpt      neverMatchesOpt?       verifyNeverMatchesOpt
def SymCCPrimitive.matchesEquivalent := SymCCPrimitive.twoPolicy       checkMatchesEquivalentOpt matchesEquivalentOpt?  verifyMatchesEquivalentOpt
def SymCCPrimitive.matchesImplies    := SymCCPrimitive.twoPolicy       checkMatchesImpliesOpt    matchesImpliesOpt?     verifyMatchesImpliesOpt
def SymCCPrimitive.matchesDisjoint   := SymCCPrimitive.twoPolicy       checkMatchesDisjointOpt   matchesDisjointOpt?    verifyMatchesDisjointOpt
def SymCCPrimitive.alwaysAllows      := SymCCPrimitive.singlePolicySet checkAlwaysAllowsOpt      alwaysAllowsOpt?       verifyAlwaysAllowsOpt
def SymCCPrimitive.alwaysDenies      := SymCCPrimitive.singlePolicySet checkAlwaysDeniesOpt      alwaysDeniesOpt?       verifyAlwaysDeniesOpt
def SymCCPrimitive.equivalent        := SymCCPrimitive.twoPolicySet    checkEquivalentOpt        equivalentOpt?         verifyEquivalentOpt
def SymCCPrimitive.implies           := SymCCPrimitive.twoPolicySet    checkImpliesOpt           impliesOpt?            verifyImpliesOpt
def SymCCPrimitive.disjoint          := SymCCPrimitive.twoPolicySet    checkDisjointOpt          disjointOpt?           verifyDisjointOpt        

/-- the `SymCCPrimitive` for `CheckAsserts` -/
def SymCCPrimitive.assertsPrim : SymCCPrimitive := {
  run := λ (schema : Schema) (req : ByteArray) => do
    let (asserts, εnv) ← parseCheckAssertsReq schema req
    timedSolve Solver.cvc5 (checkUnsat (λ _ => .ok asserts) εnv)
  runWithCex := λ _ _ => .error s!"Counterexample generation not supported for CheckAsserts"
  asserts := λ (schema : Schema) (req : ByteArray) => do
    let (asserts, _) ← parseCheckAssertsReq schema req
    runAndTime (λ () => .ok asserts)
  smtLib := λ (schema : Schema) (req : ByteArray) => do
    let (asserts, εnv) ← parseCheckAssertsReq schema req
    smtLibOf asserts εnv
  printToStdout := λ (schema : Schema) (req : ByteArray) => do
    let (asserts, εnv) ← parseCheckAssertsReq schema req
    printAsserts asserts εnv
}

/-
-------
Each of the following `run*` functions returns a JSON encoded string that encodes
  1.) .error err_message if there was an error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold

Note that the time includes the encoder and solver but _not_ policy compilation to Term
-------
-/

@[export runCheckAsserts] unsafe def runCheckAsserts (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.assertsPrim.run schema req

@[export runCheckNeverErrors] unsafe def runCheckNeverErrors (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.neverErrors.run schema req

@[export runCheckAlwaysMatches] unsafe def runCheckAlwaysMatches (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysMatches.run schema req

@[export runCheckNeverMatches] unsafe def runCheckNeverMatches (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.neverMatches.run schema req

@[export runCheckMatchesEquivalent] unsafe def runCheckMatchesEquivalent (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesEquivalent.run schema req

@[export runCheckMatchesImplies] unsafe def runCheckMatchesImplies (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesImplies.run schema req

@[export runCheckMatchesDisjoint] unsafe def runCheckMatchesDisjoint (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesDisjoint.run schema req

@[export runCheckAlwaysAllows] unsafe def runCheckAlwaysAllows (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysAllows.run schema req

@[export runCheckAlwaysDenies] unsafe def runCheckAlwaysDenies (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysDenies.run schema req

@[export runCheckEquivalent] unsafe def runCheckEquivalent (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.equivalent.run schema req

@[export runCheckImplies] unsafe def runCheckImplies (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.implies.run schema req

@[export runCheckDisjoint] unsafe def runCheckDisjoint (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.disjoint.run schema req

/-
-------
Each of the following `run*WithCex` functions returns a JSON encoded string that encodes
  1.) .error err_message if there was an error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold

Note that the time includes the encoder and solver but _not_ policy compilation to Term
-------
-/

@[export runCheckNeverErrorsWithCex] unsafe def runCheckNeverErrorsWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.neverErrors.runWithCex schema req

@[export runCheckAlwaysMatchesWithCex] unsafe def runCheckAlwaysMatchesWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysMatches.runWithCex schema req

@[export runCheckNeverMatchesWithCex] unsafe def runCheckNeverMatchesWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.neverMatches.runWithCex schema req

@[export runCheckMatchesEquivalentWithCex] unsafe def runCheckMatchesEquivalentWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesEquivalent.runWithCex schema req

@[export runCheckMatchesImpliesWithCex] unsafe def runCheckMatchesImpliesWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesImplies.runWithCex schema req

@[export runCheckMatchesDisjointWithCex] unsafe def runCheckMatchesDisjointWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesDisjoint.runWithCex schema req

@[export runCheckAlwaysAllowsWithCex] unsafe def runCheckAlwaysAllowsWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysAllows.runWithCex schema req

@[export runCheckAlwaysDeniesWithCex] unsafe def runCheckAlwaysDeniesWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysDenies.runWithCex schema req

@[export runCheckEquivalentWithCex] unsafe def runCheckEquivalentWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.equivalent.runWithCex schema req

@[export runCheckImpliesWithCex] unsafe def runCheckImpliesWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.implies.runWithCex schema req

@[export runCheckDisjointWithCex] unsafe def runCheckDisjointWithCex (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.disjoint.runWithCex schema req

/-
-------
Each of the following `print*` functions returns a JSON encoded string that encodes
  1.) .error err_message if there was an error in parsing or encoding the vcs
  2.) .ok { data := (), duration := <encode+print_time> } if the vcs were successfully printed to stdout in SMTLib format

Note that the time includes the encoder and printing but _not_ policy compilation to Term
-------
-/

@[export printCheckAsserts] unsafe def printCheckAsserts (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.assertsPrim.printToStdout schema req

@[export printCheckNeverErrors] unsafe def printCheckNeverErrors (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.neverErrors.printToStdout schema req

@[export printCheckAlwaysMatches] unsafe def printCheckAlwaysMatches (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysMatches.printToStdout schema req

@[export printCheckNeverMatches] unsafe def printCheckNeverMatches (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.neverMatches.printToStdout schema req

@[export printCheckAlwaysAllows] unsafe def printCheckAlwaysAllows (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysAllows.printToStdout schema req

@[export printCheckAlwaysDenies] unsafe def printCheckAlwaysDenies (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysDenies.printToStdout schema req

@[export printCheckEquivalent] unsafe def printCheckEquivalent (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.equivalent.printToStdout schema req

@[export printCheckImplies] unsafe def printCheckImplies (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.implies.printToStdout schema req

@[export printCheckDisjoint] unsafe def printCheckDisjoint (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.disjoint.printToStdout schema req

@[export printCheckMatchesEquivalent] unsafe def printCheckMatchesEquivalent (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesEquivalent.printToStdout schema req

@[export printCheckMatchesImplies] unsafe def printCheckMatchesImplies (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesImplies.printToStdout schema req

@[export printCheckMatchesDisjoint] unsafe def printCheckMatchesDisjoint (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesDisjoint.printToStdout schema req

/-
-------
Each of the following `assertsOf*` functions returns a JSON encoded string that encodes
  1.) .error err_message if there was an error in parsing or generating the vcs
  2.) .ok { data := <encoding>, duration := ... } where <encoding> is the JSON encoding of the VCs (Asserts/Terms) computed for the request

Note that the time does _not_ include policy compilation to Term, so, the work actually being timed is pretty trivial
-------
-/

@[export assertsOfCheckNeverErrors] unsafe def assertsOfCheckNeverErrors (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.neverErrors.asserts schema req

@[export assertsOfCheckAlwaysMatches] unsafe def assertsOfCheckAlwaysMatches (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysMatches.asserts schema req

@[export assertsOfCheckNeverMatches] unsafe def assertsOfCheckNeverMatches (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.neverMatches.asserts schema req

@[export assertsOfCheckAlwaysAllows] unsafe def assertsOfCheckAlwaysAllows (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysAllows.asserts schema req

@[export assertsOfCheckAlwaysDenies] unsafe def assertsOfCheckAlwaysDenies (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysDenies.asserts schema req

@[export assertsOfCheckEquivalent] unsafe def assertsOfCheckEquivalent (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.equivalent.asserts schema req

@[export assertsOfCheckImplies] unsafe def assertsOfCheckImplies (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.implies.asserts schema req

@[export assertsOfCheckDisjoint] unsafe def assertsOfCheckDisjoint (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.disjoint.asserts schema req

@[export assertsOfCheckMatchesEquivalent] unsafe def assertsOfCheckMatchesEquivalent (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesEquivalent.asserts schema req

@[export assertsOfCheckMatchesImplies] unsafe def assertsOfCheckMatchesImplies (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesImplies.asserts schema req

@[export assertsOfCheckMatchesDisjoint] unsafe def assertsOfCheckMatchesDisjoint (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesDisjoint.asserts schema req

/-
-------
Each of the following `smtLibOf*` functions returns a JSON encoded string that encodes
  1.) .error err_message if there was an error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query

Note that the time is only the encoder and _not_ policy compilation to Term
-------
-/

@[export smtLibOfCheckAsserts] unsafe def smtLibOfCheckAsserts (schema : Schema) (req: ByteArray) : String :=
  runFfiM $ SymCCPrimitive.assertsPrim.smtLib schema req

@[export smtLibOfCheckNeverErrors] unsafe def smtLibOfCheckNeverErrors (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.neverErrors.smtLib schema req

@[export smtLibOfCheckAlwaysMatches] unsafe def smtLibOfCheckAlwaysMatches (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysMatches.smtLib schema req

@[export smtLibOfCheckNeverMatches] unsafe def smtLibOfCheckNeverMatches (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.neverMatches.smtLib schema req

@[export smtLibOfCheckAlwaysAllows] unsafe def smtLibOfCheckAlwaysAllows (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysAllows.smtLib schema req

@[export smtLibOfCheckAlwaysDenies] unsafe def smtLibOfCheckAlwaysDenies (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.alwaysDenies.smtLib schema req

@[export smtLibOfCheckEquivalent] unsafe def smtLibOfCheckEquivalent (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.equivalent.smtLib schema req

@[export smtLibOfCheckImplies] unsafe def smtLibOfCheckImplies (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.implies.smtLib schema req

@[export smtLibOfCheckDisjoint] unsafe def smtLibOfCheckDisjoint (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.disjoint.smtLib schema req

@[export smtLibOfCheckMatchesEquivalent] unsafe def smtLibOfCheckMatchesEquivalent (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesEquivalent.smtLib schema req

@[export smtLibOfCheckMatchesImplies] unsafe def smtLibOfCheckMatchesImplies (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesImplies.smtLib schema req

@[export smtLibOfCheckMatchesDisjoint] unsafe def smtLibOfCheckMatchesDisjoint (schema : Schema) (req : ByteArray) : String :=
  runFfiM $ SymCCPrimitive.matchesDisjoint.smtLib schema req

/--
  `req`: binary protobuf for an `BatchedEvaluationRequest`
  Upon success returns inputs to `batchedEvaluate`
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) Cannot derive a request environment from the request
  3.) Request cannot be validated
  4.) Policy cannot be validated
  5.) Policy set contains more than one policy (a limitation at this moment)
-/
def parseBatchedEvaluationReq (req : ByteArray) : Except String (TypedExpr × Request × Entities × Nat) := do
  let req ← (@Proto.Message.interpret? Proto.BatchedEvaluationRequest) req |>.mapError (s!"failed to parse input: {·}")
  let policySet := req.policies
  let policy ← match policySet with
    | [policy] => .ok policy
    | _ => .error s!"only one policy is expected"
  let schema := req.schema
  let request := req.request
  let entities := req.entities
  let iteration := req.iteration.toNat
  let expr ← match schema.environment? request.principal.ty request.resource.ty request.action with
    | .some env =>
      if requestIsValid env request.asPartialRequest then do
        let expr := substituteAction env.reqty.action policy.toExpr
        let (te, _) ← (typeOf expr ∅ env).mapError (fun err => s!"invalid policy: {reprStr err}")
        .ok te
      else
        .error s!"invalid request"
    | .none => .error s!"invalid environment derived from request"
  return (expr, request, entities, iteration)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded of `Option Bool`
  1.) .error err_message if there was an error in parsing `req`
  2.) .ok {data, ..} where data is of type `Option Bool`. It is true when the
      result residual is `.val true`; and it is false when the result residual
      is either `.val false` or `.error _`. So we can interpret the boolean
      value as if the policy takes effect or not
-/
@[export batchedEvaluateFFI] unsafe def batchedEvaluateFFI (req : ByteArray) : String :=
  runFfiM do
    let (expr, request, entities, iteration) ← parseBatchedEvaluationReq req
    runAndTime (λ () => match batchedEvaluate expr request (entityLoaderFor entities) iteration with
    | .val v _ => match v.asBool with
      | .ok b => (.some b : Option Bool)
      | .error _ => .none
    | .error _ => (.some false)
    | _ => .none
    )

--------------------------------- FFI Test Utils ---------------------------------
/- Some definitions used to test lean object decoding in Rust -/

@[export ffiTestString] def ffiTestString : String := "ffiTestString"
@[export ffiTestExceptOk] def ffiTestExceptOk : Except String String := .ok "ok"
@[export ffiTestExceptErr] def ffiTestExceptErr : Except String String := .error "error"

end CedarFFI
