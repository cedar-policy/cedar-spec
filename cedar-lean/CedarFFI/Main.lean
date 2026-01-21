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
open Cedar.Proto
open Proto

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

@[export loadProtobufSchema] unsafe def loadProtobufSchema (req: ByteArray) : Except String Cedar.Validation.Schema :=
  ((@Message.interpret? Proto.Schema) req |>.mapError (s!"failed to parse input: {·}")) >>= (·.toSchema)

--------------------------------- Cedar Evaluation / Validation ---------------------------------

/--
  `req`: binary protobuf for an `AuthorizationRequest`

  returns a string containing JSON
-/
@[export isAuthorized] unsafe def isAuthorizedFFI (req: ByteArray) : String :=
  runFfiM do
    let p ← (@Message.interpret? AuthorizationRequest) req |>.mapError (s!"failed to parse input: {·}")
    runAndTime (λ () => isAuthorized p.request p.entities p.policies)

/--
  `req`: binary protobuf for a `ValidationRequest`

  returns a string containing JSON
-/
@[export validate] unsafe def validateReqFFI (req : ByteArray) : String :=
  runFfiM do
    let v ← (@Message.interpret? ValidationRequest) req |>.mapError (s!"failed to parse input: {·}")
    runAndTime (λ () => validate v.policies v.schema)

/--
  `req`: binary protobuf for a `LevelValidationRequest`

  returns a string containing JSON
-/
@[export levelValidate] unsafe def levelValidateFFI (req : ByteArray) : String :=
  runFfiM do
    let v ← (@Message.interpret? LevelValidationRequest) req |>.mapError (s!"failed to parse input: {·}")
    runAndTime (λ () => validateWithLevel v.policies v.schema v.level.level)

/--
  `req`: binary protobuf for an `EvaluationRequest`

  Parses req, evalutes expression, and prints it.
  returns a string encoding either .error err_msg if an error occurs or .ok () upon success
-/
@[export printEvaluation] unsafe def printEvaluationFFI (req: ByteArray) : String :=
  runFfiM do
    let v ← (@Message.interpret? EvaluationRequest) req |>.mapError (s!"failed to parse input: {·}")
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
    let v ← (@Message.interpret? EvaluationRequest) req |>.mapError (s!"failed to parse input: {·}")
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
    let v ← (@Message.interpret? EntityValidationRequest) req |>.mapError (s!"failed to parse input: {·}")
    let actionEntities := (v.schema.acts.mapOnValues actionSchemaEntryToEntityData)
    let entities := Cedar.Data.Map.make (v.entities.kvs ++ actionEntities.kvs)
    runAndTime (λ () => validateEntities v.schema entities)

/--
  `req`: binary protobuf for a `RequestValidationRequest`

  returns a string containing JSON
-/
@[export validateRequest] unsafe def validateRequestFFI (req : ByteArray) : String :=
  runFfiM do
    let v ← (@Message.interpret? RequestValidationRequest) req |>.mapError (s!"failed to parse input: {·}")
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
def parseCheckPolicyReq (schema : Cedar.Validation.Schema) (req : ByteArray) : Except String (Cedar.Spec.Policy × CompiledPolicy) := do
  let req ← (@Message.interpret? CheckPolicyRequest) req |>.mapError (s!"failed to parse input: {·}")
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
def parseCheckPoliciesReq (schema : Cedar.Validation.Schema) (req : ByteArray) : Except String (Policies × CompiledPolicySet) := do
  let req ← (@Message.interpret? CheckPolicySetRequest) req |>.mapError (s!"failed to parse input: {·}")
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
def parseComparePolicySetsReq (schema : Cedar.Validation.Schema) (req : ByteArray) : Except String (Policies × Policies × CompiledPolicySet × CompiledPolicySet) := do
  let req ← (@Message.interpret? ComparePolicySetsRequest) req |>.mapError (s!"failed to parse input: {·}")
  let srcPolicySet := req.srcPolicySet
  let tgtPolicySet := req.tgtPolicySet
  let request := req.request
  let env ← match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env => .ok env
  let cpSrcPolicySet ← CompiledPolicySet.compile srcPolicySet env |>.mapError (s!"failed to validate src policies for requestEnv (PrincipalType : {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {·}")
  let cpTgtPolicySet ← CompiledPolicySet.compile tgtPolicySet env |>.mapError (s!"failed to validate tgt policies for requestEnv (PrincipalType : {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {·}")
  return (srcPolicySet, tgtPolicySet, cpSrcPolicySet, cpTgtPolicySet)

def parseCheckAssertsReq (schema : Cedar.Validation.Schema) (proto : ByteArray) : Except String (Cedar.SymCC.Asserts × SymEnv) := do
  let req ← (@Message.interpret? CheckAssertsRequest) proto |>.mapError (s!"failed to parse input: {·}")
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
  `req`: binary protobuf for a `CheckAsserts`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `asserts` hold
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `asserts` do not hold
-/
@[export runCheckAsserts] unsafe def runCheckAsserts (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (asserts, εnv) ← parseCheckAssertsReq schema req
    timedSolve Solver.cvc5 (checkUnsat (λ _ => .ok asserts) εnv)

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckNeverErrors] unsafe def runCheckNeverErrors (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cp) ← parseCheckPolicyReq schema req
    timedSolve Solver.cvc5 (checkNeverErrorsOpt cp)

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckNeverErrorsWithCex] unsafe def runCheckNeverErrorsWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cp) ← parseCheckPolicyReq schema req
    timedSolve Solver.cvc5 (neverErrorsOpt? cp)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckAlwaysAllows] unsafe def runCheckAlwaysAllows (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    timedSolve Solver.cvc5 (checkAlwaysAllowsOpt cpset)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckAlwaysAllowsWithCex] unsafe def runCheckAlwaysAllowsWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    timedSolve Solver.cvc5 (alwaysAllowsOpt? cpset)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckAlwaysDenies] unsafe def runCheckAlwaysDenies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    timedSolve Solver.cvc5 (checkAlwaysDeniesOpt cpset)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckAlwaysDeniesWithCex] unsafe def runCheckAlwaysDeniesWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    timedSolve Solver.cvc5 (alwaysDeniesOpt? cpset)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckEquivalent] unsafe def runCheckEquivalent (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    timedSolve Solver.cvc5 (checkEquivalentOpt cpset₁ cpset₂)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckEquivalentWithCex] unsafe def runCheckEquivalentWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    timedSolve Solver.cvc5 (equivalentOpt? cpset₁ cpset₂)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckImplies] unsafe def runCheckImplies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    timedSolve Solver.cvc5 (checkImpliesOpt cpset₁ cpset₂)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckImpliesWithCex] unsafe def runCheckImpliesWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    timedSolve Solver.cvc5 (impliesOpt? cpset₁ cpset₂)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckDisjoint] unsafe def runCheckDisjoint (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    timedSolve Solver.cvc5 (checkDisjointOpt cpset₁ cpset₂)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold

  Note that the time includes the encoder and solver but _not_ policy compilation to Term
-/
@[export runCheckDisjointWithCex] unsafe def runCheckDisjointWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    timedSolve Solver.cvc5 (disjointOpt? cpset₁ cpset₂)

/--
  Auxillary function that encodes and runs the solver on the generated VCs. Useful for
  running the File or Buffer based solvers to print or stringify the SMTLib representation
  of the VCs.
-/
private def ignoreOutput (asserts : Cedar.SymCC.Asserts) (εnv : SymEnv) : SolverM Unit := do
  if asserts.any (· == false) || asserts.all (· == true) then
    --Solver.reset
    pure ()
  else
    let _ ← Encoder.encode asserts εnv (produceModels := true)
    match (← Solver.checkSat) with
    | .unsat   => pure ()
    | .sat     => pure ()
    | .unknown => pure ()

private def printAsserts (asserts : Cedar.SymCC.Asserts) (εnv : SymEnv) : FfiM (Timed Unit) :=
  do
    let stdOut ← IO.getStdout
    let solver ← Solver.streamWriter stdOut
    timedSolve (pure solver) (ignoreOutput asserts εnv)

/--
  `req`: binary protobuf for a `CheckAsserts`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckAsserts] unsafe def printCheckAsserts (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (asserts, εnv) ← parseCheckAssertsReq schema req
    printAsserts asserts εnv

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format

  Note that the time includes the encoder and printing but _not_ policy compilation to Term
-/
@[export printCheckNeverErrors] unsafe def printCheckNeverErrors (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cp) ← parseCheckPolicyReq schema req
    printAsserts (verifyNeverErrorsOpt cp) cp.εnv

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format

  Note that the time includes the encoder and printing but _not_ policy compilation to Term
-/
@[export printCheckAlwaysAllows] unsafe def printCheckAlwaysAllows (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    printAsserts (verifyAlwaysAllowsOpt cpset) cpset.εnv

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format

  Note that the time includes the encoder and printing but _not_ policy compilation to Term
-/
@[export printCheckAlwaysDenies] unsafe def printCheckAlwaysDenies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    printAsserts (verifyAlwaysDeniesOpt cpset) cpset.εnv

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format

  Note that the time includes the encoder and printing but _not_ policy compilation to Term
-/
@[export printCheckEquivalent] unsafe def printCheckEquivalent (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    printAsserts (verifyEquivalentOpt cpset₁ cpset₂) cpset₁.εnv -- cpset₁ and cpset₂ will have the same εnv

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format

  Note that the time includes the encoder and printing but _not_ policy compilation to Term
-/
@[export printCheckImplies] unsafe def printCheckImplies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    printAsserts (verifyImpliesOpt cpset₁ cpset₂) cpset₁.εnv -- cpset₁ and cpset₂ will have the same εnv

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format

  Note that the time includes the encoder and printing but _not_ policy compilation to Term
-/
@[export printCheckDisjoint] unsafe def printCheckDisjoint (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    printAsserts (verifyDisjointOpt cpset₁ cpset₂) cpset₁.εnv -- cpset₁ and cpset₂ will have the same εnv

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded of the term generated by `verifyNeverErrors`
-/
@[export assertsOfCheckNeverErrors] unsafe def assertsOfCheckNeverErrors (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (_, cp) ← parseCheckPolicyReq schema req
    -- for backwards compatibility, we provide a λ that returns Result, even though verify*Opt functions return Asserts directly
    runAndTime (λ () => (.ok $ verifyNeverErrorsOpt cp : Cedar.SymCC.Result Cedar.SymCC.Asserts))

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded of the term generated by `verifyNeverErrors` on the deserialized policy

  this DOES NOT use the optimized interface (which requires you to compile the
  typechecked policy, not the original deserialized policy), so it is
  inefficient. Callers should migrate to `assertsOfCheckNeverErrors` if/when possible
-/
@[export assertsOfCheckNeverErrorsOnOriginal] unsafe def assertsOfCheckNeverErrorsOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (policy, cp) ← parseCheckPolicyReq schema req
    runAndTime (λ () => verifyNeverErrors policy cp.εnv)

/--
  `req`: binary protobuf for an `CheckPoliciesRequest`

  returns JSON encoded of the term generated by `verifyAlwaysAllows`
-/
@[export assertsOfCheckAlwaysAllows] unsafe def assertsOfCheckAlwaysAllows (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    -- for backwards compatibility, we provide a λ that returns Result, even though verify*Opt functions return Asserts directly
    runAndTime (λ () => (.ok $ verifyAlwaysAllowsOpt cpset : Cedar.SymCC.Result Cedar.SymCC.Asserts))

/--
  `req`: binary protobuf for an `CheckPoliciesRequest`

  returns JSON encoded of the term generated by `verifyAlwaysAllows` on the deserialized policy set

  this DOES NOT use the optimized interface (which requires you to compile the
  typechecked pset, not the original deserialized pset), so it is
  inefficient. Callers should migrate to `assertsOfCheckAlwaysAllows` if/when possible
-/
@[export assertsOfCheckAlwaysAllowsOnOriginal] unsafe def assertsOfCheckAlwaysAllowsOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (pset, cpset) ← parseCheckPoliciesReq schema req
    runAndTime (λ () => verifyAlwaysAllows pset cpset.εnv)

/--
  `req`: binary protobuf for an `CheckPoliciesRequest`

  returns JSON encoded of the term generated by `verifyAlwaysDenies`
-/
@[export assertsOfCheckAlwaysDenies] unsafe def assertsOfCheckAlwaysDenies (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    -- for backwards compatibility, we provide a λ that returns Result, even though verify*Opt functions return Asserts directly
    runAndTime (λ () => (.ok $ verifyAlwaysDeniesOpt cpset : Cedar.SymCC.Result Cedar.SymCC.Asserts))

/--
  `req`: binary protobuf for an `CheckPoliciesRequest`

  returns JSON encoded of the term generated by `verifyAlwaysDenies` on deserialized policy set

  this DOES NOT use the optimized interface (which requires you to compile the
  typechecked pset, not the original deserialized pset), so it is
  inefficient. Callers should migrate to `assertsOfCheckAlwaysDenies` if/when possible
-/
@[export assertsOfCheckAlwaysDeniesOnOriginal] unsafe def assertsOfCheckAlwaysDeniesOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (pset, cpset) ← parseCheckPoliciesReq schema req
    runAndTime (λ () => verifyAlwaysDenies pset cpset.εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyEquivalent`
-/
@[export assertsOfCheckEquivalent] unsafe def assertsOfCheckEquivalent (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    -- for backwards compatibility, we provide a λ that returns Result, even though verify*Opt functions return Asserts directly
    runAndTime (λ () => (.ok $ verifyEquivalentOpt cpset₁ cpset₂ : Cedar.SymCC.Result Cedar.SymCC.Asserts))

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyEquivalent` on deserialized policy sets

  this DOES NOT use the optimized interface (which requires you to compile the
  typechecked psets, not the original deserialized psets), so it is
  inefficient. Callers should migrate to `assertsOfCheckEquivalent` if/when possible
-/
@[export assertsOfCheckEquivalentOnOriginal] unsafe def assertsOfCheckEquivalentOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (pset₁, pset₂, cpset₁, _) ← parseComparePolicySetsReq schema req
    runAndTime (λ () => verifyEquivalent pset₁ pset₂ cpset₁.εnv) -- cpset₁ and cpset₂ will have the same εnv

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyImplies`
-/
@[export assertsOfCheckImplies] unsafe def assertsOfCheckImplies (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    -- for backwards compatibility, we provide a λ that returns Result, even though verify*Opt functions return Asserts directly
    runAndTime (λ () => (.ok $ verifyImpliesOpt cpset₁ cpset₂ : Cedar.SymCC.Result Cedar.SymCC.Asserts))

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyImplies` on deserialized policy sets

  this DOES NOT use the optimized interface (which requires you to compile the
  typechecked psets, not the original deserialized psets), so it is
  inefficient. Callers should migrate to `assertsOfCheckImplies` if/when possible
-/
@[export assertsOfCheckImpliesOnOriginal] unsafe def assertsOfCheckImpliesOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (pset₁, pset₂, cpset₁, _) ← parseComparePolicySetsReq schema req
    runAndTime (λ () => verifyImplies pset₁ pset₂ cpset₁.εnv) -- cpset₁ and cpset₂ will have the same εnv

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyDisjoint`
-/
@[export assertsOfCheckDisjoint] unsafe def assertsOfCheckDisjoint (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    -- for backwards compatibility, we provide a λ that returns Result, even though verify*Opt functions return Asserts directly
    runAndTime (λ () => (.ok $ verifyDisjointOpt cpset₁ cpset₂ : Cedar.SymCC.Result Cedar.SymCC.Asserts))

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyDisjoint` on deserialized policy sets

  this DOES NOT use the optimized interface (which requires you to compile the
  typechecked psets, not the original deserialized psets), so it is
  inefficient. Callers should migrate to `assertsOfCheckDisjoint` if/when possible
-/
@[export assertsOfCheckDisjointOnOriginal] unsafe def assertsOfCheckDisjointOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (pset₁, pset₂, cpset₁, _) ← parseComparePolicySetsReq schema req
    runAndTime (λ () => verifyDisjoint pset₁ pset₂ cpset₁.εnv) -- cpset₁ and cpset₂ will have the same εnv

private def smtLibOf (asserts : Cedar.SymCC.Asserts) (εnv : SymEnv) : FfiM (Timed String) :=
  do
    let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
    let solver ← Solver.bufferWriter buffer
    let r ← timedSolve (pure solver) (ignoreOutput asserts εnv)
    let inner_buffer ← buffer.swap ⟨ByteArray.empty, 0⟩
    let data := (String.fromUTF8? inner_buffer.data).getD ""
    return ({ data := data, duration := r.duration } : Timed String)

/--
  `req`: binary protobuf for a `CheckAsserts`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckAsserts] unsafe def smtLibOfCheckAsserts (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (asserts, εnv) ← parseCheckAssertsReq schema req
    smtLibOf asserts εnv

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckNeverErrors] unsafe def smtLibOfCheckNeverErrors (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cp) ← parseCheckPolicyReq schema req
    smtLibOf (verifyNeverErrorsOpt cp) cp.εnv

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckAlwaysAllows] unsafe def smtLibOfCheckAlwaysAllows (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    smtLibOf (verifyAlwaysAllowsOpt cpset) cpset.εnv

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckAlwaysDenies] unsafe def smtLibOfCheckAlwaysDenies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, cpset) ← parseCheckPoliciesReq schema req
    smtLibOf (verifyAlwaysDeniesOpt cpset) cpset.εnv

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckEquivalent] unsafe def smtLibOfCheckEquivalent (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    smtLibOf (verifyEquivalentOpt cpset₁ cpset₂) cpset₁.εnv -- cpset₁ and cpset₂ will have the same εnv

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckImplies] unsafe def smtLibOfCheckImplies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    smtLibOf (verifyImpliesOpt cpset₁ cpset₂) cpset₁.εnv -- cpset₁ and cpset₂ will have the same εnv

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckDisjoint] unsafe def smtLibOfCheckDisjoint (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (_, _, cpset₁, cpset₂) ← parseComparePolicySetsReq schema req
    smtLibOf (verifyDisjointOpt cpset₁ cpset₂) cpset₁.εnv -- cpset₁ and cpset₂ will have the same εnv

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
def parseBatchedEvaluationReq (req : ByteArray) : Except String (Cedar.Validation.TypedExpr × Cedar.Spec.Request × Cedar.Spec.Entities × Nat) := do
  let req ← (@Message.interpret? BatchedEvaluationRequest) req |>.mapError (s!"failed to parse input: {·}")
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
  1.) .error err_message if there was in error in parsing `req`
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
