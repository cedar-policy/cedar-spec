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
import CedarProto
import Protobuf

import CedarFFI.ToJson

/-! This file defines the public interfaces for the Lean implementation.
    The input and output are stringified JSON objects. -/

namespace CedarFFI

open Cedar.Spec
open Cedar.SymCC
open Cedar.Validation
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
  .ok {
    data := result,
    duration := stop - start
  }

def runAndTimeIO (f : IO α) : IO (Timed α) := do
  let start ← IO.monoNanosNow
  let result ← f
  let stop ← IO.monoNanosNow
  .ok {
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
  `return_original`: return the deserialized policy when enabled, as opposed to the one generated by the validator

  Upon success returns a well-typed policy and symbolic environment corresponding to the request `req`
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) The requestEnv of `req` is not consistent with the schema of `req`
  3.) The policy of `req` is not well-typed for the requestEnv of `req`
-/
def parseCheckPolicyReq (schema : Cedar.Validation.Schema) (req : ByteArray) (return_original: Bool) : Except String (Cedar.Spec.Policy × SymEnv) := do
  let req ← (@Message.interpret? CheckPolicyRequest) req |>.mapError (s!"failed to parse input: {·}")
  let policy := req.policy
  let request := req.request
  let env ← match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env => .ok env
  let _ ← env.validateWellFormed |>.mapError (s!"failed to validate environment (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {·}")
  let well_typed_policy ← match wellTypedPolicy policy env with
    | none => .error s!"failed to validate policy for requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some policy => .ok policy
  return (if return_original then policy else well_typed_policy, SymEnv.ofTypeEnv env)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`
  `return_original`: return the deserialized policy set when enabled, as opposed to the one generated by the validator

  Upon success returns a list of well-typed policies and symbolic environment corresponding to the request `req`
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) The requestEnv of `req` is not consistent with the schema of `req`
  3.) Any policy of the policySet of `req` is not well-typed for the requestEnv of `req`
-/
def parseCheckPoliciesReq (schema : Cedar.Validation.Schema) (req : ByteArray) (return_original: Bool) : Except String (Policies × SymEnv) := do
  let req ← (@Message.interpret? CheckPolicySetRequest) req |>.mapError (s!"failed to parse input: {·}")
  let policySet := req.policySet
  let request := req.request
  let env ← match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env => .ok env
  let well_typed_policies ← match wellTypedPolicies policySet env with
    | none => .error s!"failed to validate policy for requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some policies => .ok policies
  return (if return_original then policySet else well_typed_policies, SymEnv.ofTypeEnv env)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`
  `return_original`: return the deserialized policy sets when enabled, as opposed to the ones generated by the validator

  Upon success returns a list of well-typed policies and symbolic environment corresponding to the request `req`
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) The requestEnv of `req` is not consistent with the schema of `req`
  3.) Any policy of the source or target PolicySets of `req` is not well-typed for the requestEnv of `req`
-/
def parseComparePolicySetsReq (schema : Cedar.Validation.Schema) (req : ByteArray) (return_original: Bool) : Except String (Policies × Policies × SymEnv) := do
  let req ← (@Message.interpret? ComparePolicySetsRequest) req |>.mapError (s!"failed to parse input: {·}")
  let srcPolicySet := req.srcPolicySet
  let tgtPolicySet := req.tgtPolicySet
  let request := req.request
  let env ← match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env => .ok env
  let (well_typed_src_policies, well_typed_tgt_policies) ← match wellTypedPolicies srcPolicySet env, wellTypedPolicies tgtPolicySet env with
    | none, _ | _, none => .error s!"failed to validate policy for requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some src, some tgt => .ok (src, tgt)
  return if return_original then (srcPolicySet, tgtPolicySet, SymEnv.ofTypeEnv env) else (well_typed_src_policies, well_typed_tgt_policies, SymEnv.ofTypeEnv env)


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
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckNeverErrors] unsafe def runCheckNeverErrors (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policy, εnv) ← parseCheckPolicyReq schema req false
    timedSolve Solver.cvc5 (checkNeverErrors policy εnv)

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckNeverErrorsWithCex] unsafe def runCheckNeverErrorsWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policy, εnv) ← parseCheckPolicyReq schema req false
    timedSolve Solver.cvc5 (neverErrors? policy εnv)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckAlwaysAllows] unsafe def runCheckAlwaysAllows (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req false
    timedSolve Solver.cvc5 (checkAlwaysAllows policies εnv)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckAlwaysAllowsWithCex] unsafe def runCheckAlwaysAllowsWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req false
    timedSolve Solver.cvc5 (alwaysAllows? policies εnv)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckAlwaysDenies] unsafe def runCheckAlwaysDenies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req false
    timedSolve Solver.cvc5 (checkAlwaysDenies policies εnv)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckAlwaysDeniesWithCex] unsafe def runCheckAlwaysDeniesWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req false
    timedSolve Solver.cvc5 (alwaysDenies? policies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckEquivalent] unsafe def runCheckEquivalent (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    timedSolve Solver.cvc5 (checkEquivalent srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckEquivalentWithCex] unsafe def runCheckEquivalentWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    timedSolve Solver.cvc5 (equivalent? srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckImplies] unsafe def runCheckImplies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    timedSolve Solver.cvc5 (checkImplies srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckImpliesWithCex] unsafe def runCheckImpliesWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    timedSolve Solver.cvc5 (implies? srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := false, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckDisjoint] unsafe def runCheckDisjoint (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    timedSolve Solver.cvc5 (checkDisjoint srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := null, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := {request: ..., entities: ...}, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckDisjointWithCex] unsafe def runCheckDisjointWithCex (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    timedSolve Solver.cvc5 (disjoint? srcPolicies tgtPolicies εnv)

/--
  Auxillary function that encodes and runs the solver on the generated VCs. Useful for
  running the File or Buffer based solvers to print or stringify the SMTLib representation
  of the VCs.
-/
private def ignoreOutput (vc : SymEnv → Cedar.SymCC.Result Cedar.SymCC.Asserts) (εnv : SymEnv) : SolverM Unit := do
  match vc εnv with
  | .ok asserts =>
    if asserts.any (· == false) || asserts.all (· == true) then
      --Solver.reset
      pure ()
    else
      let _ ← Encoder.encode asserts εnv (produceModels := true)
      match (← Solver.checkSat) with
      | .unsat   => pure ()
      | .sat     => pure ()
      | .unknown => pure ()
  | .error err =>
    throw (IO.userError s!"SymCC failed: {reprStr err}.")

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckNeverErrors] unsafe def printCheckNeverErrors (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policy, εnv) ← parseCheckPolicyReq schema req false
    let stdOut ← IO.getStdout
    let solver ← Solver.streamWriter stdOut
    let vcs := ignoreOutput (verifyNeverErrors policy) εnv
    timedSolve (pure solver) vcs

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckAlwaysAllows] unsafe def printCheckAlwaysAllows (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req false
    let stdOut ← IO.getStdout
    let solver ← Solver.streamWriter stdOut
    let vcs := ignoreOutput (verifyAlwaysAllows policies) εnv
    timedSolve (pure solver) vcs

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckAlwaysDenies] unsafe def printCheckAlwaysDenies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req false
    let stdOut ← IO.getStdout
    let solver ← Solver.streamWriter stdOut
    let vcs := ignoreOutput (verifyAlwaysDenies policies) εnv
    timedSolve (pure solver) vcs

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckEquivalent] unsafe def printCheckEquivalent (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    let stdOut ← IO.getStdout
    let solver ← Solver.streamWriter stdOut
    let vcs := ignoreOutput (verifyEquivalent srcPolicies tgtPolicies) εnv
    timedSolve (pure solver) vcs

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckImplies] unsafe def printCheckImplies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    let stdOut ← IO.getStdout
    let solver ← Solver.streamWriter stdOut
    let vcs := ignoreOutput (verifyImplies srcPolicies tgtPolicies) εnv
    timedSolve (pure solver) vcs

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckDisjoint] unsafe def printCheckDisjoint (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    let stdOut ← IO.getStdout
    let solver ← Solver.streamWriter stdOut
    let vcs := ignoreOutput (verifyDisjoint srcPolicies tgtPolicies) εnv
    timedSolve (pure solver) vcs

/--
  `req`: binary protobuf for a `CheckAsserts`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <solve_time> } if the solver could prove `asserts` hold
  3.) .ok { data := false, duration := <solve_time> } if the solver could prove `asserts` do not hold
-/
@[export runCheckAsserts] unsafe def runCheckAsserts (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (asserts, εnv) ← parseCheckAssertsReq schema req
    timedSolve Solver.cvc5 (checkUnsat (λ _ => .ok asserts) εnv)

/--
  `req`: binary protobuf for a `CheckAsserts`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckAsserts] unsafe def printCheckAsserts (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (asserts, εnv) ← parseCheckAssertsReq schema req
    let stdOut ← IO.getStdout
    let solver ← Solver.streamWriter stdOut
    timedSolve (pure solver) (ignoreOutput (λ _ => .ok asserts) εnv)

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
    let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
    let solver ← Solver.bufferWriter buffer
    let r ← timedSolve (pure solver) (ignoreOutput (fun _ => .ok asserts) εnv)
    let inner ← buffer.swap ⟨ByteArray.empty, 0⟩
    let data  := (String.fromUTF8? inner.data).getD ""
    return ({ data := data, duration := r.duration } : Timed String)

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded of the term generated by `verifyNeverErrors`
-/
@[export assertsOfCheckNeverErrors] unsafe def assertsOfCheckNeverErrors (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (policy, εnv) ← parseCheckPolicyReq schema req false
    runAndTime (λ () => verifyNeverErrors policy εnv)

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded of the term generated by `verifyNeverErrors` on the deserialized policy
-/
@[export assertsOfCheckNeverErrorsOnOriginal] unsafe def assertsOfCheckNeverErrorsOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (policy, εnv) ← parseCheckPolicyReq schema req true
    runAndTime (λ () => verifyNeverErrors policy εnv)

/--
  `req`: binary protobuf for an `CheckPoliciesRequest`

  returns JSON encoded of the term generated by `verifyAlwaysAllows`
-/
@[export assertsOfCheckAlwaysAllows] unsafe def assertsOfCheckAlwaysAllows (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req false
    runAndTime (λ () => verifyAlwaysAllows policies εnv)

/--
  `req`: binary protobuf for an `CheckPoliciesRequest`

  returns JSON encoded of the term generated by `verifyAlwaysAllows` on the deserialized policy set
-/
@[export assertsOfCheckAlwaysAllowsOnOriginal] unsafe def assertsOfCheckAlwaysAllowsOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req true
    runAndTime (λ () => verifyAlwaysAllows policies εnv)

/--
  `req`: binary protobuf for an `CheckPoliciesRequest`

  returns JSON encoded of the term generated by `verifyAlwaysDenies`
-/
@[export assertsOfCheckAlwaysDenies] unsafe def assertsOfCheckAlwaysDenies (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req false
    runAndTime (λ () => verifyAlwaysDenies policies εnv)

/--
  `req`: binary protobuf for an `CheckPoliciesRequest`

  returns JSON encoded of the term generated by `verifyAlwaysDenies` on deserialized policy set
-/
@[export assertsOfCheckAlwaysDeniesOnOriginal] unsafe def assertsOfCheckAlwaysDeniesOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req true
    runAndTime (λ () => verifyAlwaysDenies policies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyEquivalent`
-/
@[export assertsOfCheckEquivalent] unsafe def assertsOfCheckEquivalent (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    runAndTime (λ () => verifyEquivalent srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyEquivalent` on deserialized policy sets
-/
@[export assertsOfCheckEquivalentOnOriginal] unsafe def assertsOfCheckEquivalentOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req true
    runAndTime (λ () => verifyEquivalent srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyImplies`
-/
@[export assertsOfCheckImplies] unsafe def assertsOfCheckImplies (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    runAndTime (λ () => verifyImplies srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyImplies` on deserialized policy sets
-/
@[export assertsOfCheckImpliesOnOriginal] unsafe def assertsOfCheckImpliesOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req true
    runAndTime (λ () => verifyImplies srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyDisjoint`
-/
@[export assertsOfCheckDisjoint] unsafe def assertsOfCheckDisjoint (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    runAndTime (λ () => verifyDisjoint srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyDisjoint` on deserialized policy sets
-/
@[export assertsOfCheckDisjointOnOriginal] unsafe def assertsOfCheckDisjointOnOriginal (schema : Cedar.Validation.Schema) (req: ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req true
    runAndTime (λ () => verifyDisjoint srcPolicies tgtPolicies εnv)

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckNeverErrors] unsafe def smtLibOfCheckNeverErrors (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policy, εnv) ← parseCheckPolicyReq schema req false
    let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
    let solver ← Solver.bufferWriter buffer
    let vcs := ignoreOutput (verifyNeverErrors policy) εnv
    let r ← timedSolve (pure solver) vcs
    let inner_buffer ← buffer.swap ⟨ByteArray.empty, 0⟩
    let data := (String.fromUTF8? inner_buffer.data).getD ""
    return ({ data := data, duration := r.duration } : Timed String)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckAlwaysAllows] unsafe def smtLibOfCheckAlwaysAllows (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req false
    let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
    let solver ← Solver.bufferWriter buffer
    let vcs := ignoreOutput (verifyAlwaysAllows policies) εnv
    let r ← timedSolve (pure solver) vcs
    let inner_buffer ← buffer.swap ⟨ByteArray.empty, 0⟩
    let data := (String.fromUTF8? inner_buffer.data).getD ""
    return ({ data := data, duration := r.duration } : Timed String)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckAlwaysDenies] unsafe def smtLibOfCheckAlwaysDenies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (policies, εnv) ← parseCheckPoliciesReq schema req false
    let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
    let solver ← Solver.bufferWriter buffer
    let vcs := ignoreOutput (verifyAlwaysDenies policies) εnv
    let r ← timedSolve (pure solver) vcs
    let inner_buffer ← buffer.swap ⟨ByteArray.empty, 0⟩
    let data := (String.fromUTF8? inner_buffer.data).getD ""
    return ({ data := data, duration := r.duration } : Timed String)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckEquivalent] unsafe def smtLibOfCheckEquivalent (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
    let solver ← Solver.bufferWriter buffer
    let vcs := ignoreOutput (verifyEquivalent srcPolicies tgtPolicies) εnv
    let r ← timedSolve (pure solver) vcs
    let inner_buffer ← buffer.swap ⟨ByteArray.empty, 0⟩
    let data := (String.fromUTF8? inner_buffer.data).getD ""
    return ({ data := data, duration := r.duration } : Timed String)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckImplies] unsafe def smtLibOfCheckImplies (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
    let solver ← Solver.bufferWriter buffer
    let vcs := ignoreOutput (verifyImplies srcPolicies tgtPolicies) εnv
    let r ← timedSolve (pure solver) vcs
    let inner_buffer ← buffer.swap ⟨ByteArray.empty, 0⟩
    let data := (String.fromUTF8? inner_buffer.data).getD ""
    return ({ data := data, duration := r.duration } : Timed String)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckDisjoint] unsafe def smtLibOfCheckDisjoint (schema : Cedar.Validation.Schema) (req : ByteArray) : String :=
  runFfiM do
    let (srcPolicies, tgtPolicies, εnv) ← parseComparePolicySetsReq schema req false
    let buffer ← IO.mkRef ⟨ByteArray.empty, 0⟩
    let solver ← Solver.bufferWriter buffer
    let vcs := ignoreOutput (verifyDisjoint srcPolicies tgtPolicies) εnv
    let r ← timedSolve (pure solver) vcs
    let inner_buffer ← buffer.swap ⟨ByteArray.empty, 0⟩
    let data := (String.fromUTF8? inner_buffer.data).getD ""
    return ({ data := data, duration := r.duration } : Timed String)

--------------------------------- FFI Test Utils ---------------------------------
/- Some definitions used to test lean object decoding in Rust -/

@[export ffiTestString] def ffiTestString : String := "ffiTestString"
@[export ffiTestExceptOk] def ffiTestExceptOk : Except String String := .ok "ok"
@[export ffiTestExceptErr] def ffiTestExceptErr : Except String String := .error "error"

end CedarFFI
