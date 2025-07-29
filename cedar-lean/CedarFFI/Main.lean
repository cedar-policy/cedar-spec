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

--------------------------------- Cedar Evaluation / Validation ---------------------------------

/--
  `req`: binary protobuf for an `AuthorizationRequest`

  returns a string containing JSON
-/
@[export isAuthorized] unsafe def isAuthorizedFFI (req: ByteArray) : String :=
    let result: Except String (Timed Response) :=
      match (@Message.interpret? AuthorizationRequest) req with
      | .error e =>
        .error s!"isAuthorizedDRT: failed to parse input: {e}"
      | .ok p =>
        let result := runAndTime (λ () => isAuthorized p.request p.entities p.policies)
        .ok (unsafeBaseIO result)
    toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `ValidationRequest`

  returns a string containing JSON
-/
@[export validate] unsafe def validateReqFFI (req : ByteArray) : String :=
    let result: Except String (Timed ValidationResult) :=
      match (@Message.interpret? ValidationRequest) req with
      | .error e =>
        .error s!"validateDRT: failed to parse input: {e}"
      | .ok v =>
        let result := runAndTime (λ () => validate v.policies v.schema)
        .ok (unsafeBaseIO result)
    toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `LevelValidationRequest`

  returns a string containing JSON
-/
@[export levelValidate] unsafe def levelValidateFFI (req : ByteArray) : String :=
    let result: Except String (Timed ValidationResult) :=
      match (@Message.interpret? LevelValidationRequest) req with
      | .error e =>
        .error s!"levelValidateDRT: failed to parse input: {e}"
      | .ok v =>
        let result := runAndTime (λ () => validateWithLevel v.policies v.schema v.level.level)
        .ok (unsafeBaseIO result)
    toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `EvaluationRequest`

  Parses req, evalutes expression, and prints it.
  returns a string encoding either .error err_msg if an error occurs or .ok () upon success
-/
@[export printEvaluation] unsafe def printEvaluationFFI (req: ByteArray) : String :=
  let result : Except String (Timed Unit) :=
    match (@Message.interpret? EvaluationRequest) req with
    | .error e => .error s!"evaluate: failed to parse input: {e}"
    | .ok v =>
      let result : BaseIO (Timed (Except String Unit)) := runAndTime (λ () =>
        match evaluate v.expr v.request v.entities with
        | .error e =>
          match unsafeIO (println! s!"evaluate: error during evaluation: {reprStr e}") with
          | .error _ => .error s!"evaluate: error occurred while printing evaluation error"
          | .ok _ => .ok ()
        | .ok v =>
          match unsafeIO (println! "{reprStr v}") with
          | .error _ => .error s!"evaluate: error printing value"
          | .ok _ => .ok ()
      )
      let result := unsafeBaseIO result
      match result.data with
      | .ok _ => .ok { data := (), duration := result.duration }
      | .error s => .error s
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `EvaluationRequest`

  returns a string containing JSON, indicating whether the Lean evaluation
  result matches the `expected` in the request (where `expected = none`
  indicates the evaluation is expected to produce an error)
-/
@[export checkEvaluate] unsafe def checkEvaluateFFI (req : ByteArray) : String :=
  let result : Except String (Timed Bool) := do
    match (@Message.interpret? EvaluationRequest) req with
    | .error e => .error s!"evaluate: failed to parse input: {e}"
    | .ok v =>
      let result := runAndTime (λ () =>
        match (evaluate v.expr v.request v.entities), v.expected with
        | .error _, .none => true
        | .ok v₁, .some v₂ => (v₁ == v₂)
        | _, _ => false
      )
      .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `EntityValidationRequest`

  returns a string containing JSON
-/
@[export validateEntities] unsafe def validateEntitiesFFI (req : ByteArray) : String :=
  let result : Except String (Timed EntityValidationResult) :=
    match (@Message.interpret? EntityValidationRequest) req with
    | .error e => .error s!"validateEntitiesDRT: failed to parse input: {e}"
    | .ok v => do
        let actionEntities := (v.schema.acts.mapOnValues actionSchemaEntryToEntityData)
        let entities := Cedar.Data.Map.make (v.entities.kvs ++ actionEntities.kvs)
        let result := runAndTime (λ () => Cedar.Validation.validateEntities v.schema entities )
        .ok (unsafeBaseIO result)
  toString (Lean.toJson result)


/--
  `req`: binary protobuf for a `RequestValidationRequest`

  returns a string containing JSON
-/
@[export validateRequest] unsafe def validateRequestFFI (req : ByteArray) : String :=
  let result : Except String (Timed RequestValidationResult) :=
    match (@Message.interpret? RequestValidationRequest) req with
    | .error e => .error s!"validateRequestDRT: failed to parse input: {e}"
    | .ok v => do
        let result := runAndTime (λ () => Cedar.Validation.validateRequest v.schema v.request )
        .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

------------------------------------ Cedar Symbolic Compiler ------------------------------------

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  Upon success returns a well-typed policy and symbolic environment corresponding to the request `req`
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) The requestEnv of `req` is not consistent with the schema of `req`
  3.) The policy of `req` is not well-typed for the requestEnv of `req`
-/
def parseCheckPolicyReq (req : ByteArray) : Except String (Cedar.Spec.Policy × SymEnv) :=
  match (@Proto.Message.interpret? CheckPolicyRequest) req with
  | .error e => .error s!"failed to parse input: {e}"
  | .ok req =>
    let policy := req.policy
    let schema := req.schema
    let request := req.request
    match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env => do
      match env.validateWellFormed with
      | .error e => .error s!"failed to validate environment (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource}): {e}"
      | .ok _ => .ok ()
      match wellTypedPolicy policy env with
      | none => .error s!"failed to validate policy for requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
      | some policy => .ok (policy, SymEnv.ofTypeEnv env)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  Upon success returns a list of well-typed policies and symbolic environment corresponding to the request `req`
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) The requestEnv of `req` is not consistent with the schema of `req`
  3.) Any policy of the policySet of `req` is not well-typed for the requestEnv of `req`
-/
def parseCheckPoliciesReq (req : ByteArray) : Except String (Policies × SymEnv) :=
  match (@Proto.Message.interpret? CheckPolicySetRequest) req with
  | .error e => .error s!"failed to parse input: {e}"
  | .ok req =>
    let policySet := req.policySet
    let schema := req.schema
    let request := req.request
    match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env =>
      match wellTypedPolicies policySet env with
      | none => .error s!"failed to validate policy for requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
      | some policies => .ok (policies, SymEnv.ofTypeEnv env)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  Upon success returns a list of well-typed policies and symbolic environment corresponding to the request `req`
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) The requestEnv of `req` is not consistent with the schema of `req`
  3.) Any policy of the source or target PolicySets of `req` is not well-typed for the requestEnv of `req`
-/
def parseComparePolicySetsReq (req : ByteArray) : Except String (Policies × Policies × SymEnv) :=
  match (@Proto.Message.interpret? ComparePolicySetsRequest) req with
  | .error e => .error s!"failed to parse input: {e}"
  | .ok req =>
    let srcPolicySet := req.srcPolicySet
    let tgtPolicySet := req.tgtPolicySet
    let schema := req.schema
    let request := req.request
    match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env =>
      match wellTypedPolicies srcPolicySet env, wellTypedPolicies tgtPolicySet env with
      | none, _
      | _, none => .error s!"failed to validate policy for requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
      | some srcPolicies, some tgtPolicies => .ok (srcPolicies, tgtPolicies, SymEnv.ofTypeEnv env)


def parseCheckAssertsReq (proto : ByteArray) : Except String (Cedar.SymCC.Asserts × SymEnv) :=
  match (@Proto.Message.interpret? CheckAssertsRequest) proto with
  | .error e => .error s!"failed to parse input: {e}"
  | .ok req =>
    let asserts := req.asserts
    let schema := req.schema
    let request := req.request
    match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env =>
      .ok (asserts, SymEnv.ofTypeEnv env)

/--
  Run `solver` on `vcs` without exposing the IO monad to the calling code
-/
private unsafe def unsafeSolve {α} (solver : IO Solver) (vcs : SolverM α) : Except String α := do
    match unsafeIO solver with
    | .error _ => .error "error creating solver"
    | .ok solver =>
      match unsafeIO (vcs |>.run solver) with
      | .error _ => .error "error encoding verification conditions or running solver"
      | .ok b => .ok b

@[implemented_by unsafeSolve]
opaque solve {α} (solver : IO Solver) (vcs : SolverM α) : Except String α

private unsafe def unsafeTimedSolve {α} (solver: IO Solver) (vcs : SolverM α) : Except String (Timed α) :=
  let result := unsafeBaseIO (runAndTime (λ () => solve solver vcs))
  match result.data with
  | .ok res => .ok ( { data := res, duration := result.duration })
  | .error s => .error s

@[implemented_by unsafeTimedSolve]
opaque timedSolve {α} (solver : IO Solver) (vcs : SolverM α) : Except String (Timed α)

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckNeverErrors] unsafe def runCheckNeverErrors (req : ByteArray) : String :=
  let result : Except String (Timed Bool) :=
    match parseCheckPolicyReq req with
    | .error s => .error s!"checkNeverErrors: {s}"
    | .ok (policy, εnv) =>
      match timedSolve Solver.cvc5 (Cedar.SymCC.checkNeverErrors policy εnv) with
      | .error s => .error s!"checkNeverErrors: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckAlwaysAllows] unsafe def runCheckAlwaysAllows (req : ByteArray) : String :=
  let result : Except String (Timed Bool) :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysAllows: {s}"
    | .ok (policies, εnv) =>
      match timedSolve Solver.cvc5 (Cedar.SymCC.checkAlwaysAllows policies εnv) with
      | .error s => .error s!"checkAlwaysAllows: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckAlwaysDenies] unsafe def runCheckAlwaysDenies (req : ByteArray) : String :=
  let result : Except String (Timed Bool) :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysDenies: {s}"
    | .ok (policies, εnv) =>
      match timedSolve Solver.cvc5 (Cedar.SymCC.checkAlwaysDenies policies εnv) with
      | .error s => .error s!"checkAlwaysDenies: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckEquivalent] unsafe def runCheckEquivalent (req : ByteArray) : String :=
  let result : Except String (Timed Bool) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkEquivalent: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      match timedSolve Solver.cvc5 (Cedar.SymCC.checkEquivalent srcPolicies tgtPolicies εnv) with
      | .error s => .error s!"checkEquivalent: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckImplies] unsafe def runCheckImplies (req : ByteArray) : String :=
  let result : Except String (Timed Bool) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkImplies: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      match timedSolve Solver.cvc5 (Cedar.SymCC.checkImplies srcPolicies tgtPolicies εnv) with
      | .error s => .error s!"checkImplies: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` holds
  3.) .ok { data := true, duration := <encode+solve_time> } if the solver could prove `req` does not hold
-/
@[export runCheckDisjoint] unsafe def runCheckDisjoint (req : ByteArray) : String :=
  let result : Except String (Timed Bool) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkDisjoint: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      match timedSolve Solver.cvc5 (Cedar.SymCC.checkDisjoint srcPolicies tgtPolicies εnv) with
      | .error s => .error s!"checkDisjoint: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  Auxillary function that encodes and runs the solver on the generated VCs. Useful for
  running the File or Buffer based solvers to print or stringify the SMTLib representation
  of the VCs.
-/
private def ignoreOutput (vc : SymEnv → Cedar.SymCC.Result Cedar.SymCC.Asserts) (εnv : SymEnv) : SolverM Unit := do
  match vc εnv with
  | .ok asserts =>
    if asserts.any (· == false) || asserts.all (· == true) then
      Solver.reset
    else
      let _ ← Encoder.encode asserts εnv (produceModels := false)
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
@[export printCheckNeverErrors] unsafe def printCheckNeverErrors (req : ByteArray) : String :=
  let result : Except String (Timed Unit) :=
    match parseCheckPolicyReq req with
    | .error s => .error s!"checkNeverErrors: {s}"
    | .ok (policy, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyNeverErrors policy) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkNeverErrors: {s}"
      | .ok r => .ok r
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckAlwaysAllows] unsafe def printCheckAlwaysAllows (req : ByteArray) : String :=
  let result : Except String (Timed Unit) :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysAllows: {s}"
    | .ok (policies, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyAlwaysAllows policies) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkAlwaysAllows: {s}"
      | .ok r => .ok r
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckAlwaysDenies] unsafe def printCheckAlwaysDenies (req : ByteArray) : String :=
  let result : Except String (Timed Unit) :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysDenies: {s}"
    | .ok (policies, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyAlwaysDenies policies) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkAlwaysDenies: {s}"
      | .ok r => .ok r
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckEquivalent] unsafe def printCheckEquivalent (req : ByteArray) : String :=
  let result : Except String (Timed Unit) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkEquivalent: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyEquivalent srcPolicies tgtPolicies) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkEquivalent: {s}"
      | .ok r => .ok r
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckImplies] unsafe def printCheckImplies (req : ByteArray) : String :=
  let result : Except String (Timed Unit) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkImplies: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyImplies srcPolicies tgtPolicies) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkImplies: {s}"
      | .ok r => .ok r
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckDisjoint] unsafe def printCheckDisjoint (req : ByteArray) : String :=
  let result : Except String (Timed Unit) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkDisjoint: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyDisjoint srcPolicies tgtPolicies) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkDisjoint: {s}"
      | .ok r => .ok r
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `CheckAsserts`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok { data := true, duration := <solve_time> } if the solver could prove `asserts` hold
  3.) .ok { data := true, duration := <solve_time> } if the solver could prove `asserts` do not hold
-/
@[export runCheckAsserts] unsafe def runCheckAsserts (req: ByteArray) : String :=
  let result: Except String (Timed Bool) :=
    match parseCheckAssertsReq req with
    | .error s => .error s!"runCheckAsserts: {s}\n{repr req}"
    | .ok (asserts, εnv) =>
      match timedSolve Solver.cvc5 (Cedar.SymCC.checkUnsat (λ _ => .ok asserts) εnv) with
      | .error s => .error s!"runCheckAsserts: {s}"
      | .ok r => .ok r
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `CheckAsserts`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := (), duration := <encode+print_time>} if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckAsserts] unsafe def printCheckAsserts (req: ByteArray) : String :=
  let result: Except String (Timed Unit) :=
    match parseCheckAssertsReq req with
    | .error s => .error s!"printCheckAsserts: {s}\n{repr req}"
    | .ok (asserts, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      match timedSolve solver (ignoreOutput (λ _ => .ok asserts) εnv) with
      | .error s => .error s!"printCheckAsserts: {s}"
      | .ok r => .ok r
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for a `CheckAsserts`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckAsserts] unsafe def smtLibOfCheckAsserts (req: ByteArray) : String :=
  let result: Except String (Timed String) :=
    match parseCheckAssertsReq req with
    | .error s => .error s!"smtLibOfCheckAsserts: {s}\n{repr req}"
    | .ok (asserts, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      match timedSolve solver (ignoreOutput (λ _ => .ok asserts) εnv) with
      | .error s => .error s!"smtLibOfCheckAsserts: {s}"
      | .ok r =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"smtLibOfCheckAsserts: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok { data := ((String.fromUTF8? inner_buffer.data).getD ""), duration := r.duration }
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded of the term generated by `verifyNeverErrors`
-/
@[export assertsOfCheckNeverErrors] unsafe def assertsOfCheckNeverErrors (req: ByteArray) : String :=
  let result : Except String (Timed (Cedar.SymCC.Result Cedar.SymCC.Asserts)) :=
    match parseCheckPolicyReq req with
    | .error s => .error s!"assertsOfCheckNeverErrors: {s}"
    | .ok (policy, εnv) =>
      let result := runAndTime (λ () => verifyNeverErrors policy εnv)
      .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPoliciesRequest`

  returns JSON encoded of the term generated by `verifyAlwaysAllows`
-/
@[export assertsOfCheckAlwaysAllows] unsafe def assertsOfCheckAlwaysAllows (req: ByteArray) : String :=
  let result : Except String (Timed (Cedar.SymCC.Result Cedar.SymCC.Asserts)) :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"assertsOfCheckAlwaysAllows: {s}"
    | .ok (policies, εnv) =>
      let result := runAndTime (λ () => verifyAlwaysAllows policies εnv)
      .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPoliciesRequest`

  returns JSON encoded of the term generated by `verifyAlwaysDenies`
-/
@[export assertsOfCheckAlwaysDenies] unsafe def assertsOfCheckAlwaysDenies (req: ByteArray) : String :=
  let result : Except String (Timed (Cedar.SymCC.Result Cedar.SymCC.Asserts)) :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"assertsOfCheckAlwaysDenies: {s}"
    | .ok (policies, εnv) =>
      let result := runAndTime (λ () => verifyAlwaysDenies policies εnv)
      .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyEquivalent`
-/
@[export assertsOfCheckEquivalent] unsafe def assertsOfCheckEquivalent (req: ByteArray) : String :=
  let result : Except String (Timed (Cedar.SymCC.Result Cedar.SymCC.Asserts)) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"assertsOfCheckEquivalent: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let result := runAndTime (λ () => verifyEquivalent srcPolicies tgtPolicies εnv)
      .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyImplies`
-/
@[export assertsOfCheckImplies] unsafe def assertsOfCheckImplies (req: ByteArray) : String :=
  let result : Except String (Timed (Cedar.SymCC.Result Cedar.SymCC.Asserts)) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"assertsOfCheckImplies: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let result := runAndTime (λ () => verifyImplies srcPolicies tgtPolicies εnv)
      .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded of the term generated by `verifyDisjoint`
-/
@[export assertsOfCheckDisjoint] unsafe def assertsOfCheckDisjoint (req: ByteArray) : String :=
  let result : Except String (Timed (Cedar.SymCC.Result Cedar.SymCC.Asserts)) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"assertsOfCheckDisjoint: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let result := runAndTime (λ () => verifyDisjoint srcPolicies tgtPolicies εnv)
      .ok (unsafeBaseIO result)
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckNeverErrors] unsafe def smtLibOfCheckNeverErrors (req : ByteArray) : String :=
  let result : Except String (Timed String) :=
    match parseCheckPolicyReq req with
    | .error s => .error s!"checkNeverErrors: {s}"
    | .ok (policy, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyNeverErrors policy) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkNeverErrors: {s}"
      | .ok r =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkNeverErrors: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok { data := ((String.fromUTF8? inner_buffer.data).getD ""), duration := r.duration }
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckAlwaysAllows] unsafe def smtLibOfCheckAlwaysAllows (req : ByteArray) : String :=
  let result : Except String (Timed String) :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysAllows: {s}"
    | .ok (policies, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyAlwaysAllows policies) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkAlwaysAllows: {s}"
      | .ok r =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkAlwaysAllows: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok { data := ((String.fromUTF8? inner_buffer.data).getD ""), duration := r.duration }
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckAlwaysDenies] unsafe def smtLibOfCheckAlwaysDenies (req : ByteArray) : String :=
  let result : Except String (Timed String) :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysDenies: {s}"
    | .ok (policies, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyAlwaysDenies policies) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkAlwaysDenies: {s}"
      | .ok r =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkAlwaysDenies: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok { data := ((String.fromUTF8? inner_buffer.data).getD ""), duration := r.duration }
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckEquivalent] unsafe def smtLibOfCheckEquivalent (req : ByteArray) : String :=
  let result : Except String (Timed String) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkEquivalent: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyEquivalent srcPolicies tgtPolicies) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkEquivalent: {s}"
      | .ok r =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkEquivalent: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok { data := ((String.fromUTF8? inner_buffer.data).getD ""), duration := r.duration }
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckImplies] unsafe def smtLibOfCheckImplies (req : ByteArray) : String :=
  let result : Except String (Timed String) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkImplies: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyImplies srcPolicies tgtPolicies) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkImplies: {s}"
      | .ok r =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkImplies: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok { data := ((String.fromUTF8? inner_buffer.data).getD ""), duration := r.duration }
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok {data := SMTLib-Script, duration := encode_time} where SMTLib-Script is a
      string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckDisjoint] unsafe def smtLibOfCheckDisjoint (req : ByteArray) : String :=
  let result : Except String (Timed String) :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkDisjoint: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyDisjoint srcPolicies tgtPolicies) εnv
      match timedSolve solver vcs with
      | .error s => .error s!"checkDisjoint: {s}"
      | .ok r =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkDisjoint: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok { data := ((String.fromUTF8? inner_buffer.data).getD ""), duration := r.duration }
  toString (Lean.toJson result)

end CedarFFI
