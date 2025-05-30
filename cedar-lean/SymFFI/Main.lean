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

namespace Cedar.SymCC.Proto

open Cedar.Spec
open Cedar.SymCC
open Cedar.Validation
open Proto

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  Upon success returns a well-typed policy and symbolic environment corresponding to the request `req`
  Returns a failure if
  1.) Protobuf message could not be parsed
  2.) The requestEnv of `req` is not consistent with the schema of `req`
  3.) The policy of `req` is not well-typed for the requestEnv of `req`
-/
def parseCheckPolicyReq (req : ByteArray) : Except String (Spec.Policy × SymEnv) :=
  match (@Proto.Message.interpret? CheckPolicyRequest) req with
  | .error e => .error s!"failed to parse input: {e}"
  | .ok req =>
    let policy := req.policy
    let schema := req.schema
    let request := req.request
    match schema.environment? request.principal request.resource request.action with
    | none => .error s!"failed to get environment from requestEnv (PrincipalType: {request.principal}, ActionName: {request.action}, ResourceType: {request.resource})"
    | some env =>
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
def parseCheckPoliciesReq (req : ByteArray) : Except String (Spec.Policies × SymEnv) :=
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
def parseComparePolicySetsReq (req : ByteArray) : Except String (Spec.Policies × Spec.Policies × SymEnv) :=
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

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok true if the solver could prove `req` holds
  3.) .ok false if the solver could prove `req` does not hold
-/
@[export runCheckNeverErrors] unsafe def runCheckNeverErrors (req : ByteArray) : String :=
  let result : Except String Bool :=
    match parseCheckPolicyReq req with
    | .error s => .error s!"checkNeverErrors: {s}"
    | .ok (policy, εnv) =>
      match solve Solver.cvc5 (Cedar.SymCC.checkNeverErrors policy εnv) with
      | .error s => .error s!"checkNeverErrors: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok true if the solver could prove `req` holds
  3.) .ok false if the solver could prove `req` does not hold
-/
@[export runCheckAlwaysAllows] unsafe def runCheckAlwaysAllows (req : ByteArray) : String :=
  let result : Except String Bool :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysAllows: {s}"
    | .ok (policies, εnv) =>
      match solve Solver.cvc5 (Cedar.SymCC.checkAlwaysAllows policies εnv) with
      | .error s => .error s!"checkAlwaysAllows: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok true if the solver could prove `req` holds
  3.) .ok false if the solver could prove `req` does not hold
-/
@[export runCheckAlwaysDenies] unsafe def runCheckAlwaysDenies (req : ByteArray) : String :=
  let result : Except String Bool :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysDenies: {s}"
    | .ok (policies, εnv) =>
      match solve Solver.cvc5 (Cedar.SymCC.checkAlwaysDenies policies εnv) with
      | .error s => .error s!"checkAlwaysDenies: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok true if the solver could prove `req` holds
  3.) .ok false if the solver could prove `req` does not hold
-/
@[export runCheckEquivalent] unsafe def runCheckEquivalent (req : ByteArray) : String :=
  let result : Except String Bool :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkEquivalent: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      match solve Solver.cvc5 (Cedar.SymCC.checkEquivalent srcPolicies tgtPolicies εnv) with
      | .error s => .error s!"checkEquivalent: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)
/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok true if the solver could prove `req` holds
  3.) .ok false if the solver could prove `req` does not hold
-/
@[export runCheckImplies] unsafe def runCheckImplies (req : ByteArray) : String :=
  let result : Except String Bool :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkImplies: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      match solve Solver.cvc5 (Cedar.SymCC.checkImplies srcPolicies tgtPolicies εnv) with
      | .error s => .error s!"checkImplies: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `ComparePolicySetsRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or running the solver
  2.) .ok true if the solver could prove `req` holds
  3.) .ok false if the solver could prove `req` does not hold
-/
@[export runCheckDisjoint] unsafe def runCheckDisjoint (req : ByteArray) : String :=
  let result : Except String Bool :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkDisjoint: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      match solve Solver.cvc5 (Cedar.SymCC.checkDisjoint srcPolicies tgtPolicies εnv) with
      | .error s => .error s!"checkDisjoint: {s}"
      | .ok b => .ok b
  toString (Lean.toJson result)

/--
  Auxillary function that encodes and runs the solver on the generated VCs. Useful for
  running the File or Buffer based solvers to print or stringify the SMTLib representation
  of the VCs.
-/
private def ignoreOutput (vc : SymEnv → Result Asserts) (εnv : SymEnv) : SolverM Unit := do
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
  2.) .ok () if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckNeverErrors] unsafe def printCheckNeverErrors (req : ByteArray) : String :=
  let result : Except String Unit :=
    match parseCheckPolicyReq req with
    | .error s => .error s!"checkNeverErrors: {s}"
    | .ok (policy, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyNeverErrors policy) εnv
      match solve solver vcs with
      | .error s => .error s!"checkNeverErrors: {s}"
      | .ok _ => .ok ()
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok () if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckAlwaysAllows] unsafe def printCheckAlwaysAllows (req : ByteArray) : String :=
  let result : Except String Unit :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysAllows: {s}"
    | .ok (policies, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyAlwaysAllows policies) εnv
      match solve solver vcs with
      | .error s => .error s!"checkAlwaysAllows: {s}"
      | .ok _ => .ok ()
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok () if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckAlwaysDenies] unsafe def printCheckAlwaysDenies (req : ByteArray) : String :=
  let result : Except String Unit :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysDenies: {s}"
    | .ok (policies, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyAlwaysDenies policies) εnv
      match solve solver vcs with
      | .error s => .error s!"checkAlwaysDenies: {s}"
      | .ok _ => .ok ()
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok () if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckEquivalent] unsafe def printCheckEquivalent (req : ByteArray) : String :=
  let result : Except String Unit :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkEquivalent: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyEquivalent srcPolicies tgtPolicies) εnv
      match solve solver vcs with
      | .error s => .error s!"checkEquivalent: {s}"
      | .ok _ => .ok ()
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok () if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckImplies] unsafe def printCheckImplies (req : ByteArray) : String :=
  let result : Except String Unit :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkImplies: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyImplies srcPolicies tgtPolicies) εnv
      match solve solver vcs with
      | .error s => .error s!"checkImplies: {s}"
      | .ok _ => .ok ()
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok () if the vcs were successfully printed to stdout in SMTLib format
-/
@[export printCheckDisjoint] unsafe def printCheckDisjoint (req : ByteArray) : String :=
  let result : Except String Unit :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkDisjoint: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let stdOut := unsafeBaseIO IO.getStdout
      let solver := Solver.streamWriter stdOut
      let vcs := ignoreOutput (verifyDisjoint srcPolicies tgtPolicies) εnv
      match solve solver vcs with
      | .error s => .error s!"checkDisjoint: {s}"
      | .ok _ => .ok ()
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicyRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok SMTLib-Script where SMTLib-Script is a string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckNeverErrors] unsafe def smtLibOfCheckNeverErrors (req : ByteArray) : String :=
  let result : Except String String :=
    match parseCheckPolicyReq req with
    | .error s => .error s!"checkNeverErrors: {s}"
    | .ok (policy, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyNeverErrors policy) εnv
      match solve solver vcs with
      | .error s => .error s!"checkNeverErrors: {s}"
      | .ok _ =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkNeverErrors: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok ((String.fromUTF8? inner_buffer.data).getD "")
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok SMTLib-Script where SMTLib-Script is a string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckAlwaysAllows] unsafe def smtLibOfCheckAlwaysAllows (req : ByteArray) : String :=
  let result : Except String String :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysAllows: {s}"
    | .ok (policies, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyAlwaysAllows policies) εnv
      match solve solver vcs with
      | .error s => .error s!"checkAlwaysAllows: {s}"
      | .ok _ =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkAlwaysAllows: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok ((String.fromUTF8? inner_buffer.data).getD "")
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok SMTLib-Script where SMTLib-Script is a string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckAlwaysDenies] unsafe def smtLibOfCheckAlwaysDenies (req : ByteArray) : String :=
  let result : Except String String :=
    match parseCheckPoliciesReq req with
    | .error s => .error s!"checkAlwaysDenies: {s}"
    | .ok (policies, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyAlwaysDenies policies) εnv
      match solve solver vcs with
      | .error s => .error s!"checkAlwaysDenies: {s}"
      | .ok _ =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkAlwaysDenies: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok ((String.fromUTF8? inner_buffer.data).getD "")
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok SMTLib-Script where SMTLib-Script is a string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckEquivalent] unsafe def smtLibOfCheckEquivalent (req : ByteArray) : String :=
  let result : Except String String :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkEquivalent: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyEquivalent srcPolicies tgtPolicies) εnv
      match solve solver vcs with
      | .error s => .error s!"checkEquivalent: {s}"
      | .ok _ =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkEquivalent: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok ((String.fromUTF8? inner_buffer.data).getD "")
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok SMTLib-Script where SMTLib-Script is a string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckImplies] unsafe def smtLibOfCheckImplies (req : ByteArray) : String :=
  let result : Except String String :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkImplies: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyImplies srcPolicies tgtPolicies) εnv
      match solve solver vcs with
      | .error s => .error s!"checkImplies: {s}"
      | .ok _ =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkImplies: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok ((String.fromUTF8? inner_buffer.data).getD "")
  toString (Lean.toJson result)

/--
  `req`: binary protobuf for an `CheckPolicySetRequest`

  returns JSON encoded string that encodes
  1.) .error err_message if there was in error in parsing or encoding the vcs
  2.) .ok SMTLib-Script where SMTLib-Script is a string containing the SMTLib script encoding the verification query
-/
@[export smtLibOfCheckDisjoint] unsafe def smtLibOfCheckDisjoint (req : ByteArray) : String :=
  let result : Except String String :=
    match parseComparePolicySetsReq req with
    | .error s => .error s!"checkDisjoint: {s}"
    | .ok (srcPolicies, tgtPolicies, εnv) =>
      let buffer := unsafeBaseIO (IO.mkRef ⟨ByteArray.empty, 0⟩)
      let solver := Solver.bufferWriter buffer
      let vcs := ignoreOutput (verifyDisjoint srcPolicies tgtPolicies) εnv
      match solve solver vcs with
      | .error s => .error s!"checkDisjoint: {s}"
      | .ok _ =>
        match unsafeIO (buffer.swap ⟨ByteArray.empty, 0⟩) with
        | .error _ => .error s!"checkDisjoint: error retrieving SMTLib script from buffer"
        | .ok inner_buffer => .ok ((String.fromUTF8? inner_buffer.data).getD "")
  toString (Lean.toJson result)

end Cedar.SymCC.Proto
