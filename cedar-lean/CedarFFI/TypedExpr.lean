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
import CedarProto
import Protobuf

import CedarFFI.Main
import CedarFFI.ToJson

/-! Typed-expression FFI entry point (cedar-spec issue #840).

    `validate` reports only whether validation passed. This entry point
    additionally returns the `TypedExpr` that `typecheckPolicy` produces for
    each (policy, environment) pair, so the Rust and Lean typecheckers can be
    compared on the annotated AST rather than on a pass/fail flag.

    The `TypedExpr` encoding is Lean's *derived* `ToJson` for the datatype. It
    is deliberately not hand-written to resemble the Rust representation: the
    Rust side normalises into this shape independently, so agreement between
    the two is not manufactured by a shared, hand-tuned encoder. -/

namespace CedarFFI

open Cedar.Spec
open Cedar.Validation
open Cedar

deriving instance Lean.ToJson for Cedar.Validation.TypedExpr

/-- One (policy, environment) typechecking outcome. The environment is
    identified by a key that both implementations produce independently. -/
structure TypedExprEnvResult where
  principal : String
  action    : String
  resource  : String
  ok        : Bool
  typedExpr : Option TypedExpr
deriving Lean.ToJson

structure TypedExprPolicyResult where
  policyId : String
  envs     : List TypedExprEnvResult
deriving Lean.ToJson

def typecheckOneEnv (p : Cedar.Spec.Policy) (env : TypeEnv) : TypedExprEnvResult :=
  let base : TypedExprEnvResult := {
    principal := toString env.reqty.principal,
    action    := toString env.reqty.action,
    resource  := toString env.reqty.resource,
    ok        := false,
    typedExpr := none
  }
  match typecheckPolicy p env with
  | .ok tx   => { base with ok := true,  typedExpr := some tx }
  | .error _ => { base with ok := false, typedExpr := none }

def typecheckAllPolicies (policies : Policies) (schema : Cedar.Validation.Schema) :
  List TypedExprPolicyResult :=
  policies.map fun p =>
    { policyId := toString p.id,
      envs     := schema.environments.map (typecheckOneEnv p) }

/--
  `req`: binary protobuf for a `ValidationRequest` (the same message `validate` takes)

  returns a string containing JSON
-/
@[export typecheckPolicyTyped] unsafe def typecheckPolicyTypedFFI (req : ByteArray) : String :=
  runFfiM do
    let v ← (@Proto.Message.interpret? Proto.ValidationRequest) req
              |>.mapError (s!"failed to parse input: {·}")
    runAndTime (λ () => typecheckAllPolicies v.policies v.schema)

end CedarFFI
