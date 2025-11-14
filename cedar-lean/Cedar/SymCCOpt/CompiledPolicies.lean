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

import Cedar.Spec
import Cedar.SymCC
import Cedar.Validation.Validator

namespace Cedar.SymCC

open Cedar.Spec Cedar.Data

inductive CompiledPolicyError where
  | validationError (e : Validation.ValidationError)
  | symCCError (e : SymCC.Error)
deriving Repr, BEq

instance : ToString CompiledPolicyError where
  toString
  | .validationError e => s!"{e}"
  | .symCCError e => s!"{e}"

/--
Represents a symbolically compiled policy. This can be fed into the various
functions in SymCCOpt.lean for efficient solver queries (that don't have to
repeat symbolic compilation).
-/
structure CompiledPolicy where
  /-- typechecked policy compiled to a `Term` of type .option bool -/
  term : Term
  /-- `SymEnv` representing the environment this policy was compiled for -/
  εnv : SymEnv
  /-- typechecked policy -/
  policy : Policy
  /-- footprint of the policy -/
  footprint : Set Term
  /-- acyclicity constraints for this policy -/
  acyclicity : Set Term
deriving Repr, Inhabited, DecidableEq

/--
Compile a policy `p` for the given environment `Γ`.
This function calls the Cedar typechecker to obtain a policy `p'` that is
semantically equivalent to `p` and well-typed with respect to `Γ`.
Then, it runs the symbolic compiler to produce a compiled policy.
-/
def CompiledPolicy.compile (p : Policy) (Γ : Validation.TypeEnv) : Except CompiledPolicyError CompiledPolicy := do
  let policy ← wellTypedPolicy p Γ |>.mapError .validationError
  let εnv := SymEnv.ofEnv Γ
  let term ← SymCC.compile policy.toExpr εnv |>.mapError .symCCError
  let footprint := SymCC.footprint policy.toExpr εnv
  let acyclicity := footprint.map (SymCC.acyclicity · εnv.entities)
  .ok { term, εnv, policy, footprint, acyclicity }

/--
Represents a symbolically compiled policyset. This can be fed into the various
functions in SymCCOpt.lean for efficient solver queries (that don't have to
repeat symbolic computation).
-/
structure CompiledPolicies where
  /-- typechecked policies compiled to a single `Term` of type .bool representing the authorization decision -/
  term : Term
  /-- `SymEnv` representing the environment these policies were compiled for -/
  εnv : SymEnv
  /-- typechecked policies -/
  policies : Policies
  /-- footprint of the policies -/
  footprint : Set Term
  /-- acyclicity constraints for these policies -/
  acyclicity : Set Term
deriving Repr, Inhabited, DecidableEq

/--
Compile a set of policies `ps` for the given environment `Γ`.
This function calls the Cedar typechecker on each `p ∈ ps` to obtain a policy `p'`
that is semantically equivalent to `p` and well-typed with respect to `Γ`.
Then, it runs the symbolic compiler to produce a compiled policy.
-/
def CompiledPolicies.compile (ps : Policies) (Γ : Validation.TypeEnv) : Except CompiledPolicyError CompiledPolicies := do
  let policies ← wellTypedPolicies ps Γ |>.mapError .validationError
  let εnv := SymEnv.ofEnv Γ
  let term ← isAuthorized policies εnv |>.mapError .symCCError
  let footprint := SymCC.footprints (policies.map Policy.toExpr) εnv
  let acyclicity := footprint.map (SymCC.acyclicity · εnv.entities)
  .ok { term, εnv, policies, footprint, acyclicity }

/--
A `CompiledPolicies` that represents the policyset that allows all requests in
the `εnv`.
-/
def CompiledPolicies.allowAll (εnv : SymEnv) : CompiledPolicies :=
  let allowAll : Policy := {
    id := "allowAll",
    effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope .any,
    resourceScope := .resourceScope .any,
    condition := [],
  }
  let footprint := SymCC.footprint allowAll.toExpr εnv
  {
    term := .bool true
    εnv
    policies := [allowAll]
    footprint
    acyclicity := footprint.map (SymCC.acyclicity · εnv.entities)
  }

/--
A `CompiledPolicies` that represents the policyset that denies all requests in
the `εnv`.
-/
def CompiledPolicies.denyAll (εnv : SymEnv) : CompiledPolicies :=
  {
    term := .bool false
    εnv
    policies := []
    footprint := Set.empty
    acyclicity := Set.empty
  }
