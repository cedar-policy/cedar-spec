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

import Cedar.Validation.Typechecker
import Cedar.Validation.Levels

/-! This file defines the Cedar validator. -/

namespace Cedar.Validation

open Cedar.Spec
open Cedar.Data

----- Definitions -----

/--
For a given action, compute the cross-product of the applicable principal and
resource types.
-/
def ActionSchemaEntry.requestTypes (action : EntityUID) (entry : ActionSchemaEntry) : List RequestType :=
  entry.appliesToPrincipal.toList.foldl (fun acc principal =>
    let reqtys : List RequestType :=
      entry.appliesToResource.toList.map (fun resource =>
        {
          principal := principal,
          action := action,
          resource := resource,
          context := entry.context
        })
    reqtys ++ acc) ∅

/-- Return every schema-defined environment. -/
def Schema.environments (schema : Schema) : List TypeEnv :=
  let requestTypes : List RequestType :=
    schema.acts.toList.foldl (fun acc (action,entry) => entry.requestTypes action ++ acc) ∅
  requestTypes.map ({
    ets := schema.ets,
    acts := schema.acts,
    reqty := ·
  })

/--
  Return all the schema-defined environments for a particular `action`, or
  `none` if this action is not declared in the schema.

  Note that `some ∅` means something different than `none` -- `some ∅` means
  that the `action` was declared in the schema, but there are no valid
  environments for it
-/
def Schema.environmentsForAction? (schema : Schema) (action : EntityUID) : Option (List TypeEnv) := do
  let ase ← schema.acts.find? action
  let p_r_pairs := List.productTR ase.appliesToPrincipal.elts ase.appliesToResource.elts
  some $ p_r_pairs.map λ (principal, resource) => {
    ets := schema.ets,
    acts := schema.acts,
    reqty := {
      principal,
      action,
      resource,
      context := ase.context,
    }
  }

/--
  Return the environment for the particular (p,a,r) tuple, or `none` if this
  is not a valid tuple in this schema
-/
def Schema.environment? (schema : Schema) (principal resource : EntityType) (action : EntityUID) : Option TypeEnv := do
  let ase ← schema.acts.find? action
  match ase.appliesToPrincipal.contains principal, ase.appliesToResource.contains resource with
  | true, true => some {
    ets := schema.ets,
    acts := schema.acts,
    reqty := {
      principal,
      action,
      resource,
      context := ase.context,
    }
  }
  | _, _ => none -- principal and/or resource type are invalid for that action

inductive ValidationError where
  | typeError (pid : PolicyID) (error : TypeError)
  | levelError (pid : PolicyID)
  | impossiblePolicy (pid : PolicyID)

abbrev ValidationResult := Except ValidationError Unit

def mapOnVars (f : Var → Expr) : Expr → Expr
  | .lit l => .lit l
  | .var var => f var
  | .ite x₁ x₂ x₃ =>
    let x₁ := mapOnVars f x₁
    let x₂ := mapOnVars f x₂
    let x₃ := mapOnVars f x₃
    .ite x₁ x₂ x₃
  | .and x₁ x₂ =>
    let x₁ := mapOnVars f x₁
    let x₂ := mapOnVars f x₂
    .and x₁ x₂
  | .or x₁ x₂ =>
    let x₁ := mapOnVars f x₁
    let x₂ := mapOnVars f x₂
    .or x₁ x₂
  | .unaryApp op₁ x₁ =>
    let x₁ := mapOnVars f x₁
    .unaryApp op₁ x₁
  | .binaryApp op₂ x₁ x₂ =>
    let x₁ := mapOnVars f x₁
    let x₂ := mapOnVars f x₂
    .binaryApp op₂ x₁ x₂
  | .hasAttr x₁ a =>
    let x₁ := mapOnVars f x₁
    .hasAttr x₁ a
  | .getAttr x₁ a =>
    let x₁ := mapOnVars f x₁
    .getAttr x₁ a
  | .set xs =>
    let xs := xs.attach.map (λ ⟨x, _⟩ => mapOnVars f x)
    .set xs
  | .record axs =>
    let axs := axs.attach₂.map (λ ⟨(a, x), _⟩ => (a, mapOnVars f x))
    .record axs
  | .call xfn xs =>
    let xs := xs.attach.map (λ ⟨x, _⟩ => mapOnVars f x)
    .call xfn xs

/- Substitute `action` variable for a literal EUID to improve typechecking precision. -/
def substituteAction (uid : EntityUID) (expr : Expr) : Expr :=
  let f (var : Var) : Expr :=
    match var with
    | .action => .lit (.entityUID uid)
    | _ => .var var
  mapOnVars f expr

/-- Check that a policy is Boolean-typed. -/
def typecheckPolicy (policy : Policy) (env : TypeEnv) : Except ValidationError TypedExpr :=
  let expr := substituteAction env.reqty.action policy.toExpr
  match typeOf expr ∅ env with
  | .ok (tx, _) =>
    if tx.typeOf ⊑ .bool .anyBool
    then .ok tx
    else .error (.typeError policy.id (.unexpectedType tx.typeOf))
  | .error e => .error (.typeError policy.id e)

def typecheckPolicyWithLevel (policy : Policy) (level : Nat) (env : TypeEnv) : Except ValidationError TypedExpr := do
  let tx ← typecheckPolicy policy env
  if tx.checkLevel env level then
    .ok tx
  else
    .error (.levelError policy.id)

def allFalse (txs : List TypedExpr) : Bool :=
  txs.all (TypedExpr.typeOf · == .bool .ff)

/-- Check a policy under multiple environments. -/
def typecheckPolicyWithEnvironments (policy : Policy) (envs : List TypeEnv) : ValidationResult := do
  let policyTypes ← envs.mapM (typecheckPolicy policy)
  if allFalse policyTypes then .error (.impossiblePolicy policy.id) else .ok ()

/-- Check a policy with a level under multiple environments. -/
def typecheckPolicyWithLevelWithEnvironments (policy : Policy) (level : Nat) (envs : List TypeEnv) : ValidationResult := do
  let policyTypes ← envs.mapM (typecheckPolicyWithLevel policy level)
  if allFalse policyTypes then .error (.impossiblePolicy policy.id) else .ok ()

/--
Analyze a set of policies to check that all are boolean-typed, and that
none are guaranteed to be false under all possible environments.
-/
def validate (policies : Policies) (schema : Schema) : ValidationResult :=
  policies.forM (typecheckPolicyWithEnvironments · schema.environments)

/--
Analyze a set of policies to check that all are boolean-typed, and that
none are guaranteed to be false under all possible environments.
-/
def validateWithLevel (policies : Policies) (schema : Schema) (level : Nat) : ValidationResult :=
  policies.forM (typecheckPolicyWithLevelWithEnvironments · level schema.environments)

----- Derivations -----

deriving instance Repr for ValidationError

/-
Lossy serialization of errors to Json. This serialization provides some extra
information to DRT without having to derive `Lean.ToJson` for `Expr` and `CedarType`.
-/
def validationErrorToJson : ValidationError → Lean.Json
  | .typeError _ (.lubErr _ _) => "lubErr"
  | .typeError _ (.unexpectedType _) => "unexpectedType"
  | .typeError _ (.attrNotFound _ _) => "attrNotFound"
  | .typeError _ (.tagNotFound _ _) => "tagNotFound"
  | .typeError _ (.unknownEntity _) => "unknownEntity"
  | .typeError _ (.extensionErr _) => "extensionErr"
  | .typeError _ .emptySetErr => "emptySetErr"
  | .typeError _ (.incompatibleSetTypes _) => "incompatibleSetTypes"
  | .levelError _ => "levelError"
  | .impossiblePolicy _ => "impossiblePolicy"

instance : Lean.ToJson ValidationError where
  toJson := validationErrorToJson

-- Used to serialize `ValidationResult`
deriving instance Lean.ToJson for Except
instance : Lean.ToJson Unit where
  toJson := λ _ => Lean.Json.null

end Cedar.Validation
