/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

/-! This file defines the Cedar validator. -/

namespace Cedar.Validation

open Cedar.Spec
open Cedar.Data

----- Definitions -----

structure SchemaActionEntry where
  appliesToPricipal : Set EntityType
  appliesToResource : Set EntityType
  ancestors : Set EntityUID
  context : RecordType

abbrev SchemaActionStore := Map EntityUID SchemaActionEntry

structure Schema where
  ets : EntityTypeStore
  acts : SchemaActionStore

/--
For a given action, compute the cross-product of the applicable principal and
resource types.
-/
def SchemaActionEntry.toRequestTypes (action : EntityUID) (entry : SchemaActionEntry) : List RequestType :=
  entry.appliesToPricipal.toList.foldl (fun acc principal =>
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
def Schema.toEnvironments (schema : Schema) : List Environment :=
  let requestTypes : List RequestType :=
    schema.acts.toList.foldl (fun acc (action,entry) => entry.toRequestTypes action ++ acc) ∅
  requestTypes.map ({
    ets := schema.ets,
    acts := schema.acts.mapOnValues (fun entry => { ancestors := entry.ancestors }),
    reqty := ·
  })

inductive ValidationError where
  | typeError (pid : PolicyID) (error : TypeError)
  | impossiblePolicy (pid : PolicyID)

abbrev ValidationResult := Except ValidationError Unit

/-- Check that a policy is Boolean-typed. -/
def typecheckPolicy (policy : Policy) (env : Environment) : Except ValidationError CedarType :=
  match typeOf policy.toExpr ∅ env with
  | .ok (ty, _) =>
    if ty ⊑ .bool .anyBool
    then .ok ty
    else .error (.typeError policy.id (.unexpectedType ty))
  | .error e => .error (.typeError policy.id e)

def allFalse (tys : List CedarType) : Bool :=
  tys.all (· == .bool .ff)

/-- Check a policy under multiple environments. -/
def typecheckPolicyWithEnvironments (policy : Policy) (envs : List Environment) : ValidationResult := do
  let policyTypes ← envs.mapM (typecheckPolicy policy)
  if allFalse policyTypes then .error (.impossiblePolicy policy.id) else .ok ()

/--
Analyze a set of policies to checks that all are boolean-typed, and that
none are guaranteed to be false under all possible environments.
-/
def validate (policies : Policies) (schema : Schema) : ValidationResult :=
  let envs := schema.toEnvironments
  policies.forM (typecheckPolicyWithEnvironments · envs)

----- Derivations -----

deriving instance Lean.ToJson for Except
deriving instance Lean.ToJson for ValidationError

instance : Lean.ToJson Unit where
  toJson := λ _ => Lean.Json.null


end Cedar.Validation
