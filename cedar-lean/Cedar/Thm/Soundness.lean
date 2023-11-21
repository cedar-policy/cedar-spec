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

import Cedar.Spec
import Cedar.Thm.Lemmas.Typechecker
import Mathlib.Data.List.Basic

/-!
This file defines the top-level soundness property for the validator.

todo: fill in `sorry`s. Some invariants may need to be adjusted. The current
definitions are an informed guess based on the corresponding Dafny proof.
--/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation

def EvaluatesToBool (policy : Policy) (request : Request) (entities : Entities) : Prop :=
  ∃ (b : Bool), EvaluatesTo policy.toExpr request entities b

/--
If a policy successfully validates, then evaluating that policy with any request
will either (1) return a Boolean value or (2) return an error of type `entityDoesNotExist`
or `extensionError`. Both options are encoded in the `EvaluatesToBool` predicate.
The validator cannot protect against `entityDoesNotExist` and `extensionError`
errors because it has no knowledge of the entities/context that will be provided
at authorization time.
-/
theorem typecheck_policy_is_sound (policy : Policy) (env : Environment) (t : CedarType) (request : Request) (entities : Entities) :
  RequestAndEntitiesMatchEnvironment env request entities →
  typecheckPolicy policy env = .ok t →
  EvaluatesToBool policy request entities
:= by
  sorry

def RequestMatchesSchema (schema : Schema) (request : Request) : Prop :=
  match schema.acts.find? request.action with
  | some entry =>
      request.principal.ty ∈ entry.appliesToPrincipal ∧
      request.resource.ty ∈ entry.appliesToResource ∧
      InstanceOfType request.context (.record entry.context)
  | _ => False

def RequestAndEntitiesMatchSchema (schema : Schema) (request : Request) (entities : Entities) : Prop :=
  RequestMatchesSchema schema request ∧
  InstanceOfEntityTypeStore entities schema.ets ∧
  InstanceOfActionStore entities (schema.acts.mapOnValues (fun entry => { ancestors := entry.ancestors }))

/--
Top-level soundness theorem: If validation succeeds, then for any request
consistent with the schema, every policy in the store will satisfy `EvaluatesToBool`.
-/
theorem validate_is_sound (policies : Policies) (schema : Schema) (request : Request) (entities : Entities) :
  RequestAndEntitiesMatchSchema schema request entities →
  validate policies schema = .ok () →
  ∀ policy, policy ∈ policies → EvaluatesToBool policy request entities
:= by
  sorry
