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
This file defines the top-level soundness property for the valdator.

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
theorem typecheckPolicy_is_sound (policy : Policy) (env : Environment) (t : CedarType) (request : Request) (entities : Entities) :
  RequestAndEntitiesMatchEnvironment env request entities →
  typecheckPolicy policy env = .ok t →
  EvaluatesToBool policy request entities
:= by
  intro h₀ h₁
  unfold typecheckPolicy at h₁
  cases h₂ : (typeOf (Policy.toExpr policy) ∅ env) <;>
  rw [h₂] at h₁ <;>
  simp at h₁
  case ok res =>
    cases h₃ : (res.fst ⊑ CedarType.bool BoolType.anyBool) <;>
    rw [h₃] at h₁ <;>
    simp at h₁
    clear h₁ t
    have h₁ : GuardedCapabilitiesInvariant policy.toExpr res.2 request entities ∧ ∃ (v : Value), EvaluatesTo policy.toExpr request entities v ∧ InstanceOfType v res.1 := by
      apply typeOf_is_sound (env:=env) (c₁:=∅)
      apply empty_CapabilitiesInvariant
      apply h₀
      apply h₂
    cases h₁ with
    | intro _ h₁ =>
      cases h₁ with
      | intro v h₁ =>
        cases h₁ with
        | intro h₁ h₄ =>
          have h₅ : ∃ b, v = .prim (.bool b) := by
            apply instance_of_type_bool_is_bool
            apply h₄
            apply h₃
          cases h₅ with
          | intro b h₅ =>
            unfold EvaluatesToBool
            exists b
            rewrite [← h₅]
            apply h₁

def RequestMatchesSchema (schema : Schema) (request : Request) : Prop :=
  match schema.acts.find? request.action with
  | some entry =>
      request.principal.ty ∈ entry.appliesToPricipal ∧
      request.resource.ty ∈ entry.appliesToResource ∧
      InstanceOfType request.context (.record entry.context)
  | _ => False

def RequestAndEntitiesMatchSchema (schema : Schema) (request : Request) (entities : Entities) : Prop :=
  RequestMatchesSchema schema request ∧
  InstanceOfEntityTypeStore entities schema.ets ∧
  InstanceOfActionStore entities (schema.acts.mapOnValues (fun entry => entry.descendants))

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
