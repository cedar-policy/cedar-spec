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

import Cedar.Thm.Validation.Typechecker

/-!
This file defines the top-level soundness property for the type checker.
--/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation

def typecheck (policy : Policy) (env : Environment) : Except TypeError CedarType := do
  let (ty, _) ← typeOf policy.toExpr ∅ env
  if ty ⊑ .bool .anyBool
  then .ok ty
  else .error (.unexpectedType ty)

/--
If typechecking succeeds, then for any request consistent with the schema,
either (1) evaluation produces a boolean or (2) it returns an error of type
`entityDoesNotExist`, `extensionError`, or `arithBoundsError`. Both options are
encoded in the `EvaluatesTo` predicate. The type checker cannot protect against
these errors because it has no knowledge of the entities/context that will be
provided at authorization time, and it does not reason about the semantics of
arithmetic operators.
-/
theorem typecheck_is_sound (policy : Policy) (env : Environment) (t : CedarType) (request : Request) (entities : Entities) :
  RequestAndEntitiesMatchEnvironment env request entities →
  typecheck policy env = .ok t →
  (∃ (b : Bool), EvaluatesTo policy.toExpr request entities b)
:= by
  intro h₁ h₂
  simp [typecheck] at h₂
  cases h₃ : typeOf (Policy.toExpr policy) [] env <;> simp [h₃] at h₂
  split at h₂ <;> simp at h₂
  rename_i ht
  have hc := empty_capabilities_invariant request entities
  have ⟨_, v, h₄, h₅⟩ := type_of_is_sound hc h₁ h₃
  rw [h₂] at ht h₅
  have ⟨b, h₆⟩ := instance_of_type_bool_is_bool v t h₅ ht
  subst h₆
  exists b

end Cedar.Thm
