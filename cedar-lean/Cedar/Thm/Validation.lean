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
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Levels
import Cedar.Thm.Validation.Slice
import Cedar.Thm.Validation.Validator
import Cedar.Thm.Validation.RequestEntityValidation
import Cedar.Thm.Validation.EnvironmentValidation
import Cedar.Thm.Validation.Levels
import Cedar.Thm.Validation.SubstituteAction
import Cedar.Thm.Validation.Typechecker

/-!
This file contains the top-level correctness properties for the Cedar validator.
We show that if validation succeeds for a set of policies, then for any request
consistent with the schema, evaluating a policy in this set either produces a
boolean value, or throws one of the errors in the set of valid errors.
--/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
If a set of policies is well-typed (valid) with respect to the schema according to the validator,
and the input request and entities are consistent with the schema, then evaluating a policy in this set
either produces a boolean value, or throws an error of type `entityDoesNotExist`, `extensionError`, or
`arithBoundsError`. These errors cannot be protected against at validation time, as they depend on runtime
information.
-/

theorem validation_is_sound (policies : Policies) (schema : Schema) (request : Request) (entities : Entities) :
  schema.validateWellFormed = .ok () →
  validate policies schema = .ok () →
  validateRequest schema request = .ok () →
  validateEntities schema entities = .ok () →
  AllEvaluateToBool policies request entities
:= by
  intro hwf h₀ h₁ h₂
  have h₁ := request_and_entities_validate_implies_instance_of_wf_schema schema request entities hwf h₁ h₂
  unfold validate at h₀
  simp only [AllEvaluateToBool]
  cases h₃ : policies with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons h' t' =>
    intro policy pin
    simp only [EvaluatesToBool]
    apply typecheck_policy_with_environments_is_sound policy schema request entities h₁
    subst h₃
    simp only [List.forM_eq_forM, List.forM_cons] at h₀
    simp_do_let (typecheckPolicyWithEnvironments typecheckPolicy h' schema) as h₄ at h₀
    case ok _ =>
      rw [List.mem_cons] at pin
      cases pin with
      | inl h₅ =>
        subst h₅
        exact h₄
      | inr h₅ =>
        apply List.forM_ok_implies_all_ok t' (typecheckPolicyWithEnvironments _ · schema)
        repeat assumption

/--
If a set of policies is well-typed and validates at a level `n`, then any
authorization request made using a slice of entities obtained by slicing at
level `n` will return the same response as authorizing using the original
entities.
-/
theorem validate_with_level_is_sound {ps : Policies} {schema : Schema} {n : Nat} {request : Request} {entities : Entities}
  (hwf : schema.validateWellFormed = .ok ())
  (hr : validateRequest schema request = .ok ())
  (he : validateEntities schema entities = .ok ())
  (htl : validateWithLevel ps schema n = .ok ()) :
  isAuthorized request entities ps = isAuthorized request (entities.sliceAtLevel request n) ps
:= validate_with_level_is_sound_wf (request_and_entities_validate_implies_instance_of_wf_schema _ _ _ hwf hr he) htl

/--
End-to-end statement of issue #642 for a validated policy set, phrased over the
*executable* closure check `Entities.closedAtLevel`: if `ps` validates at level
`n` and the store passes `entities.closedAtLevel request n`, then no policy
evaluates to `entityDoesNotExist`.  These are exactly the evaluations
`isAuthorized` performs, so this is the per-policy guarantee `isAuthorized`
inherits: the authorizer surfaces evaluation results only through the
kind-agnostic `errorPolicies` / `satisfiedPolicies` and never raises
`entityDoesNotExist` of its own.  Mirrors `validate_with_level_is_sound`, with the
runtime closure obligation discharged by running `Entities.closedAtLevel`
(`closedAtLevel_iff` bridges it to the `EntitiesClosedAtLevel` predicate).
-/
theorem validate_with_level_no_dne {ps : Policies} {schema : Schema} {n : Nat} {request : Request} {entities : Entities}
  (hwf : schema.validateWellFormed = .ok ())
  (hr : validateRequest schema request = .ok ())
  (he : validateEntities schema entities = .ok ())
  (hcl : entities.closedAtLevel request n)
  (htl : validateWithLevel ps schema n = .ok ()) :
  ∀ p ∈ ps, evaluate p.toExpr request entities ≠ .error .entityDoesNotExist
:= validate_with_level_no_dne_wf
    (request_and_entities_validate_implies_instance_of_wf_schema _ _ _ hwf hr he)
    (closedAtLevel_iff.mp hcl) htl

end Cedar.Thm
