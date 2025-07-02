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
import Cedar.Thm.Validation.Levels

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
  validate policies schema = .ok () →
  validateRequest schema request = .ok () →
  validateEntities schema entities = .ok () →
  schema.wellFormed = .ok () →
  AllEvaluateToBool policies request entities
:= by
  intro h₀ h₁ h₂ h₃
  have h₁ := request_and_entities_validate_implies_match_schema schema request entities h₁ h₂ h₃
  unfold validate at h₀
  simp only [AllEvaluateToBool]
  cases h₄ : policies with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons h' t' =>
    intro policy pin
    simp only [EvaluatesToBool]
    apply typecheck_policy_with_environments_is_sound policy schema.environments request entities h₁
    subst h₄
    simp only [List.forM_eq_forM, List.forM_cons] at h₀
    cases h₄ : (typecheckPolicyWithEnvironments h' schema.environments) <;>
    simp only [h₄, Except.bind_err, reduceCtorEq] at h₀
    case ok _ =>
      rw [List.mem_cons] at pin
      cases pin with
      | inl h₅ =>
        subst h₅
        exact h₄
      | inr h₅ =>
        apply List.forM_ok_implies_all_ok t' (typecheckPolicyWithEnvironments · schema.environments)
        repeat assumption

/--
If a set of policies is well-typed and validates at a level `n`, then any
authorization request made using a slice of entities obtained by slicing at
level `n` will return the same response as authorizing using the original
entities.
-/
theorem validate_with_level_is_sound {ps : Policies} {schema : Schema} {n : Nat} {request : Request} {entities slice : Entities}
  (hr : validateRequest schema request = .ok ())
  (he : validateEntities schema entities = .ok ())
  (hwf : schema.wellFormed = .ok ())
  (hs : slice = entities.sliceAtLevel request n)
  (htl : validateWithLevel ps schema n = .ok ()) :
  isAuthorized request entities ps = isAuthorized request slice ps
:= by
  have hsound : ∀ p ∈ ps, evaluate p.toExpr request entities = evaluate p.toExpr request slice := by
    have hre := request_and_entities_validate_implies_match_schema _ _ _ hr he hwf
    replace htl := List.forM_ok_implies_all_ok _ _ htl
    intro p hp
    exact typecheck_policy_at_level_with_environments_is_sound hs hre (htl p hp)
  exact is_authorized_congr_evaluate hsound

end Cedar.Thm
