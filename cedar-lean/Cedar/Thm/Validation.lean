import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Validator

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
If validation succeeds, then for any request consistent with the schema, either
(1) evaluation of every policy produces a boolean or (2) returns an error TODO
-/
theorem validation_is_sound (policies : Policies) (schema : Schema) (request : Request) (entities : Entities) :
  validate policies schema = .ok () →
  RequestAndEntitiesMatchSchema schema request entities →
  AllEvaluateCorrectly policies request entities
:= by
  intro h₀ h₁
  unfold validate at h₀
  simp only [AllEvaluateCorrectly]
  cases h₃ : policies with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons h' t' =>
    intro policy pin
    simp only [OneEvaluatesCorrectly]
    apply typecheck_policy_with_environments_is_sound policy schema.toEnvironments request entities h₁
    subst h₃
    simp only [List.forM_cons'] at h₀
    cases h₄ : (typecheckPolicyWithEnvironments h' schema.toEnvironments) <;> simp only [h₄,
      Except.bind_err] at h₀
    case ok _ =>
      rw [List.mem_cons] at pin
      cases pin with
      | inl h₅ =>
        subst h₅
        assumption
      | inr h₅ =>
      apply List.forM_implies_all_ok t' (fun x => typecheckPolicyWithEnvironments x schema.toEnvironments)
      repeat assumption

end Cedar.Thm
