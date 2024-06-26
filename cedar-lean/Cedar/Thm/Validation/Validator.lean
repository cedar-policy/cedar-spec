import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

def RequestConsistentWithSchema (schema : Schema) (request : Request) : Prop :=
  match schema.acts.find? request.action with
  | some e =>
      request.principal.ty ∈ e.appliesToPrincipal ∧
      request.resource.ty ∈ e.appliesToResource ∧
      InstanceOfType request.context (.record e.context)
  | _ => False

def RequestAndEntitiesConsistentWithSchema (schema : Schema) (request : Request) (entities : Entities) : Prop :=
  InstanceOfEntitySchema entities schema.ets ∧
  InstanceOfActionSchema entities schema.acts ∧
  RequestConsistentWithSchema schema request

-- for a single expression, evaluates to a boolean value (or appropriate error)
def OneEvaluatesCorrectly (expr : Expr) (request : Request) (entities : Entities) : Prop :=
∃ (b : Bool), EvaluatesTo expr request entities b

-- every policy as an expression evaluates to a boolean value or appropriate error
def AllEvaluateCorrectly (policies : Policies) (request : Request) (entities : Entities) : Prop :=
∀ policy : Policy, policy ∈ policies → OneEvaluatesCorrectly policy.toExpr request entities


theorem typecheck_policy_is_sound (policy : Policy) (env : Environment) (t : CedarType) (request : Request) (entities : Entities) :
RequestAndEntitiesMatchEnvironment env request entities →
typecheckPolicy policy env = .ok t →
∃ b : Bool, EvaluatesTo policy.toExpr request entities b := by sorry


theorem typecheck_policy_with_environments_is_sound (policy : Policy) (envs : List Environment) (request : Request) (entities : Entities) :
∀ env : Environment, env ∈ envs →
RequestAndEntitiesMatchEnvironment env request entities →
typecheckPolicyWithEnvironments policy envs = .ok () →
∃ b : Bool, EvaluatesTo policy.toExpr request entities b := by
intro env h₀ h₁ h₂
have hc := empty_capabilities_invariant request entities
simp [typecheckPolicyWithEnvironments] at h₂
cases h₃ : List.mapM (typecheckPolicy policy) envs with
| error => simp [h₃] at h₂
| ok ts =>
  simp [h₃] at h₂
  sorry



end Cedar.Thm
