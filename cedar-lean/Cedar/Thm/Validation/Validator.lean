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


-- what is the relation between env.reqty.action
theorem evaluates_subst (env : Environment) (policy : Policy) (req : Request) (entities : Entities) (v : Value) :
RequestAndEntitiesMatchEnvironment env request entities →
EvaluatesTo (substituteAction env.reqty.action policy.toExpr) request entities value →
 EvaluatesTo policy.toExpr request entities value := by
 sorry 


theorem typecheck_policy_is_sound (policy : Policy) (env : Environment) (t : CedarType) (request : Request) (entities : Entities) :
RequestAndEntitiesMatchEnvironment env request entities →
typecheckPolicy policy env = .ok t →
∃ b : Bool, EvaluatesTo policy.toExpr request entities b := by
intro h₁ h₂
simp [typecheckPolicy] at h₂
cases h₃ : typeOf (substituteAction env.reqty.action policy.toExpr) [] env <;> simp [h₃] at h₂
split at h₂ <;> simp at h₂
rename_i cp ht
have hc := empty_capabilities_invariant request entities
have ⟨_, v, h₄, h₅⟩ := type_of_is_sound hc h₁ h₃
have ⟨b, h₆⟩ := instance_of_type_bool_is_bool v cp.fst h₅ ht
subst h₆
exists b
apply evaluates_subst env policy request entities (Value.prim (Prim.bool b))
repeat assumption

theorem typecheck_policy_with_environments_is_sound (policy : Policy) (envs : List Environment) (request : Request) (entities : Entities) :
(∀ env : Environment, env ∈ envs →
RequestAndEntitiesMatchEnvironment env request entities) →
typecheckPolicyWithEnvironments policy envs = .ok () →
∃ b : Bool, EvaluatesTo policy.toExpr request entities b := by
intro h₀ h₂
simp [typecheckPolicyWithEnvironments] at h₂
cases h₃ : List.mapM (typecheckPolicy policy) envs with
| error => simp [h₃] at h₂
| ok ts =>
  simp [h₃] at h₂
  cases h₄ : envs with
  | nil =>
    simp [h₄, pure, Except.pure] at h₃
    subst h₃
    simp [allFalse] at h₂
  | cons h t =>
      have h₆ : RequestAndEntitiesMatchEnvironment h request entities := by
        have h₇ : h ∈ envs := by simp [h₄]
        specialize h₀ h
        apply h₀ h₇
      sorry


    -- simp [h₄] at h₃
    -- simp [typecheckPolicy] at h₃
    -- cases h₅ : typeOf (substituteAction h.reqty.action policy.toExpr) [] h <;> simp [h₅] at h₃
    -- split at h₃ <;> simp at h₃
    -- rename_i cp ht
    -- have hc := empty_capabilities_invariant request entities
    -- have h₆ : RequestAndEntitiesMatchEnvironment h request entities := by
    --   have h₇ : h ∈ envs := by simp [h₄]
    --   sorry
    -- have ⟨_, v, h₈, h₉⟩ := type_of_is_sound hc h₆ h₅
    -- have ⟨b, h₁₀⟩ := instance_of_type_bool_is_bool v cp.fst h₉ ht
    -- subst h₁₀
    -- exists b
    -- apply evaluates_subst h policy request entities (Value.prim (Prim.bool b))
    -- assumption


end Cedar.Thm
