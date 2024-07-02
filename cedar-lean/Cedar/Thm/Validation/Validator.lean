import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Data

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

-- for a single expression, evaluates to a boolean value (or appropriate error)
def OneEvaluatesCorrectly (expr : Expr) (request : Request) (entities : Entities) : Prop :=
∃ (b : Bool), EvaluatesTo expr request entities b

-- every policy as an expression evaluates to a boolean value or appropriate error
def AllEvaluateCorrectly (policies : Policies) (request : Request) (entities : Entities) : Prop :=
∀ policy : Policy, policy ∈ policies → OneEvaluatesCorrectly policy.toExpr request entities

def EvaluatesSubst (expr : Expr) (request : Request) (entities : Entities) : Prop :=
evaluate (substituteAction request.action expr) request entities = evaluate expr request entities

theorem evaluates_subst_ite {i t e : Expr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst i request entities)
(ih₂ : EvaluatesSubst t request entities)
(ih₃ : EvaluatesSubst e request entities) :
evaluate (substituteAction request.action (Expr.ite i t e)) request entities =
evaluate (Expr.ite i t e) request entities := by
simp [EvaluatesSubst] at *
simp [evaluate]
cases h₀ : Result.as Bool (evaluate i request entities) <;> simp [h₀]
case error =>
  simp [Result.as] at h₀
  cases h₁ : evaluate i request entities <;> simp [h₁] at h₀
  rename_i e1 e2
  simp [substituteAction]
  sorry
  sorry
case ok => sorry

theorem evaluates_subst_unaryApp {op : UnaryOp} {e : Expr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst e request entities) :
evaluate (substituteAction request.action (Expr.unaryApp op e)) request entities =
evaluate (Expr.unaryApp op e) request entities := by
simp [EvaluatesSubst] at ih₁
simp [evaluate]
cases h₀ : evaluate e request entities <;> simp [h₀]
case error e₁ =>
  simp [substituteAction, mapOnVars] at *
  simp [evaluate] at *
  -- cannot use evaluate (mapOnVars (fun var ....)) here
  sorry
case ok v => sorry

theorem evaluates_subst (expr : Expr) (request : Request) (entities : Entities) :
evaluate (substituteAction request.action expr) request entities =
evaluate expr request entities := by
cases h₀ : expr with
| lit p => simp [substituteAction, mapOnVars]
| var vr =>
  cases h₁ : vr <;> simp [substituteAction, mapOnVars] <;> try assumption
  case action => sorry
| ite i t e =>
  have ih₁ := evaluates_subst i request entities
  have ih₂ := evaluates_subst t request entities
  have ih₃ := evaluates_subst e request entities
  exact @evaluates_subst_ite i t e request entities ih₁ ih₂ ih₃
| and a b => sorry
| or a b => sorry
| unaryApp op e =>
  have ih₁ := evaluates_subst e request entities
  exact @evaluates_subst_unaryApp op e request entities ih₁
| binaryApp op a b => sorry
| getAttr x => sorry
| hasAttr x attr => sorry
| set x => sorry
| record x => sorry
| call x args => sorry


theorem action_matches_env (env : Environment) (request : Request) (entities : Entities) :
RequestAndEntitiesMatchEnvironment env request entities →
request.action = env.reqty.action := by
intro h₀
simp [RequestAndEntitiesMatchEnvironment, InstanceOfRequestType] at h₀
obtain ⟨ ⟨ _, h₁, _, _ ⟩ , _ , _⟩ := h₀
assumption

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
simp [EvaluatesTo]
sorry
-- rw [← evaluates_subst policy.toExpr request entities]
-- rw [action_matches_env]
-- repeat assumption


-- From Mathlib [https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Forall2.html#List.forall%E2%82%82_cons_right_iff]
theorem forall₂_cons_left_iff {a l u} :
    List.Forall₂ R (a :: l) u ↔ ∃ b u', R a b ∧ List.Forall₂ R l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', List.Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨_, _, h₁, h₂, rfl⟩ => List.Forall₂.cons h₁ h₂

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
      rw [List.mapM_ok_iff_forall₂] at h₃
      have h₆ : RequestAndEntitiesMatchEnvironment h request entities := by
        have h₇ : h ∈ envs := by simp [h₄]
        specialize h₀ h
        apply h₀ h₇
      subst h₄
      rw [forall₂_cons_left_iff] at h₃
      simp at h₃
      obtain ⟨ b, _, _, _, _ ⟩ := h₃
      apply typecheck_policy_is_sound policy h b
      repeat assumption

end Cedar.Thm
