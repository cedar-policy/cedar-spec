import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Data

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

-- def RequestConsistentWithSchema (schema : Schema) (request : Request) : Prop :=
--   match schema.acts.find? request.action with
--   | some e =>
--       request.principal.ty ∈ e.appliesToPrincipal ∧
--       request.resource.ty ∈ e.appliesToResource ∧
--       InstanceOfType request.context (.record e.context)
--   | _ => False


theorem evaluates_subst (policy : Policy) (req : Request) (entities : Entities) (v : Value) :
EvaluatesTo (substituteAction request.action policy.toExpr) request entities value →
 EvaluatesTo policy.toExpr request entities value := by
 intro h₀
 simp [substituteAction] at h₀
 cases h₁ : policy.toExpr <;> simp [h₁, mapOnVars] at h₀
 case lit =>
  assumption
 case var vr =>
  cases h₂ : vr <;> simp [h₂] at h₀ <;> try assumption
  case action => sorry
 case ite i t e => sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry
 sorry


theorem matchesEnv (env : Environment) (request : Request) (entities : Entities) :
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
apply evaluates_subst policy request entities (Value.prim (Prim.bool b))
rw [matchesEnv]
repeat assumption


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
