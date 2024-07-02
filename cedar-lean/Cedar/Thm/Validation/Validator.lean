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
simp [EvaluatesSubst, substituteAction, mapOnVars] at *
simp [evaluate, ih₁, ih₂, ih₃]

theorem evaluates_subst_getAttr {e : Expr} {attr : Attr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst e request entities) :
evaluate (substituteAction request.action (Expr.getAttr e attr)) request entities =
evaluate (Expr.getAttr e attr) request entities := by
simp [EvaluatesSubst] at ih₁
simp [substituteAction, mapOnVars] at *
simp [evaluate, ih₁]

theorem evaluates_subst_hasAttr {e : Expr} {attr : Attr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst e request entities) :
evaluate (substituteAction request.action (Expr.hasAttr e attr)) request entities =
evaluate (Expr.hasAttr e attr) request entities := by
simp [EvaluatesSubst] at ih₁
simp [substituteAction, mapOnVars] at *
simp [evaluate, ih₁]

theorem evaluates_subst_unaryApp {op : UnaryOp} {e : Expr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst e request entities) :
evaluate (substituteAction request.action (Expr.unaryApp op e)) request entities =
evaluate (Expr.unaryApp op e) request entities := by
simp [EvaluatesSubst] at ih₁
simp [substituteAction, mapOnVars] at *
simp [evaluate, ih₁]

theorem evaluates_subst_binaryApp {op : BinaryOp} {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst a request entities)
(ih₂ : EvaluatesSubst b request entities) :
evaluate (substituteAction request.action (Expr.binaryApp op a b)) request entities =
evaluate (Expr.binaryApp op a b) request entities := by
simp [EvaluatesSubst] at *
simp [substituteAction, mapOnVars] at *
simp [evaluate, ih₁, ih₂]

theorem evaluates_subst_and {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst a request entities)
(ih₂ : EvaluatesSubst b request entities) :
evaluate (substituteAction request.action (Expr.and a b)) request entities =
evaluate (Expr.and a b) request entities := by
simp [EvaluatesSubst, substituteAction, mapOnVars] at *
simp [evaluate, ih₁, ih₂]

theorem evaluates_subst_or {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst a request entities)
(ih₂ : EvaluatesSubst b request entities) :
evaluate (substituteAction request.action (Expr.or a b)) request entities =
evaluate (Expr.or a b) request entities := by
simp [EvaluatesSubst, substituteAction, mapOnVars] at *
simp [evaluate, ih₁, ih₂]

theorem evaluates_subst_set {xs : List Expr} {request : Request} {entities : Entities}
(ih₁ : ∀ xᵢ, xᵢ ∈ xs → EvaluatesSubst xᵢ request entities) :
evaluate (substituteAction request.action (Expr.set xs)) request entities =
evaluate (Expr.set xs) request entities := by
simp [EvaluatesSubst] at ih₁
sorry

theorem evaluates_subst_record {axs : List (Attr × Expr)} {request : Request} {entities : Entities}
(ih₁ : ∀ axᵢ, axᵢ ∈ axs → EvaluatesSubst axᵢ.snd request entities) :
evaluate (substituteAction request.action (Expr.record axs)) request entities =
evaluate (Expr.record axs) request entities := by
simp [EvaluatesSubst] at ih₁
sorry

theorem evaluates_subst_call {xfn : ExtFun} {xs : List Expr} {request : Request} {entities : Entities}
(ih₁ : ∀ xᵢ, xᵢ ∈ xs → EvaluatesSubst xᵢ request entities) :
evaluate (substituteAction request.action (Expr.call xfn xs)) request entities =
evaluate (Expr.call xfn xs) request entities := by
simp [EvaluatesSubst] at ih₁
sorry

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
| and a b =>
  have ih₁ := evaluates_subst a request entities
  have ih₂ := evaluates_subst b request entities
  exact @evaluates_subst_and a b request entities ih₁ ih₂
| or a b =>
  have ih₁ := evaluates_subst a request entities
  have ih₂ := evaluates_subst b request entities
  exact @evaluates_subst_or a b request entities ih₁ ih₂
| unaryApp op e =>
  have ih₁ := evaluates_subst e request entities
  exact @evaluates_subst_unaryApp op e request entities ih₁
| binaryApp op a b =>
  have ih₁ := evaluates_subst a request entities
  have ih₂:= evaluates_subst b request entities
  exact @evaluates_subst_binaryApp op a b request entities ih₁ ih₂
| getAttr x attr =>
  have ih₁ := evaluates_subst x request entities
  exact @evaluates_subst_getAttr x attr request entities ih₁
| hasAttr x attr =>
  have ih₁ := evaluates_subst x request entities
  exact @evaluates_subst_hasAttr x attr request entities ih₁
| set xs =>
  have ih : ∀ xᵢ, xᵢ ∈ xs → EvaluatesSubst xᵢ request entities := by
    intro xᵢ _
    exact @evaluates_subst xᵢ request entities
  exact @evaluates_subst_set xs request entities ih
| record axs =>
  have ih : ∀ axᵢ, axᵢ ∈ axs → EvaluatesSubst axᵢ.snd request entities := by
    intro axᵢ hᵢ
    have _ : sizeOf axᵢ.snd < 1 + sizeOf axs := by
      apply List.sizeOf_snd_lt_sizeOf_list hᵢ
    exact @evaluates_subst axᵢ.snd request entities
  exact @evaluates_subst_record axs request entities ih
| call xfn xs =>
  have ih : ∀ xᵢ, xᵢ ∈ xs → EvaluatesSubst xᵢ request entities := by
    intro xᵢ _
    exact @evaluates_subst xᵢ request entities
  exact @evaluates_subst_call xfn xs request entities ih



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
-- should probably go in the helper lemmas file 
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
