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

module

public import CedarRustModel.Convert
import CedarRustModel.Lemmas.Basic
import CedarRustModel.Ext.Values
import all Cedar.Spec.Policy

/-!
The model of static and template-linked policies (`src/policy.rs`) agrees with
`Cedar/Spec/Policy.lean`; `policy_to_expr` (production's `Policy::condition`)
is `Policy.toExpr`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model Cedar.Spec Cedar.Data

/-! ## Translation -/

@[expose] public section

def Scope.toSpec : policy.Scope → Cedar.Spec.Scope
  | .Any => .any
  | .Eq u => .eq (EntityUID.toSpec u)
  | .Mem u => .mem (EntityUID.toSpec u)
  | .Is n => .is (Name.toSpec n)
  | .IsMem n u => .isMem (Name.toSpec n) (EntityUID.toSpec u)

def ActionScope.toSpec : policy.ActionScope → Cedar.Spec.ActionScope
  | .ActionScope s => .actionScope (Scope.toSpec s)
  | .ActionInAny us => .actionInAny ((List.toList us).map EntityUID.toSpec)

def ConditionKind.toSpec : policy.ConditionKind → Cedar.Spec.ConditionKind
  | .When => .when
  | .Unless => .unless

def Condition.toSpec (c : policy.Condition) : Cedar.Spec.Condition :=
  { kind := ConditionKind.toSpec c.kind, body := Expr.toSpec c.body }

def Conditions.toSpec (cs : value.List policy.Condition) : Cedar.Spec.Conditions :=
  (List.toList cs).map Condition.toSpec

def LinkedPolicy.toSpec (p : policy.LinkedPolicy) : Cedar.Spec.Policy :=
  { id := Str.toSpec p.id
    effect := Effect.toSpec p.effect
    principalScope := .principalScope (Scope.toSpec p.principal_scope)
    actionScope := ActionScope.toSpec p.action_scope
    resourceScope := .resourceScope (Scope.toSpec p.resource_scope)
    condition := Conditions.toSpec p.condition }

end

/-! ## Proofs -/

public section

/-! ### Cloning -/

theorem clone_effect_ok (e : authorizer.Effect) : policy.clone_effect e = ok e := by
  cases e <;> rfl

theorem clone_pattern_ok (p : value.List expr.PatElem) : policy.clone_pattern p = ok p := by
  induction p with
  | Nil => rw [policy.clone_pattern.eq_def]
  | Cons e p ih => rw [policy.clone_pattern.eq_def]; cases e <;> simp [ih]

theorem clone_unary_op_ok (o : expr.UnaryOp) : policy.clone_unary_op o = ok o := by
  cases o <;> simp [policy.clone_unary_op, clone_pattern_ok, clone_name_ok]

theorem clone_binary_op_ok (o : expr.BinaryOp) : policy.clone_binary_op o = ok o := by
  cases o <;> simp [policy.clone_binary_op]

theorem clone_var_ok (v : expr.Var) : policy.clone_var v = ok v := by
  cases v <;> simp [policy.clone_var]

mutual
theorem clone_expr_ok : (x : expr.Expr) → policy.clone_expr x = ok x
  | .Lit p => by rw [policy.clone_expr.eq_def]; simp [clone_prim_ok]
  | .Var v => by rw [policy.clone_expr.eq_def]; simp [clone_var_ok]
  | .Ite x₁ x₂ x₃ => by
    rw [policy.clone_expr.eq_def]; simp [clone_expr_ok x₁, clone_expr_ok x₂, clone_expr_ok x₃]
  | .And x₁ x₂ => by rw [policy.clone_expr.eq_def]; simp [clone_expr_ok x₁, clone_expr_ok x₂]
  | .Or x₁ x₂ => by rw [policy.clone_expr.eq_def]; simp [clone_expr_ok x₁, clone_expr_ok x₂]
  | .UnaryApp o x₁ => by
    rw [policy.clone_expr.eq_def]; simp [clone_unary_op_ok, clone_expr_ok x₁]
  | .BinaryApp o x₁ x₂ => by
    rw [policy.clone_expr.eq_def]; simp [clone_binary_op_ok, clone_expr_ok x₁, clone_expr_ok x₂]
  | .GetAttr x₁ a => by rw [policy.clone_expr.eq_def]; simp [clone_expr_ok x₁, clone_str_ok]
  | .HasAttr x₁ a => by rw [policy.clone_expr.eq_def]; simp [clone_expr_ok x₁, clone_str_ok]
  | .ExtHasAttr x₁ a as' => by
    rw [policy.clone_expr.eq_def]; simp [clone_expr_ok x₁, clone_str_ok, clone_strs_ok]
  | .Set xs => by rw [policy.clone_expr.eq_def]; simp [clone_exprs_ok xs]
  | .Record axs => by rw [policy.clone_expr.eq_def]; simp [clone_attr_exprs_ok axs]
  | .Call f xs => by rw [policy.clone_expr.eq_def]; simp [clone_extfun_ok, clone_exprs_ok xs]
theorem clone_exprs_ok : (xs : value.List expr.Expr) → policy.clone_exprs xs = ok xs
  | .Nil => by rw [policy.clone_exprs.eq_def]
  | .Cons x xs => by
    rw [policy.clone_exprs.eq_def]; simp [clone_expr_ok x, clone_exprs_ok xs]
theorem clone_attr_exprs_ok :
    (axs : value.List (value.List Char × expr.Expr)) → policy.clone_attr_exprs axs = ok axs
  | .Nil => by rw [policy.clone_attr_exprs.eq_def]
  | .Cons (a, x) axs => by
    rw [policy.clone_attr_exprs.eq_def]
    simp [clone_str_ok, clone_expr_ok x, clone_attr_exprs_ok axs]
end

/-! ### Policies as expressions -/

theorem uid_lits_ok (us : value.List value.EntityUID) :
    ∃ xs, policy.uid_lits us = ok xs ∧
      Exprs.toSpec xs = (List.toList us).map fun u => .lit (.entityUID (EntityUID.toSpec u)) := by
  induction us with
  | Nil => rw [policy.uid_lits.eq_def]; simp [Exprs.toSpec]
  | Cons u us ih =>
    obtain ⟨xs, h₁, h₂⟩ := ih
    rw [policy.uid_lits.eq_def]
    simp [clone_uid_ok, h₁, Exprs.toSpec, Expr.toSpec, Prim.toSpec, h₂]

theorem scope_to_expr_ok (s : policy.Scope) (v : expr.Var) :
    ∃ x, policy.scope_to_expr s v = ok x ∧
      Expr.toSpec x = (Scope.toSpec s).toExpr (Var.toSpec v) := by
  cases s <;>
    simp [policy.scope_to_expr, policy.var_eq_uid, policy.var_in_uid, policy.var_is,
      clone_var_ok, clone_uid_ok, clone_name_ok, Scope.toSpec, Cedar.Spec.Scope.toExpr,
      Var.eqEntityUID, Var.inEntityUID, Var.isEntityType, Expr.toSpec, Prim.toSpec,
      UnaryOp.toSpec, BinaryOp.toSpec]

theorem action_scope_to_expr_ok (s : policy.ActionScope) :
    ∃ x, policy.action_scope_to_expr s = ok x ∧
      Expr.toSpec x = (ActionScope.toSpec s).toExpr := by
  cases s with
  | ActionScope s =>
    obtain ⟨x, h₁, h₂⟩ := scope_to_expr_ok s .Action
    simp only [policy.action_scope_to_expr, h₁]
    exact ⟨x, rfl, by simp [h₂, ActionScope.toSpec, Cedar.Spec.ActionScope.toExpr, Var.toSpec]⟩
  | ActionInAny us =>
    obtain ⟨xs, h₁, h₂⟩ := uid_lits_ok us
    simp [policy.action_scope_to_expr, h₁, ActionScope.toSpec, Cedar.Spec.ActionScope.toExpr,
      Expr.toSpec, Var.toSpec, BinaryOp.toSpec, h₂]

theorem condition_to_expr_ok (c : policy.Condition) :
    ∃ x, policy.condition_to_expr c = ok x ∧ Expr.toSpec x = (Condition.toSpec c).toExpr := by
  rcases c with ⟨k, b⟩
  cases k <;>
    simp [policy.condition_to_expr, clone_expr_ok, Condition.toSpec, ConditionKind.toSpec,
      Cedar.Spec.Condition.toExpr, Expr.toSpec, UnaryOp.toSpec]

private theorem Conditions.toExpr_cons_cons (c d : Cedar.Spec.Condition) (cs : Cedar.Spec.Conditions) :
    Cedar.Spec.Conditions.toExpr (c :: d :: cs) =
      Expr.mkAnd c.toExpr (Cedar.Spec.Conditions.toExpr (d :: cs)) := by
  simp only [Cedar.Spec.Conditions.toExpr]
  rw [List.reverse_cons (a := c)]
  generalize h : (d :: cs).reverse = rs
  have hne : rs ≠ [] := by rw [← h]; simp
  match rs, hne with
  | r :: rs', _ => simp [List.foldl_append]

theorem mk_and_ok (x₁ x₂ : expr.Expr) :
    ∃ x, policy.mk_and x₁ x₂ = ok x ∧
      Expr.toSpec x = Expr.mkAnd (Expr.toSpec x₁) (Expr.toSpec x₂) := by
  rcases x₁ with ((b₁|_|_|_)|_|_|_|_|_|_|_|_|_|_|_) <;>
  rcases x₂ with ((b₂|_|_|_)|_|_|_|_|_|_|_|_|_|_|_) <;>
  first
  | (cases b₁ <;> simp [policy.mk_and, Expr.mkAnd, Expr.toSpec, Prim.toSpec])
  | simp [policy.mk_and, Expr.mkAnd, Expr.toSpec, Prim.toSpec]

theorem conditions_to_expr_ok (cs : value.List policy.Condition) :
    ∃ x, policy.conditions_to_expr cs = ok x ∧
      Expr.toSpec x = Cedar.Spec.Conditions.toExpr (Conditions.toSpec cs) := by
  induction cs with
  | Nil =>
    rw [policy.conditions_to_expr.eq_def]
    simp [Conditions.toSpec, Cedar.Spec.Conditions.toExpr, Expr.toSpec, Prim.toSpec]
  | Cons c cs ih =>
    obtain ⟨x, h₁, h₂⟩ := condition_to_expr_ok c
    rw [policy.conditions_to_expr.eq_def]
    cases cs with
    | Nil =>
      simp [h₁, Conditions.toSpec, Cedar.Spec.Conditions.toExpr, h₂]
    | Cons d ds =>
      obtain ⟨y, h₃, h₄⟩ := ih
      obtain ⟨z, h₅, h₆⟩ := mk_and_ok x y
      simp only [h₁, h₃, h₅, bind_ok]
      refine ⟨_, rfl, ?_⟩
      simp only [Conditions.toSpec, List.toList_cons, List.map_cons] at h₄ ⊢
      rw [Conditions.toExpr_cons_cons, h₆, h₂, h₄]

/-- `policy::policy_to_expr` (production's `Policy::condition`) is `Policy.toExpr`. -/
theorem policy_to_expr_ok (p : policy.LinkedPolicy) :
    ∃ x, policy.policy_to_expr p = ok x ∧ Expr.toSpec x = (LinkedPolicy.toSpec p).toExpr := by
  obtain ⟨xp, hp₁, hp₂⟩ := scope_to_expr_ok p.principal_scope .Principal
  obtain ⟨xa, ha₁, ha₂⟩ := action_scope_to_expr_ok p.action_scope
  obtain ⟨xr, hr₁, hr₂⟩ := scope_to_expr_ok p.resource_scope .Resource
  obtain ⟨xc, hc₁, hc₂⟩ := conditions_to_expr_ok p.condition
  obtain ⟨y₁, hy₁, hy₁'⟩ := mk_and_ok xr xc
  obtain ⟨y₂, hy₂, hy₂'⟩ := mk_and_ok xa y₁
  obtain ⟨y₃, hy₃, hy₃'⟩ := mk_and_ok xp y₂
  simp only [policy.policy_to_expr, hp₁, ha₁, hr₁, hc₁, hy₁, hy₂, hy₃, bind_ok]
  refine ⟨y₃, rfl, ?_⟩
  simp only [Cedar.Spec.Policy.toExpr, LinkedPolicy.toSpec, Cedar.Spec.PrincipalScope.toExpr,
    Cedar.Spec.ResourceScope.toExpr, Var.toSpec] at hp₂ hr₂ ⊢
  rw [hy₃', hy₂', hy₁', hp₂, ha₂, hr₂, hc₂]

/-- The authorizer's policy for a linked policy corresponds to it. -/
theorem to_policy_correct (p : policy.LinkedPolicy) :
    ∃ q, policy.to_policy p = ok q ∧ Policy.Corresponds q (LinkedPolicy.toSpec p) := by
  obtain ⟨x, h₁, h₂⟩ := policy_to_expr_ok p
  simp only [policy.to_policy, clone_str_ok, clone_effect_ok, h₁, bind_ok]
  exact ⟨_, rfl, rfl, rfl, h₂.symm⟩

end -- public section

end CedarRustModel
