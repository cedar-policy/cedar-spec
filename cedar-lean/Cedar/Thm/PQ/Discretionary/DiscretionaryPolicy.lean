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

import Cedar.PQ.Discretionary
import Cedar.Thm.Authorization

/-!
This file contains theorems describing the shape and behavior of discretionary policies
-/

namespace Cedar.PQ

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

inductive DiscretionaryPolicy (policy : Policy) : Prop where
  | discretionary {p a r: EntityUID}
    (hp : policy.principalScope.scope.bound = .some p)
    (ha : policy.actionScope = .actionScope (.eq a))
    (hr : policy.resourceScope.scope = .eq r)
    (hc : policy.condition = []) :
    DiscretionaryPolicy policy

theorem eq_scope_authorizes_principal {policy : Policy} {req : Request} {es : Entities} {p : EntityUID} :
  satisfied policy req es = true →
  policy.principalScope.scope = .eq p →
  req.principal = p
:= by
  intro h_satisfied h_scope
  have h_eval : evaluate policy.toExpr req es = .ok (.prim (.bool true)) := by
    simpa [satisfied] using h_satisfied
  have h_principal := and_true_implies_left_true h_eval
  replace h_scope : policy.3.1 = Scope.eq p := h_scope
  simpa [h_scope, evaluate, Var.eqEntityUID, apply₂, PrincipalScope.toExpr, Scope.toExpr] using h_principal

theorem mem_scope_authorizes_principal_ancestor {policy : Policy} {req : Request} {es : Entities} {p : EntityUID} :
  satisfied policy req es = true →
  policy.principalScope.scope = .mem p →
  p = req.principal ∨ (es.ancestorsOrEmpty req.principal).contains p
:= by
  intro h_satisfied h_scope
  have h_eval : evaluate policy.toExpr req es = .ok (.prim (.bool true)) := by
    simpa [satisfied] using h_satisfied
  replace h_eval := and_true_implies_left_true h_eval
  replace h_scope : policy.3.1 = Scope.mem p := h_scope
  simp only [PrincipalScope.toExpr, Scope.toExpr, h_scope, evaluate, Var.inEntityUID, apply₂, inₑ] at h_eval
  cases h_eq : (req.principal == p)
  · right
    simpa [h_eq] using h_eval
  · exact .inl $ beq_iff_eq.mp h_eq|>.symm

theorem is_mem_scope_authorizes_principal_ancestor {policy : Policy} {req : Request} {es : Entities} {ty : EntityType} {p : EntityUID} :
  satisfied policy req es = true →
  policy.principalScope.scope = .isMem ty p →
  p = req.principal ∨ (es.ancestorsOrEmpty req.principal).contains p
:= by
  intro h_satisfied h_scope
  have h_eval : evaluate policy.toExpr req es = .ok (.prim (.bool true)) := by
    simpa [satisfied] using h_satisfied
  replace h_eval := and_true_implies_left_true h_eval
  replace h_scope : policy.3.1 = Scope.isMem ty p := h_scope
  simp only [PrincipalScope.toExpr, Scope.toExpr, h_scope] at h_eval
  replace h_eval := and_true_implies_right_true h_eval
  simp only [evaluate, Var.inEntityUID, apply₂, inₑ] at h_eval
  cases h_eq : (req.principal == p)
  · right
    simpa [h_eq] using h_eval
  · exact .inl $ beq_iff_eq.mp h_eq|>.symm

theorem bound_authorizes_principal_ancestor {policy : Policy} {req : Request} {es : Entities} {p : EntityUID} :
  satisfied policy req es = true →
  policy.principalScope.scope.bound = .some p →
  p = req.principal ∨ (es.ancestorsOrEmpty req.principal).contains p
:= by
  intro h_satisfied h_bound
  cases h_scope : policy.principalScope.scope
  case any | is =>
    simp only [Scope.bound, h_scope, reduceCtorEq] at h_bound
  all_goals
    simp [Scope.bound, h_scope] at h_bound
    subst h_bound
  · simp [eq_scope_authorizes_principal h_satisfied h_scope]
  · simp [mem_scope_authorizes_principal_ancestor h_satisfied h_scope]
  · simp [is_mem_scope_authorizes_principal_ancestor h_satisfied h_scope]

theorem eq_action_authorizes_action {policy : Policy} {req : Request} {es : Entities} {a : EntityUID} :
  satisfied policy req es = true →
  policy.actionScope = .actionScope (.eq a) →
  req.action = a
:= by
  intro h_satisfied h_scope
  have h_eval : evaluate policy.toExpr req es = .ok (.prim (.bool true)) := by
    simpa [satisfied] using h_satisfied
  replace h_action := and_true_implies_left_true (and_true_implies_right_true h_eval)
  simpa [h_scope, evaluate, Var.eqEntityUID, apply₂, ActionScope.toExpr, Scope.toExpr] using h_action

theorem eq_resource_authorizes_resource {policy : Policy} {req : Request} {es : Entities} {r : EntityUID} :
  satisfied policy req es = true →
  policy.resourceScope.scope = .eq r →
  req.resource = r
:= by
  intro h_satisfied h_scope
  have h_eval : evaluate policy.toExpr req es = .ok (.prim (.bool true)) := by
    simpa [satisfied] using h_satisfied
  replace h_eval := and_true_implies_left_true ∘ and_true_implies_right_true ∘ and_true_implies_right_true $ h_eval
  replace h_scope : policy.5.1 = Scope.eq r := h_scope
  simpa [ResourceScope.toExpr, Scope.toExpr, h_scope, evaluate, Var.eqEntityUID, apply₂] using h_eval

theorem discretionary_policy_has_expected_shape {policy : Policy} :
  isPolicyDiscretionary policy = true → DiscretionaryPolicy policy
:= by
  intro h_discretionary
  simp only [isPolicyDiscretionary, List.beq_nil_eq, Bool.and_eq_true, List.isEmpty_iff] at h_discretionary
  have ⟨⟨⟨h_principal_ok, h_action_ok⟩, h_resource_ok⟩, h_condition_empty⟩ := h_discretionary
  have ⟨_, h_p⟩  : ∃ b, policy.principalScope.scope.bound = .some b := by
    cases h_p : policy.principalScope.scope <;>
      simp only [h_p, Bool.false_eq_true] at h_principal_ok
    all_goals
      simp [Scope.bound]
  have ⟨_, h_a⟩ : ∃ a, policy.actionScope = ActionScope.actionScope (Scope.eq a) := by
    cases h_a : policy.actionScope <;>
      simp only [h_a, Bool.false_eq_true] at h_action_ok
    rename_i a_scope
    cases a_scope <;>
      simp only [Bool.false_eq_true] at h_action_ok
    simp
  cases h_r : policy.resourceScope.scope <;>
    simp only [h_r, Bool.false_eq_true] at h_resource_ok
  exact DiscretionaryPolicy.discretionary h_p h_a h_r h_condition_empty

theorem discretionary_policy_structure_from_satisfaction {policy : Policy} {req : Request} {es : Entities} :
  isPolicyDiscretionary policy = true →
  satisfied policy req es = true →
  (∃ b, policy.principalScope.scope.bound = .some b ∧
    (b = req.principal ∨ (es.ancestorsOrEmpty req.principal).contains b)) ∧
  policy.actionScope = .actionScope (.eq req.action) ∧
  policy.resourceScope.scope = .eq req.resource ∧
  policy.condition = []
:= by
  intro h_discretionary h_satisfied

  have ⟨h_principal_bound, h_action_bound, h_resource_bound, h_condition⟩ :=
    discretionary_policy_has_expected_shape h_discretionary
  have h_principal_match : _ = req.principal ∨ (es.ancestorsOrEmpty req.principal).contains _ :=
    bound_authorizes_principal_ancestor h_satisfied h_principal_bound
  have h_action_match : req.action = _ :=
    eq_action_authorizes_action h_satisfied h_action_bound
  have h_resource_match : req.resource = _ :=
    eq_resource_authorizes_resource h_satisfied h_resource_bound

  and_intros
  · simp [h_principal_bound, h_principal_match]
  · rw [h_action_bound, h_action_match]
  · rw [h_resource_bound, h_resource_match]
  · exact h_condition
