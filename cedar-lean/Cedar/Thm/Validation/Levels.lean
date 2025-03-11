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
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Validator
import Cedar.Thm.Validation.RequestEntityValidation

import Cedar.Thm.Validation.Levels.Basic
import Cedar.Thm.Validation.Levels.CheckLevel
import Cedar.Thm.Validation.Levels.IfThenElse
import Cedar.Thm.Validation.Levels.GetAttr
import Cedar.Thm.Validation.Levels.HasAttr
import Cedar.Thm.Validation.Levels.UnaryApp
import Cedar.Thm.Validation.Levels.BinaryApp
import Cedar.Thm.Validation.Levels.And
import Cedar.Thm.Validation.Levels.Or
import Cedar.Thm.Validation.Levels.Record
import Cedar.Thm.Validation.Levels.Set
import Cedar.Thm.Validation.Levels.Call

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_expr {e : Expr} {n : Nat} {tx : TypedExpr} {c c₁ : Capabilities} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hc : CapabilitiesInvariant c request entities)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (ht : typeOf e c env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n) :
  evaluate e request entities = evaluate e request slice
:= by
  cases e
  case lit => simp [evaluate]
  case var v => cases v <;> simp [evaluate]
  case ite c t e =>
    have ihc := @level_based_slicing_is_sound_expr c
    have iht := @level_based_slicing_is_sound_expr t
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_if hs hc hr ht hl ihc iht ihe
  case and e₁ e₂ =>
    have ih₁ := @level_based_slicing_is_sound_expr e₁
    have ih₂ := @level_based_slicing_is_sound_expr e₂
    exact level_based_slicing_is_sound_and hs hc hr ht hl ih₁ ih₂
  case or e₁ e₂ =>
    have ih₁ := @level_based_slicing_is_sound_expr e₁
    have ih₂ := @level_based_slicing_is_sound_expr e₂
    exact level_based_slicing_is_sound_or hs hc hr ht hl ih₁ ih₂
  case unaryApp op e =>
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_unary_app hs hc hr ht hl ihe
  case binaryApp op e₁ e₂ =>
    have ihe₁ := @level_based_slicing_is_sound_expr e₁
    have ihe₂ := @level_based_slicing_is_sound_expr e₂
    exact level_based_slicing_is_sound_binary_app hs hc hr ht hl ihe₁ ihe₂
  case getAttr e _ =>
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_get_attr hs hc hr ht hl ihe
  case hasAttr e _ =>
    have ihe := @level_based_slicing_is_sound_expr e
    exact level_based_slicing_is_sound_has_attr hs hc hr ht hl ihe
  case set xs =>
    have ih : ∀ x ∈ xs, TypedAtLevelIsSound x := by
      intro x hx
      have _ : sizeOf x < sizeOf (Expr.set xs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        simp only [Expr.set.sizeOf_spec]
        omega
      exact @level_based_slicing_is_sound_expr x
    exact level_based_slicing_is_sound_set hs hc hr ht hl ih
  case call xfn xs =>
    have ih : ∀ x ∈ xs, TypedAtLevelIsSound x := by
      intro x hx
      have _ : sizeOf x < sizeOf (Expr.set xs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        simp only [Expr.set.sizeOf_spec]
        omega
      exact @level_based_slicing_is_sound_expr x
    exact level_based_slicing_is_sound_call hs hc hr ht hl ih
  case record rxs =>
    have ih : ∀ x ∈ rxs, TypedAtLevelIsSound x.snd := by
      intro x hx
      have _ : sizeOf x.snd < sizeOf (Expr.record rxs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        rw [Prod.mk.sizeOf_spec] at h₁
        simp only [Expr.record.sizeOf_spec]
        omega
      exact @level_based_slicing_is_sound_expr x.snd
    exact level_based_slicing_is_sound_record hs hc hr ht hl ih
termination_by e

theorem typecheck_policy_with_level_is_sound {p : Policy} {tx : TypedExpr} {n : Nat} {env : Environment} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (hr : RequestAndEntitiesMatchEnvironment env request entities)
  (htl : typecheckPolicyWithLevel p n env = .ok tx) :
  evaluate p.toExpr request entities = evaluate p.toExpr request slice
:= by
  simp only [typecheckPolicyWithLevel, typecheckPolicy] at htl
  split at htl <;> try contradiction
  rename_i tx' _ htx'
  cases htl₁ : tx'.typeOf ⊑ .bool .anyBool  <;> simp only [htl₁, Bool.false_eq_true, ↓reduceIte, Except.bind_err, Except.bind_ok, reduceCtorEq] at htl
  split at htl <;> simp only [reduceCtorEq, Except.ok.injEq] at htl
  subst htl
  rename_i htl'
  have subst_action_preserves_entities := (@substitute_action_preserves_evaluation · · entities)
  have subst_action_preserves_slice := (@substitute_action_preserves_evaluation · · slice)
  rw [←subst_action_preserves_slice, ←subst_action_preserves_entities, action_matches_env hr]
  rw [←level_spec] at htl'
  have hc := empty_capabilities_invariant request entities
  exact level_based_slicing_is_sound_expr hs hc hr htx' htl'

theorem typecheck_policy_at_level_with_environments_is_sound {p : Policy} {envs : List Environment} {n : Nat} {request : Request} {entities slice : Entities}
  (hs : slice = entities.sliceAtLevel request n)
  (he : ∃ env ∈ envs, RequestAndEntitiesMatchEnvironment env request entities)
  (htl : typecheckPolicyWithLevelWithEnvironments p n envs = .ok ()) :
  evaluate p.toExpr request entities = evaluate p.toExpr request slice
:= by
  simp only [typecheckPolicyWithLevelWithEnvironments] at htl
  cases htl₁: List.mapM (typecheckPolicyWithLevel p n) envs <;> simp [htl₁] at htl
  have ⟨env, ⟨he₁, hr⟩⟩ := he
  rw [List.mapM_ok_iff_forall₂] at htl₁
  replace htl₁ := List.forall₂_implies_all_left htl₁
  specialize htl₁ env he₁
  replace ⟨tx, ⟨_, htl₁⟩⟩ := htl₁
  exact typecheck_policy_with_level_is_sound hs hr htl₁

def validateWithLevel (policies : Policies) (schema : Schema) (level : Nat) : ValidationResult :=
  policies.forM (typecheckPolicyWithLevelWithEnvironments · level schema.environments)

theorem satisfied_policies_congr_evaluate {ps : Policies} {r₁ r₂ : Request} {es₁ es₂ : Entities} (effect : Effect)
  (heq : ∀ p ∈ ps, evaluate p.toExpr r₁ es₁ = evaluate p.toExpr r₂ es₂) :
  satisfiedPolicies effect ps r₁ es₁ = satisfiedPolicies effect ps r₂ es₂
:= by
  simp only [satisfiedPolicies]
  replace heq : ∀ p ∈ ps, satisfiedWithEffect effect p r₁ es₁ = satisfiedWithEffect effect p r₂ es₂ := by
    intro p hp
    specialize heq p hp
    simp only [heq, satisfiedWithEffect, satisfied]
  rw [List.filterMap_congr heq]

theorem error_policies_congr_evaluate {ps : Policies} {r₁ r₂ : Request} {es₁ es₂ : Entities}
  (heq : ∀ p ∈ ps, evaluate p.toExpr r₁ es₁ = evaluate p.toExpr r₂ es₂) :
  errorPolicies ps r₁ es₁ = errorPolicies ps r₂ es₂
:= by
  simp only [errorPolicies]
  replace heq : ∀ p ∈ ps, errored p r₁ es₁ = errored p r₂ es₂ := by
    intro p hp
    specialize heq p hp
    simp [heq, errored, hasError]
  rw [List.filterMap_congr heq]

theorem validate_with_level_is_sound {ps : Policies} {schema : Schema} {n : Nat} {request : Request} {entities slice : Entities}
  (hr : validateRequest schema request = .ok ())
  (he : validateEntities schema entities = .ok ())
  (hs : slice = entities.sliceAtLevel request n)
  (htl : validateWithLevel ps schema n = .ok ()) :
  isAuthorized request entities ps = isAuthorized request slice ps
:= by
  simp only [validateWithLevel] at htl
  replace htl := List.forM_ok_implies_all_ok _ _ htl
  have hre := request_and_entities_validate_implies_match_schema _ _ _ hr he
  clear hr he
  simp [RequestAndEntitiesMatchSchema] at hre
  have hsound : ∀ p ∈ ps, evaluate p.toExpr request entities = evaluate p.toExpr request slice := by
    intro p hp
    specialize htl p hp
    exact typecheck_policy_at_level_with_environments_is_sound hs hre htl
  simp only [isAuthorized]
  rw [
    satisfied_policies_congr_evaluate .permit hsound,
    satisfied_policies_congr_evaluate .forbid hsound,
    error_policies_congr_evaluate hsound
  ]
