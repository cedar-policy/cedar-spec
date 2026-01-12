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

import Cedar.Thm.PolicySlice
import Cedar.Thm.PQ.Discretionary.DiscretionaryPolicy
import Cedar.Thm.Authorization

namespace Cedar.PQ

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

/-!
This file contains theorems about the policiesForPrincipalAndResourceType function and its properties.
-/

theorem policiesForPrincipalAndResourceType_scope_constraint {ps : Policies} {principal : EntityUID} {principal_groups : Set EntityUID} {rty : EntityType} {p : Policy} :
  p ∈ policiesForPrincipalAndResourceType ps principal principal_groups rty →
  (∃ e, p.resourceScope.scope = .eq e ∧ e.ty = rty) ∧
  (∃ b, p.principalScope.scope.bound = some b ∧ (b = principal ∨ principal_groups.contains b))
:= by
  intro h
  rw [policiesForPrincipalAndResourceType, List.mem_filter, Bool.and_eq_true] at h
  have ⟨_, h_resource, h_principal⟩ := h
  constructor
  · cases hr : p.resourceScope.scope
    case eq e =>
      simpa [hr] using h_resource
    all_goals
      simp [hr] at h_resource
  · cases hp : p.principalScope.scope.bound
    case none =>
      simp [hp] at h_principal
    case some b =>
      simpa [hp] using h_principal

theorem policiesForPrincipalAndResourceType_subset {ps : Policies} {principal : EntityUID} {principal_groups : Set EntityUID} {rty : EntityType} :
  policiesForPrincipalAndResourceType ps principal principal_groups rty ⊆ ps
:= by
  intro p h
  simp only [policiesForPrincipalAndResourceType, List.mem_filter] at h
  exact h.1

theorem principal_not_in_ancestors_evaluates_false {p : Policy} {pe : EntityUID} {req : Request} {es : Entities} :
  p.principalScope.scope.bound = some pe →
  pe ≠ req.principal → (es.ancestorsOrEmpty req.principal).contains pe = false →
  evaluate p.toExpr req es = .ok false
:= by
  intro h₁ h₂ h₃
  apply principal_scope_false_then_policy_false
  simp only [PrincipalScope.toExpr, Scope.toExpr]
  split <;> rename_i h₄ <;> first
  | replace h₁ : none = some pe := by
      simp [Scope.bound, PrincipalScope.scope, h₄] at h₁
    contradiction
  | rename_i euid
    replace h₁ : euid = pe := by
      simpa [Scope.bound, PrincipalScope.scope, h₄] using h₁
    subst h₁
  · suffices h : req.principal ≠ euid by
      simpa [evaluate, Var.eqEntityUID, apply₂] using h
    exact (h₂ ·.symm)
  · suffices h : req.principal ≠ euid ∧ (es.ancestorsOrEmpty req.principal).contains euid = false by
      simpa [evaluate, Var.inEntityUID, apply₂, inₑ] using h
    exact .intro (h₂ ·.symm) h₃
  · apply left_bool_right_false_implies_and_false
    · simp [Var.isEntityType, producesBool, evaluate, apply₁]
    · suffices h : req.principal ≠ euid ∧ (es.ancestorsOrEmpty req.principal).contains euid = false by
        simpa [evaluate, Var.inEntityUID, apply₂, inₑ] using h
      exact .intro (h₂ ·.symm) h₃

theorem resource_ne_evaluates_false {p : Policy} {r : EntityUID} {req : Request} {es : Entities} :
  p.resourceScope.scope = .eq r →
  r ≠ req.resource →
  evaluate p.toExpr req es = .ok false
:= by
  intro h₁ h₂
  apply resource_scope_false_then_policy_false
  simp only [ResourceScope.toExpr, Scope.toExpr]
  split
  all_goals
    rename_i h₄
    simp only [h₄, ResourceScope.scope, reduceCtorEq] at h₁
  rename_i r'
  simp only [Scope.eq.injEq] at h₁
  subst h₁
  suffices h : req.resource ≠ r' by
    simpa [evaluate, Var.eqEntityUID, apply₂] using h
  intro h
  simp [h] at h₂

theorem resource_ne_type_evaluates_false {p : Policy} {r : EntityUID} {req : Request} {es : Entities} :
  p.resourceScope.scope = .eq r →
  r.ty ≠ req.resource.ty →
  evaluate p.toExpr req es = .ok false
:= by
  intro h₁ h₂
  suffices h₂ : r ≠ req.resource by
    exact resource_ne_evaluates_false h₁ h₂
  intro h₃
  simp [h₃] at h₂

theorem policiesForPrincipalAndResourceType_sound_slice {pq : ResourcesForPrincipalRequest} {r : EntityUID} {ps : Policies} (es : Entities) :
  r.ty = pq.resourceType →
  arePoliciesDiscretionary ps = true →
  IsSoundPolicySlice (pq.req r) es (policiesForPrincipalAndResourceType ps pq.principal (es.ancestorsOrEmpty pq.principal) pq.resourceType) ps
:= by
  rw [is_sound_policy_slice_def_equiv]
  unfold IsSoundPolicySliceFalseDef
  simp only [policiesForPrincipalAndResourceType_subset, true_and]
  intro h₁ h₂ p h₃ h₄
  simp only [arePoliciesDiscretionary, List.all_eq_true] at h₂
  have ⟨hp, ha, hr, hc⟩ :=
    discretionary_policy_has_expected_shape (h₂ p h₃)
  rename_i p a r'
  cases h₅ : r'.ty == r.ty
  · replace h₅ : r'.ty ≠ (pq.req r).resource.ty := by
      simp only [h₁, beq_eq_false_iff_ne] at h₅
      simp [ResourcesForPrincipalRequest.req, h₁, h₅]
    exact resource_ne_type_evaluates_false hr h₅
  · replace ⟨h₄, h₆⟩ : p ≠ pq.principal ∧ (es.ancestorsOrEmpty pq.principal).contains p = false := by
      simpa [hr, ←h₁, hp, h₃, h₅, policiesForPrincipalAndResourceType] using h₄
    exact principal_not_in_ancestors_evaluates_false hp h₄ h₆

end Cedar.PQ
