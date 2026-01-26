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

import Cedar.Data
import Cedar.Thm.PolicySlice

import Cedar.PQ.ResourceScan.PolicySlice
import Cedar.Thm.PQ.ResourceScan.PolicySlice.Any
import Cedar.Thm.PQ.ResourceScan.PolicySlice.Mem

namespace Cedar.PQ

open Cedar.Data
open Cedar.Spec
open Cedar.Thm
open Cedar.Validation

theorem subset_excludes_false_scope_implies_sound_slice
    (h_sub : slice ⊆ policies)
    (hpr_false : ∀ p ∈ policies, p ∉ slice →
      evaluate p.principalScope.toExpr req entities = .ok false ∨
      evaluate p.resourceScope.toExpr req entities = .ok false) :
    IsSoundPolicySlice req entities slice policies
:= by
  rw [is_sound_policy_slice_def_equiv]
  apply And.intro h_sub
  intro p hp hnp
  specialize hpr_false p hp hnp
  have h_false : evaluate p.toExpr req entities = .ok false := by
    cases hpr_false
    case inl hp_false => exact principal_scope_false_then_policy_false hp_false
    case inr hr_false => exact resource_scope_false_then_policy_false hr_false
  exact h_false

theorem policy_slice_subset :
∀ (pq : ResourcesForPrincipalRequest) policies entities schema,
  policySliceByResourceType pq policies entities schema ⊆ policies
:= by
  intro pq ps entities schema
  simp only [policySliceByResourceType, List.mem_filter, List.subset_def]
  intro _ h
  exact h.left

theorem policy_slice_sound : ∀ {pq ps es schema r},
    r.ty = pq.resourceType →
    InstanceOfWellFormedSchema schema (pq.req r) es →
    IsSoundPolicySlice (pq.req r) es (policySliceByResourceType pq ps es schema) ps := by
  intro pq policies entities schema resource hr hwf
  apply subset_excludes_false_scope_implies_sound_slice (policy_slice_subset pq policies entities schema)
  simp only [policySliceByResourceType, List.mem_filter, Bool.or_eq_true, not_and, not_or, Bool.not_eq_true]
  intro p hp hnp
  specialize hnp hp
  simp only [Set.any, List.any_eq_false, Bool.not_eq_true, List.any_eq_true, not_exists, not_and] at hnp
  have ⟨⟨⟨⟨hnp₁, hnp₂⟩, hnp₃⟩, hnp₄⟩, hnp₅⟩ := hnp ; clear hnp

  cases hpp : p.3.1
  case any =>
    right
    exact principal_any_false hpp hnp₁ hnp₂ hr hwf

  case is ety =>
    right
    exact principal_is_ty_false hpp hnp₁ hnp₂ hr hwf

  case eq euid =>
    cases heuid : decide (euid = pq.principal)
    · left
      suffices hp_neq : pq.principal ≠ euid from by
        simp [hpp, ResourcesForPrincipalRequest.req, Scope.toExpr, PrincipalScope.toExpr, Var.eqEntityUID, evaluate, apply₂, hp_neq]
      intro heuid'
      simp [←heuid'] at heuid
    · right
      simp only [decide_eq_true_eq] at heuid
      subst euid
      replace hpp : p.principalScope.scope.bound = .some pq.principal := by
        simp only [Scope.bound, PrincipalScope.scope, hpp]
      exact principal_bound_false hr hwf (Or.intro_left _ (Eq.refl _)) hpp hnp₃ hnp₄ hnp₅

  case mem euid =>
    cases heuid₁ : pq.principal == euid || (entities.ancestorsOrEmpty pq.principal).contains euid <;> simp at heuid₁
    · left
      simp [PrincipalScope.toExpr, ResourcesForPrincipalRequest.req, Scope.toExpr, Var.inEntityUID, evaluate, apply₂, inₑ, heuid₁, hpp]
    · right
      exact principal_mem_false hr hwf heuid₁ hpp hnp₃ hnp₄ hnp₅

  case isMem ety euid =>
    cases heuid₁ : pq.principal == euid || (entities.ancestorsOrEmpty pq.principal).contains euid <;> simp at heuid₁
    · left
      suffices hp_in_false : evaluate (Var.principal.inEntityUID euid) (pq.req resource) entities = .ok false from by
        have ⟨_, hp_is_bool⟩  : ∃ (b : Bool), evaluate (Var.principal.isEntityType ety) (pq.req resource)  entities = .ok b := by
          simp [evaluate, Var.isEntityType, apply₁]
        have hp_false := and_bool_operands_is_boolean_and hp_is_bool hp_in_false
        simp only [Bool.and_false] at hp_false
        simp only [hpp, PrincipalScope.toExpr]
        exact hp_false
      simp [ResourcesForPrincipalRequest.req, Var.inEntityUID, evaluate, apply₂,  inₑ, heuid₁]
    · right
      exact principal_is_ty_mem_false hr hwf heuid₁ hpp hnp₃ hnp₄ hnp₅

theorem isAuthorized_eq_for_policy_slice {pq : ResourcesForPrincipalRequest} (entities : Entities) (policies : Policies) (schema : Schema) :
  resource.ty = pq.resourceType →
  InstanceOfWellFormedSchema schema (pq.req resource) entities →
  isAuthorized (pq.req resource) entities (policySliceByResourceType pq policies entities schema)  = isAuthorized (pq.req resource) entities policies
:= (isAuthorized_eq_for_sound_policy_slice _ _ _ _ $ policy_slice_sound · ·)
