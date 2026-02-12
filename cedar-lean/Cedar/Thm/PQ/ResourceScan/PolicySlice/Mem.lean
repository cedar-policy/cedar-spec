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
import Cedar.Thm.Validation

import Cedar.PQ.ResourcesForPrincipal
import Cedar.PQ.ResourceScan.PolicySlice

namespace Cedar.PQ

open Cedar.Data
open Cedar.Spec
open Cedar.Thm
open Cedar.Validation

theorem principal_mem_then_resource_eq_false {entities : Entities} {euid' : EntityUID} :
  (euid = principal → euid'.ty ≠ resource.ty) →
  (euid ∈ entities.ancestorsOrEmpty principal → euid'.ty ≠ resource.ty) →
  principal = euid ∨ (entities.ancestorsOrEmpty principal).contains euid →
  resource ≠ euid'
:= by
  intro hnp₄ hnp₅ heuid₁
  suffices hty : euid'.ty ≠ resource.ty from by
    intro heuid
    rw [heuid] at hty
    contradiction
  cases heuid₁
  · rename_i heuid
    symm at heuid
    exact hnp₄ heuid
  · rename_i hin
    simp only [Set.contains_prop_bool_equiv] at hin
    exact hnp₅ hin

theorem not_mem_then_resource_is_mem_false :
  req.resource ≠ euid →
  (entities.ancestorsOrEmpty req.resource).contains euid = false →
  evaluate ((Var.resource.isEntityType ty).and (Var.resource.inEntityUID euid)) req entities = .ok false
:= by
  intros hneq hnot_in
  cases hty : ty == req.resource.ty
  · simp [Var.isEntityType, evaluate, apply₁, hty, Result.as, Coe.coe, Value.asBool]
  · simp at hty
    subst hty
    have hr_is_true : evaluate (Var.resource.isEntityType req.resource.ty) req entities = .ok true := by
      simp [evaluate, Var.isEntityType, apply₁]
    have hr_in_bool : producesBool (Var.resource.inEntityUID euid) req entities := by
      simp [producesBool, Var.inEntityUID, evaluate, apply₂]
    simp only [producesBool] at hr_in_bool
    split at hr_in_bool <;> try contradiction
    clear hr_in_bool ; rename_i b hr_in_bool
    have his_elim := and_bool_operands_is_boolean_and hr_is_true hr_in_bool
    simp only [Bool.true_and] at his_elim
    rw [his_elim, ←hr_in_bool]
    simp [evaluate, Var.inEntityUID, apply₂, inₑ, hnot_in, hneq]

theorem principal_bound_false {pq : ResourcesForPrincipalRequest}
  (hr : resource.ty = pq.resourceType)
  (hwf : InstanceOfWellFormedSchema schema (pq.req resource) entities)
  (heuid₁ : pq.principal = euid ∨ (entities.ancestorsOrEmpty pq.principal).contains euid = true)
  (hpp : p.principalScope.scope.bound = .some euid)
  (hnp₃ : isPrincipalPolicyUnqualifiedResource pq.principal p = false)
  (hnp₄ : ∀ x ∈ (schema.ancestorTypes pq.resourceType).elts, isPrincipalPolicyForResourceType pq.principal x p = false)
  (hnp₅ : ∀ x ∈ (schema.ancestorTypes pq.resourceType).elts, ∀ x₁ ∈ (entities.ancestorsOrEmpty pq.principal).elts, isPrincipalParentPolicy x₁ x p = false) :
  evaluate p.resourceScope.toExpr (pq.req resource) entities = Except.ok (Value.prim (Prim.bool false))
:= by
  simp only [isPrincipalPolicyUnqualifiedResource] at hnp₃
  simp only [isPrincipalPolicyForResourceType] at hnp₄
  simp only [isPrincipalParentPolicy] at hnp₅
  simp only [hpp, Option.some_beq_some, Option.beq_none, Bool.and_eq_false_imp, beq_iff_eq, Option.isNone_eq_false_iff] at hnp₃ hnp₄ hnp₅
  simp only [Scope.bound] at hnp₃ hnp₄ hnp₅
  simp only [ResourceScope.toExpr, Scope.toExpr]
  cases hpr : p.5.1
  case any | is =>
    simp only [ResourceScope.scope, hpr, Option.isSome_none, Bool.false_eq_true, imp_false, Bool.true_eq_false] at hnp₃ hnp₅
    cases heuid₁
    · rename_i heuid
      subst heuid
      simp at hnp₃
    · rename_i heuid₁
      have : euid ≠ euid := by
        simp only [Set.contains, List.contains_eq_mem, decide_eq_true_eq] at heuid₁
        simp only [Schema.ancestorTypes, Set.in_list_iff_in_set, Set.mem_union_iff_mem_or, Set.mem_singleton_iff_eq, forall_eq_or_imp] at hnp₅
        exact hnp₅.left euid heuid₁
      contradiction

  case eq euid' =>
    simp only [ResourceScope.scope, hpr, beq_eq_false_iff_ne, ne_eq] at hnp₄ hnp₅
    suffices h : (pq.req resource).resource ≠ euid' by
      simpa [Var.eqEntityUID, evaluate, apply₂] using h
    cases heuid₁
    · intro heuid'
      subst euid'
      rename_i heuid
      subst euid
      simp only [Schema.ancestorTypes, Set.in_list_iff_in_set, Set.mem_union_iff_mem_or, Set.mem_singleton_iff_eq, forall_const, forall_eq_or_imp] at hnp₄
      simp [hr, ResourcesForPrincipalRequest.req] at hnp₄
    · rename_i heuid₁
      simp only [Set.contains, List.elem_eq_contains, List.contains_eq_mem, decide_eq_true_eq] at heuid₁
      intro heuid'
      subst heuid'
      simp only [Schema.ancestorTypes, Set.in_list_iff_in_set, Set.mem_union_iff_mem_or, Set.mem_singleton_iff_eq, forall_eq_or_imp] at hnp₅
      replace ⟨hnp₅, hnp₆⟩ := hnp₅
      specialize hnp₅ euid heuid₁
      simp [hr, ResourcesForPrincipalRequest.req] at hnp₅

  case isMem _ euid' | mem euid' =>
    simp only [hpr, ResourceScope.scope] at hnp₄ hnp₅
    suffices hnot_in : resource ≠ euid' ∧ (entities.ancestorsOrEmpty resource).contains euid' = false from by
      first
      | exact not_mem_then_resource_is_mem_false hnot_in.left hnot_in.right
      | simp [ResourcesForPrincipalRequest.req, evaluate, Var.inEntityUID, apply₂, inₑ, hnot_in]
    rw [←hr] at hnp₄ hnp₅
    and_intros
    · simp [Schema.ancestorTypes, Set.mem_union_iff_mem_or, Set.mem_singleton_iff_eq, Set.in_list_iff_in_set] at hnp₅ hnp₄
      replace ⟨hnp₅, hnp₆⟩ := hnp₅
      replace ⟨hnp₄, hnp₇⟩ := hnp₄
      exact principal_mem_then_resource_eq_false hnp₄ (hnp₅ euid · (by rfl)) heuid₁
    · have h₁ : euid'.ty ∉ schema.ancestorTypes resource.ty := by
        specialize hnp₅ euid'.ty
        specialize hnp₄ euid'.ty
        cases heuid₁ <;> rename_i heuid₁
        · simpa [heuid₁] using hnp₄
        · simp only [Set.contains_prop_bool_equiv] at heuid₁
          replace hnp₅ := (hnp₅ · euid heuid₁)
          simpa using hnp₅
      exact instance_of_wf_schema_not_ancestor_type_implies_not_ancestor hwf h₁

theorem principal_mem_false {pq : ResourcesForPrincipalRequest}
  (hr : resource.ty = pq.resourceType)
  (hwf : InstanceOfWellFormedSchema schema (pq.req resource) entities)
  (heuid₁ : pq.principal = euid ∨ (entities.ancestorsOrEmpty pq.principal).contains euid = true)
  (hpp : p.principalScope.scope = .mem euid)
  (hnp₃ : isPrincipalPolicyUnqualifiedResource pq.principal p = false)
  (hnp₄ : ∀ x ∈ (schema.ancestorTypes pq.resourceType).elts, isPrincipalPolicyForResourceType pq.principal x p = false)
  (hnp₅ : ∀ x ∈ (schema.ancestorTypes pq.resourceType).elts, ∀ x₁ ∈ (entities.ancestorsOrEmpty pq.principal).elts, isPrincipalParentPolicy x₁ x p = false) :
  evaluate p.resourceScope.toExpr (pq.req resource) entities = Except.ok (Value.prim (Prim.bool false))
:= by
  replace hpp : p.principalScope.scope.bound = .some euid := by
    simp [Scope.bound, hpp]
  exact principal_bound_false hr hwf heuid₁ hpp hnp₃ hnp₄ hnp₅

theorem principal_is_ty_mem_false {pq : ResourcesForPrincipalRequest}
  (hr : resource.ty = pq.resourceType)
  (hwf : InstanceOfWellFormedSchema schema (pq.req resource) entities)
  (heuid₁ : pq.principal = euid ∨ (entities.ancestorsOrEmpty pq.principal).contains euid = true)
  (hpp : p.principalScope.scope = .isMem ty euid)
  (hnp₃ : isPrincipalPolicyUnqualifiedResource pq.principal p = false)
  (hnp₄ : ∀ x ∈ (schema.ancestorTypes pq.resourceType).elts, isPrincipalPolicyForResourceType pq.principal x p = false)
  (hnp₅ : ∀ x ∈ (schema.ancestorTypes pq.resourceType).elts, ∀ x₁ ∈ (entities.ancestorsOrEmpty pq.principal).elts, isPrincipalParentPolicy x₁ x p = false) :
  evaluate p.resourceScope.toExpr (pq.req resource) entities = Except.ok (Value.prim (Prim.bool false))
:= by
  replace hpp : p.principalScope.scope.bound = .some euid := by
    simp [Scope.bound, hpp]
  exact principal_bound_false hr hwf heuid₁ hpp hnp₃ hnp₄ hnp₅
