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

theorem principal_any_resource_eq_false {pq : ResourcesForPrincipalRequest}  {schema: Schema}
  (hnp₂ : ∀ x ∈ schema.ancestorTypes pq.resourceType, euid.ty ≠ x)
  (hr : resource.ty = pq.resourceType) :
  evaluate (Var.resource.eqEntityUID euid) (pq.req resource) entities = .ok false
:= by
  suffices h : (pq.req resource).resource ≠ euid by
    simpa [Var.eqEntityUID, evaluate, apply₂] using h
  intro heuid
  simp only [←heuid] at hnp₂
  specialize hnp₂ pq.resourceType
  have hin : pq.resourceType ∈ schema.ancestorTypes pq.resourceType := by
    simp [Schema.ancestorTypes, Set.mem_union_iff_mem_or, Set.mem_singleton]
  specialize hnp₂ hin
  contradiction

theorem principal_any_resource_in_false {pq : ResourcesForPrincipalRequest}
  (hnp₂ : ∀ x ∈ schema.ancestorTypes pq.resourceType, euid.ty ≠ x)
  (hr : resource.ty = pq.resourceType)
  (hwf : InstanceOfWellFormedSchema schema (pq.req resource) entities) :
  evaluate (Var.resource.inEntityUID euid) (pq.req resource) entities = .ok false
:= by
  suffices h : resource ≠ euid ∧ (entities.ancestorsOrEmpty resource).contains euid = false by
    simpa [evaluate, Var.inEntityUID, apply₂, inₑ] using h
  and_intros
  · intro heuid
    have hty : resource.ty ≠ pq.resourceType := by
      simp only [←heuid] at hnp₂
      specialize hnp₂ pq.resourceType
      have hin : pq.resourceType ∈ schema.ancestorTypes pq.resourceType := by
        simp [Schema.ancestorTypes, Set.mem_union_iff_mem_or, Set.mem_singleton]
      exact hnp₂ hin
    contradiction
  · have hnin : euid.ty ∉ schema.ancestorTypes resource.ty := by
      simpa [←hr] using hnp₂ euid.ty
    exact instance_of_wf_schema_not_ancestor_type_implies_not_ancestor hwf hnin

theorem principal_bound_none_false {pq : ResourcesForPrincipalRequest}
  (hpp : p.principalScope.scope.bound = none)
  (hnp₁ : isUnqualifiedPolicy p = false)
  (hnp₂ : ∀ x ∈ schema.ancestorTypes pq.resourceType, isUnqualifiedPrincipalResourceTypePolicy x p = false)
  (hr : resource.ty = pq.resourceType)
  (hwf : InstanceOfWellFormedSchema schema (pq.req resource) entities) :
  evaluate p.resourceScope.toExpr (pq.req resource) entities = Except.ok (Value.prim (Prim.bool false))
:= by
  unfold isUnqualifiedPrincipalResourceTypePolicy at hnp₂
  unfold isUnqualifiedPolicy at hnp₁
  simp only [hpp] at hnp₁ hnp₂
  simp only [Scope.bound, ResourceScope.scope] at hnp₁ hnp₂
  simp only [ResourceScope.toExpr, Scope.toExpr]
  cases hpr : p.5.1
  case is _ | any =>
    simp [hpr] at hnp₁

  case eq euid =>
    simp only [hpr, BEq.rfl, Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hnp₂
    exact principal_any_resource_eq_false hnp₂ hr

  case mem euid =>
    simp only [hpr, BEq.rfl,  Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hnp₂
    exact principal_any_resource_in_false hnp₂ hr hwf

  case isMem ty euid =>
    suffices hnot_in : evaluate (Var.resource.inEntityUID euid) (pq.req resource) entities = .ok (.prim (.bool false)) from by
      have h_var_is_bool : producesBool (Var.resource.isEntityType ty) (pq.req resource) entities := by
        simp [producesBool, evaluate, Var.isEntityType, apply₁]
      exact left_bool_right_false_implies_and_false h_var_is_bool hnot_in
    simp only [BEq.rfl, hpr, Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hnp₂
    exact principal_any_resource_in_false hnp₂ hr hwf

theorem principal_any_false {pq : ResourcesForPrincipalRequest}
  (hpp : p.principalScope.scope = Scope.any)
  (hnp₁ : isUnqualifiedPolicy p = false)
  (hnp₂ : ∀ x ∈ (schema.ancestorTypes pq.resourceType).elts, isUnqualifiedPrincipalResourceTypePolicy x p = false)
  (hr : resource.ty = pq.resourceType)
  (hwf : InstanceOfWellFormedSchema schema (pq.req resource) entities) :
  evaluate p.resourceScope.toExpr (pq.req resource) entities = Except.ok (Value.prim (Prim.bool false))
:= by
  have h_bound : p.principalScope.scope.bound = none := by simp [hpp, Scope.bound]
  exact principal_bound_none_false h_bound hnp₁ hnp₂ hr hwf

theorem principal_is_ty_false {pq : ResourcesForPrincipalRequest}
  (hpp : p.principalScope.scope = Scope.is ty)
  (hnp₁ : isUnqualifiedPolicy p = false)
  (hnp₂ : ∀ x ∈ (schema.ancestorTypes pq.resourceType).elts, isUnqualifiedPrincipalResourceTypePolicy x p = false)
  (hr : resource.ty = pq.resourceType)
  (hwf : InstanceOfWellFormedSchema schema (pq.req resource) entities) :
  evaluate p.resourceScope.toExpr (pq.req resource) entities = Except.ok (Value.prim (Prim.bool false))
:= by
  have h_bound : p.principalScope.scope.bound = none := by simp [hpp, Scope.bound]
  exact principal_bound_none_false h_bound hnp₁ hnp₂ hr hwf
