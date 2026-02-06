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
import Cedar.Thm.Authorization

import Cedar.PQ.ResourceScan.ResourceCandidates

namespace Cedar.PQ

open Cedar.Data
open Cedar.Spec
open Cedar.Thm
open Cedar.Validation

theorem not_descendant_implies_not_ancestor {es : Entities} :
  ¬ (es.descendantsOrEmpty e₀).contains e₁ →
  ¬ (es.ancestorsOrEmpty e₁).contains e₀
:= by
  simp only [Entities.descendantsOrEmpty, Entities.ancestorsOrEmpty]
  intro h
  cases he₁ : es.find? e₁ <;> simp
  · simp [Set.empty, Set.contains, Set.elts]
  · rename_i ed
    suffices h₁ : ¬e₀ ∈ ed.ancestors from by
      simpa [Set.contains] using h₁
    replace h : ∀ ed, (e₁, ed) ∈ es.kvs → e₀ ∉ ed.ancestors := by
      simpa [Set.contains, Set.elts] using h
    exact h ed (Map.find?_mem_toList he₁)

theorem descendant_implies_ancestor {es : Entities} :
  es.WellFormed →
  (es.descendantsOrEmpty e₀).contains e₁ →
  (es.ancestorsOrEmpty e₁).contains e₀
:= by
  intro hwf
  simp only [Entities.descendantsOrEmpty, Entities.ancestorsOrEmpty]
  cases he₁ : es.find? e₁ <;> simp
  · replace he₁ := Map.find?_none_all_absent he₁
    simp [Set.empty, Set.contains, Set.elts, he₁]
  · rename_i ed
    suffices h :  ∀ ed', (e₁, ed') ∈ es.kvs → e₀ ∈ ed'.ancestors → e₀ ∈ ed.ancestors from by
      simpa [Set.contains, Set.elts] using h
    intro ed' he₁'
    have hed : ed' = ed := by
      replace he₁' := Map.mem_toList_find? hwf he₁'
      simpa [he₁'] using he₁
    rw [←hed]
    exact id

theorem descendant_eq_ancestor {es : Entities} :
  es.WellFormed →
  (es.descendantsOrEmpty e₀).contains e₁ = (es.ancestorsOrEmpty e₁).contains e₀
:= by
  intro hwf
  cases h₁ : (es.descendantsOrEmpty e₀).contains e₁
  · have h₂ := @not_descendant_implies_not_ancestor e₀ e₁ es
    simp only [Bool.not_eq_true] at h₂
    exact (h₂ h₁).symm
  · exact (descendant_implies_ancestor hwf h₁).symm

theorem resource_candidates_for_policy_complete {p : Policy}
  (hc : resource_candidates_for_policy p es = some candidates)
  (hr : req.resource ∉ candidates)
  (hp : p.effect = .permit) :
  evaluate p.toExpr req es = .ok false
:= by
  suffices hr_false : evaluate p.resourceScope.toExpr req es = .ok false from
    resource_scope_false_then_policy_false hr_false
  simp only [resource_candidates_for_policy, hp] at hc
  split at hc <;> try contradiction
  all_goals
    simp only [Option.some.injEq] at hc
    rw [←hc] at hr ; clear hc
    rename_i euid hs
    have hneq : req.resource ≠ euid := by
      intro heq
      simp [heq] at hr
    simp only [ResourceScope.scope] at hs
    simp only [ResourceScope.toExpr, Scope.toExpr, hs]
  · simp [Var.eqEntityUID, evaluate, apply₂, hneq]
  · rename_i ty
    have hnin : ¬ (es.descendantsOrEmpty euid).contains req.resource := by
      rw [Bool.not_eq_true, Set.not_contains_prop_bool_equiv]
      simp only [List.mem_cons, not_or] at hr
      exact hr.right
    replace hnin := not_descendant_implies_not_ancestor hnin
    cases his : ty == req.resource.ty <;>
      simp [Var.inEntityUID, Var.isEntityType, Result.as, Coe.coe, Value.asBool, evaluate, apply₁, apply₂, inₑ,  his, hnin, hneq]
  · have hnin : ¬ (es.descendantsOrEmpty euid).contains req.resource := by
      rw [Bool.not_eq_true, Set.not_contains_prop_bool_equiv]
      simp only [List.mem_cons, not_or] at hr
      exact hr.right
    replace hnin := not_descendant_implies_not_ancestor hnin
    simp [Var.inEntityUID, evaluate, apply₂, inₑ, hnin, hneq]

theorem resource_candidates_policies_complete
  (hc : resource_candidates_for_policies ps es = some rs)
  (hr : req.resource ∉ rs) :
  (isAuthorized req es ps).decision = .deny
:= by
  suffices h_not_permitted : ¬ IsExplicitlyPermitted req es ps from
    default_deny _ _ _ h_not_permitted

  simp only [resource_candidates_for_policies, Option.map_eq_some_iff] at hc
  replace ⟨ _, hc, _ ⟩ := hc
  subst rs

  simp only [IsExplicitlyPermitted, HasSatisfiedEffect, not_exists, not_and]
  intro p hp he

  have ⟨ p_candidates, hc₁, hc₂ ⟩ := List.mapM_some_implies_all_some hc p hp
  simp only [List.mem_flatten, not_exists, not_and] at hr

  have h_false := resource_candidates_for_policy_complete hc₂ (hr p_candidates hc₁) he
  simp [satisfied, h_false]

theorem resource_candidates_complete'
  (hr : resource ∉ resource_candidates pq ps es)
  (he : resource ∈ es)
  (hty : resource.ty = pq.resourceType) :
  (isAuthorized (pq.req resource) es ps).decision = .deny
:= by
  simp only [resource_candidates, Set.mem_filter] at hr
  cases hr₁ : resource_candidates_for_policies ps es <;> simp only [hr₁] at hr
  case some rs =>
    suffices hr₂ : resource ∉ rs from by
      apply resource_candidates_policies_complete hr₁
      simp only [ResourcesForPrincipalRequest.req]
      exact hr₂
    replace hr : resource ∈ Map.keys es → resource ∉ rs := by
      simpa [hty] using hr
    exact hr he
  case none =>
    replace hr : resource.ty ≠ pq.resourceType := by
      simpa [he, Map.in_keys_iff_in_map] using hr
    simp [hr] at hty

theorem resource_candidates_complete : ∀ {pq ps es resource},
    resource.ty = pq.resourceType →
    resource ∈ es →
    (isAuthorized (pq.req resource) es ps).decision = .allow  →
    resource ∈ resource_candidates pq ps es := by
  intro pq es ps r h₁ h₂ h₃
  have h₄ := mt (@resource_candidates_complete' pq es ps r)
  simp only [not_imp, Classical.not_not, and_imp] at h₄
  apply h₄ h₂ h₁
  simp [h₃]

theorem resource_candidates_sound : ∀ {pq ps es resource},
    resource ∈ resource_candidates pq ps es → (resource.ty = pq.resourceType ∧ resource ∈ es) := by
  intro pq ps es r hr
  simp only [resource_candidates, Set.mem_filter, Bool.and_eq_true, beq_iff_eq] at hr
  exact .intro hr.right.left hr.left
