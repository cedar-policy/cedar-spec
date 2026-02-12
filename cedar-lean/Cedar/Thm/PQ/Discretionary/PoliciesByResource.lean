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

import Cedar.Data.Map
import Cedar.Thm.PolicySlice
import Cedar.Thm.Authorization
import Cedar.PQ.Discretionary
import Cedar.Thm.PQ.Discretionary.DiscretionaryPolicy
import Cedar.Thm.PQ.Discretionary.PoliciesForPrincipalAndResourceType

namespace Cedar.PQ

open Cedar.Data
open Cedar.Data.Map
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

/-!
This file contains theorems about the policiesByResource function and its properties.
-/

theorem policiesByResource_wf (ps : Policies) :
  (policiesByResource ps).WellFormed
:= by
  unfold policiesByResource
  cases ps
  case nil =>
    exact Map.wf_empty
  case cons h t =>
    simp only
    split
    · apply Map.make_wf
    · exact policiesByResource_wf t

theorem policiesByResource_keys_from_input {ps : Policies} {r : EntityUID} :
  (policiesByResource ps).contains r →
  ∃ p ∈ ps, p.resourceScope.scope = .eq r
:= by
  intro h₁
  cases ps <;> unfold policiesByResource at h₁
  · simp [Map.empty, Map.contains, Map.find?, Map.kvs] at h₁
  · rename_i p ps'
    split at h₁
    · rw [Map.contains_append] at h₁
      cases h₁
      · rename_i r' h₁ h₂
        cases h₃ : r != r'
        · replace h₃ : r = r' := by
            simpa using h₃
          simp [h₃, h₁]
        · have h₄ : (policiesByResource ps').contains r := by
            rw [←Map.find_matching_iff_filter_contains (policiesByResource_wf _)] at h₂
            replace ⟨v, h₂, h₃⟩ := h₂
            simp [Map.contains, Option.isSome, h₂]
          have ih := policiesByResource_keys_from_input h₄
          simp [ih]
      · rename_i r' h₁ h₂
        replace h₂ : r' = r := by
          simpa [Map.singleton_contains] using h₂
        simp [h₁, h₂]
    · have ih := policiesByResource_keys_from_input h₁
      simp [ih]

theorem policiesByResource_then_scope_eq {ps : Policies} {r : EntityUID} {rps : Policies} {p : Policy} :
  (policiesByResource ps).find? r = some rps → p ∈ rps →
  p ∈ ps ∧ p.resourceScope.scope = .eq r
:= by
  cases ps
  · simp [policiesByResource, Map.not_find?_of_empty]
  · simp only [policiesByResource, List.mem_cons]
    split
    · intro h₁ h₄
      rename_i r' h₂
      cases h₃ : r == r'
      · replace h₃ : r ≠ r' := by simpa using h₃
        rw [Map.find?_append_left] at h₁
        · rename_i tail _
          replace h₁ : (policiesByResource tail).find? r = some rps := by
            exact Map.find?_filter_iff_find (policiesByResource_wf _)|>.mpr h₁|>.left
          have ih := policiesByResource_then_scope_eq h₁ h₄
          exact .intro (.inr ih.left) ih.right
        · rename_i h t _
          have h_mem_iff_r := Map.singleton_contains r r' (h :: ((policiesByResource t).find? r').getD [])
          grind
      · simp at h₃; subst h₃
        rw [Map.find?_append_right] at h₁
        · simp only [singleton_find?, Option.some.injEq] at h₁
          simp only [←h₁, List.mem_cons] at h₄
          cases h₄
          · rename_i h₄
            rw [←h₄] at h₂
            exact .intro (.inl h₄) h₂
          · rename_i t _ h₅
            cases h₄ : (policiesByResource t).find? r
            case none =>
              simp [h₄] at h₅
            case some =>
              rename_i ps
              replace h₅ : p ∈ ps := by simpa [h₄] using h₅
              have ih := policiesByResource_then_scope_eq h₄ h₅
              simp [ih]
        · apply Map.filter_not_contains
    · intro h₁ h₂
      have ih := policiesByResource_then_scope_eq h₁ h₂
      simp [ih]

theorem policiesByResource_subset {ps : Policies} {r : EntityUID} {rps : Policies} :
  (policiesByResource ps).find? r = some rps → rps ⊆ ps
:= by
  intro h₁ p h₂
  exact (policiesByResource_then_scope_eq h₁ h₂).left

theorem policiesByResource_contains_policy {ps : Policies} {policy : Policy} {r : EntityUID} :
  policy ∈ ps →
  policy.resourceScope.scope = .eq r →
  ∃ rps, (policiesByResource ps).find? r = some rps ∧ policy ∈ rps
:= by
  intro h₁ h₂
  cases h₁
  · rename_i t
    exists policy :: ((policiesByResource t).find? r).getD []
    simp only [policiesByResource, h₂, List.mem_cons, true_or, and_true]
    rw [Map.find?_append_right]
    · apply Map.singleton_find?
    · apply Map.filter_not_contains
  · rename_i h t ht
    have ⟨rps, ih₁, ih₂⟩ := policiesByResource_contains_policy ht h₂
    simp only [policiesByResource]
    cases h₃ : h.resourceScope.scope <;> simp only [ih₁, ih₂, Option.some.injEq, exists_eq_left']
    rename_i r'
    cases h₄ : r == r'
    · exists rps
      apply (And.intro · ih₂)
      replace h₄ : r ≠ r' := by simpa using h₄
      rw [Map.find?_append_left]
      · replace h₄ : (r != r') = true := by simp [h₄]
        exact Map.find?_filter_if_find? ih₁ h₄
      · have h_mem_if_r := Map.singleton_contains r r' (h :: ((policiesByResource t).find? r').getD [])
        grind
    · replace h₄ : r = r' := by simpa using h₄
      subst h₄
      exists h :: rps
      and_intros
      · rw [Map.find?_append_right]
        · simp [Map.singleton_find?, ih₁]
        · simp [Map.filter_not_contains]
      · simp [ih₂]

theorem policiesByResource_def {ps : Policies} {resource : EntityUID} {rps : Policies} {p : Policy} :
  (policiesByResource ps).find? resource = some rps →
  (p ∈ rps ↔ (p ∈ ps ∧ p.resourceScope.scope = .eq resource))
:= by
  intro h₁
  constructor
  · exact policiesByResource_then_scope_eq h₁
  · intro h₂
    replace ⟨rps', h₂⟩ := policiesByResource_contains_policy h₂.left h₂.right
    replace h₁ : rps' = rps := by
      simpa [h₂.left] using h₁
    rw [←h₁]
    exact h₂.right

theorem policiesByResource_sound_slice {ps rps : Policies} {req : Request} {es : Entities} :
  arePoliciesDiscretionary ps = true →
  (policiesByResource ps).find? req.resource = some rps →
  IsSoundPolicySlice req es rps ps
:= by
  intro h₁ h₂
  rw [is_sound_policy_slice_def_equiv]
  apply And.intro (policiesByResource_subset h₂)
  intro p h₃ h₄
  replace h₁ : isPolicyDiscretionary p = true := by
    simp only [arePoliciesDiscretionary, List.all_eq_true] at h₁
    exact h₁ p h₃
  replace ⟨_, _, h₁, _⟩ := discretionary_policy_has_expected_shape h₁
  rename_i r' _ _ _
  have hr : r' ≠ req.resource := by
    grind [policiesByResource_def]
  exact resource_ne_evaluates_false h₁ hr

theorem policiesByResource_policiesForPrincipalAndResourceType_composed_sound_slice {pq : ResourcesForPrincipalRequest} {r : EntityUID} {es : Entities} {ps rps : Policies} :
  r.ty = pq.resourceType →
  arePoliciesDiscretionary ps = true →
  (policiesByResource (policiesForPrincipalAndResourceType ps pq.principal (es.ancestorsOrEmpty pq.principal) pq.resourceType)).find? r = some rps →
  IsSoundPolicySlice (pq.req r) es rps ps
:= by
  intro h₁ h_discretionary₁ h₃
  have h_sound₁ := policiesForPrincipalAndResourceType_sound_slice es h₁ h_discretionary₁
  have h_discretionary₂ : arePoliciesDiscretionary ((policiesForPrincipalAndResourceType ps pq.principal (es.ancestorsOrEmpty pq.principal) pq.resourceType)) = true := by
    simp only [arePoliciesDiscretionary, List.all_eq_true] at ⊢ h_discretionary₁
    intro p hmem
    exact h_discretionary₁ p (h_sound₁.left hmem)
  have h_sound₂ := @policiesByResource_sound_slice _ _ (pq.req r) es h_discretionary₂ h₃
  exact sound_slice_transitive h_sound₁ h_sound₂

end Cedar.PQ
