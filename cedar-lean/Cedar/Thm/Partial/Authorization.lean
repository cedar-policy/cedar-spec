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

import Cedar.Partial.Authorizer
import Cedar.Partial.Response
import Cedar.Spec.Authorizer
import Cedar.Spec.Response
import Cedar.Thm.Authorization.Authorizer
import Cedar.Thm.Partial.Authorization.PartialOnConcrete
import Cedar.Thm.Partial.Authorization.PartialResponse

/-! This file contains toplevel theorems about Cedar's partial authorizer. -/

namespace Cedar.Thm.Partial.Authorization

open Cedar.Data
open Cedar.Spec (Policies PolicyID)

/--
  Partial-authorizing with concrete inputs gives the same concrete decision as
  concrete-authorizing with those inputs.
-/
theorem partial_authz_decision_eqv_authz_decision_on_concrete {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {presp : Partial.Response} {resp : Spec.Response}
  (wf : req.context.WellFormed) :
  Spec.isAuthorized req entities policies = resp →
  Partial.isAuthorized req entities policies = presp →
  (resp.decision = .allow ∧ presp.decision = .allow) ∨ (resp.decision = .deny ∧ presp.decision = .deny)
:= by
  intro h₁ h₂
  subst h₁ h₂
  simp only [Spec.isAuthorized, Partial.Response.decision, Bool.and_eq_true, Bool.not_eq_true',
    Bool.not_eq_true, Bool.decide_eq_false, ite_eq_left_iff, Bool.not_eq_false]
  simp only [PartialOnConcrete.knownForbids_eq_forbids wf]
  simp only [PartialOnConcrete.forbids_eq_satisfied_forbids wf]
  cases h₁ : (Spec.satisfiedPolicies .forbid policies req entities).isEmpty
  <;> simp only [false_and, true_and, and_self, or_true, false_implies, forall_const, reduceIte]
  case true =>
    simp only [PartialOnConcrete.permits_eq_satisfied_permits wf]
    simp only [PartialOnConcrete.knownPermits_eq_permits wf]
    cases h₂ : (Spec.satisfiedPolicies .permit policies req entities).isEmpty
    case false => simp [h₂, PartialOnConcrete.permits_eq_satisfied_permits wf]
    case true => simp [h₁, h₂, PartialOnConcrete.permits_eq_satisfied_permits wf]

/--
  Corollary to the above: partial-authorizing with concrete inputs gives a
  concrete decision.
-/
theorem partial_authz_on_concrete_gives_concrete {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.context.WellFormed) :
  (Partial.isAuthorized req entities policies).decision ≠ .unknown
:= by
  intro h₁
  have h₂ := partial_authz_decision_eqv_authz_decision_on_concrete (policies := policies) (req := req) (entities := entities) (presp := Partial.isAuthorized req entities policies) (resp := Spec.isAuthorized req entities policies) wf
  simp only [forall_const] at h₂
  cases h₃ : (Spec.isAuthorized req entities policies).decision
  <;> simp only [h₃, true_and, false_and, or_false, false_or] at h₂
  <;> simp only [h₂] at h₁

/--
  On concrete inputs, partial authorization's `overapproximateDeterminingPolicies`
  are identical to concrete authorization's `determiningPolicies`
-/
theorem overapproximate_determining_eqv_determining_on_concrete {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {presp : Partial.Response} {resp : Spec.Response}
  (wf : req.context.WellFormed) :
  Spec.isAuthorized req entities policies = resp →
  Partial.isAuthorized req entities policies = presp →
  presp.overapproximateDeterminingPolicies = resp.determiningPolicies
:= by
  intro h₁ h₂
  subst h₁ h₂
  rw [← Set.eq_means_eqv Partial.Response.overapproximateDeterminingPolicies_wf determiningPolicies_wf]
  simp only [List.Equiv, List.subset_def]
  simp only [Partial.Response.overapproximateDeterminingPolicies, Spec.isAuthorized]
  simp only [Partial.Response.decision]
  simp only [PartialOnConcrete.knownForbids_eq_forbids wf]
  simp only [PartialOnConcrete.knownPermits_eq_permits wf]
  simp only [PartialOnConcrete.forbids_eq_satisfied_forbids wf]
  simp only [PartialOnConcrete.permits_eq_satisfied_permits wf]
  constructor <;> intro pid h₁
  <;> rw [Set.in_list_iff_in_set] at *
  <;> cases h₂ : (Spec.satisfiedPolicies .forbid policies req entities).isEmpty
  <;> simp only [not_true_eq_false, ↓reduceIte, Bool.not_eq_true, Bool.decide_eq_false,
    Bool.true_and, Bool.false_and, Bool.not_eq_true']
  <;> simp only [h₂] at h₁
  case left.false | right.false => simpa using h₁
  case left.true | right.true =>
    cases h₃ : (Spec.satisfiedPolicies .permit policies req entities).isEmpty
    <;> simpa [h₃] using h₁

/--
  On concrete inputs, partial authorization's `underapproximateDeterminingPolicies`
  are identical to concrete authorization's `determiningPolicies`
-/
theorem underapproximate_determining_eqv_determining_on_concrete {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {presp : Partial.Response} {resp : Spec.Response}
  (wf : req.context.WellFormed) :
  Spec.isAuthorized req entities policies = resp →
  Partial.isAuthorized req entities policies = presp →
  presp.underapproximateDeterminingPolicies = resp.determiningPolicies
:= by
  intro h₁ h₂
  subst h₁ h₂
  rw [← Set.eq_means_eqv Partial.Response.underapproximateDeterminingPolicies_wf determiningPolicies_wf]
  simp only [List.Equiv, List.subset_def]
  simp only [Partial.Response.underapproximateDeterminingPolicies, Spec.isAuthorized]
  simp only [Partial.Response.decision]
  simp only [PartialOnConcrete.knownForbids_eq_forbids wf]
  simp only [PartialOnConcrete.knownPermits_eq_permits wf]
  simp only [PartialOnConcrete.forbids_eq_satisfied_forbids wf]
  simp only [PartialOnConcrete.permits_eq_satisfied_permits wf]
  constructor <;> intro pid h₁
  <;> rw [Set.in_list_iff_in_set] at *
  <;> cases h₂ : (Spec.satisfiedPolicies .forbid policies req entities).isEmpty
  <;> simp only [not_true_eq_false, ↓reduceIte, Bool.not_eq_true, Bool.decide_eq_false,
    Bool.true_and, Bool.false_and, Bool.not_eq_true']
  <;> simp only [h₂] at h₁
  case left.false | right.false => simpa using h₁
  case left.true | right.true =>
    cases h₃ : (Spec.satisfiedPolicies .permit policies req entities).isEmpty
    <;> simpa [h₃] using h₁

/--
  On concrete inputs, partial authorization's `errorPolicies` are the same
  policies as concrete authorization's `erroringPolicies`
-/
theorem partial_authz_errorPolicies_eqv_erroringPolicies_on_concrete {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {presp : Partial.Response} {resp : Spec.Response}
  (wf : req.context.WellFormed) :
  Spec.isAuthorized req entities policies = resp →
  Partial.isAuthorized req entities policies = presp →
  presp.errorPolicies = resp.erroringPolicies
:= by
  intro h₁ h₂
  subst h₁ h₂
  simp only [Spec.isAuthorized, Bool.and_eq_true, Bool.not_eq_true']
  cases (Spec.satisfiedPolicies .forbid policies req entities).isEmpty <;>
  cases (Spec.satisfiedPolicies .permit policies req entities).isEmpty <;>
  simp only [and_true, and_false, ite_true, ite_false] <;>
  exact PartialOnConcrete.errorPolicies_eq_errorPolicies wf

/--
  Partial-authorizing with concrete inputs gives the same concrete outputs as
  concrete-authorizing with those inputs.
-/
theorem partial_authz_eqv_authz_on_concrete {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {presp : Partial.Response} {resp : Spec.Response}
  (wf : req.context.WellFormed) : -- interestingly, this theorem only requires that the context is a WellFormed map, not that the entities are well-formed or that the context values are well-formed
  Spec.isAuthorized req entities policies = resp →
  Partial.isAuthorized req entities policies = presp →
  (resp.decision = .allow ∧ presp.decision = .allow ∨ resp.decision = .deny ∧ presp.decision = .deny) ∧
  presp.overapproximateDeterminingPolicies = resp.determiningPolicies ∧
  presp.underapproximateDeterminingPolicies = resp.determiningPolicies ∧
  presp.errorPolicies = resp.erroringPolicies
:= by
  intro h₁ h₂
  apply And.intro (partial_authz_decision_eqv_authz_decision_on_concrete wf h₁ h₂)
  apply And.intro (overapproximate_determining_eqv_determining_on_concrete wf h₁ h₂)
  apply And.intro (underapproximate_determining_eqv_determining_on_concrete wf h₁ h₂)
  exact partial_authz_errorPolicies_eqv_erroringPolicies_on_concrete wf h₁ h₂

end Cedar.Thm.Partial.Authorization
