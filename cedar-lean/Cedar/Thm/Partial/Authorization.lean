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
import Cedar.Thm.Partial.Authorization.PartialOnConcrete

/-! This file contains toplevel theorems about Cedar's partial authorizer. -/

namespace Cedar.Thm.Partial.Authorization

open Cedar.Data
open Cedar.Spec (Policies PolicyID)

/--
  Partial-authorizing with concrete inputs gives the same concrete decision as
  concrete-authorizing with those inputs.
-/
theorem partial_authz_decision_eqv_authz_decision_on_concrete {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {presp : Partial.Response} {resp : Spec.Response}
  (wf : req.WellFormed) :
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
  (wf : req.WellFormed) :
  (Partial.isAuthorized req entities policies).decision ≠ .unknown
:= by
  intro h₁
  have h₂ := partial_authz_decision_eqv_authz_decision_on_concrete (policies := policies) (req := req) (entities := entities) (presp := Partial.isAuthorized req entities policies) (resp := Spec.isAuthorized req entities policies) wf
  simp only [forall_const] at h₂
  cases h₃ : (Spec.isAuthorized req entities policies).decision
  <;> simp only [h₃, true_and, false_and, or_false, false_or] at h₂
  <;> simp only [h₂] at h₁

end Cedar.Thm.Partial.Authorization
