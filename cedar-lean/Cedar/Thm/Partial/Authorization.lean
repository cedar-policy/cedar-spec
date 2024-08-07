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
import Cedar.Partial.Value
import Cedar.Spec.Authorizer
import Cedar.Spec.Response
import Cedar.Spec.Value
import Cedar.Thm.Authorization.Authorizer
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.EvaluatePolicy
import Cedar.Thm.Partial.Evaluation
import Cedar.Thm.Partial.Authorization.PartialOnConcrete
import Cedar.Thm.Partial.Authorization.PartialResponse

/-! This file contains toplevel theorems about Cedar's partial authorizer. -/

namespace Cedar.Thm.Partial.Authorization

open Cedar.Data
open Cedar.Partial (Residual Subsmap Unknown)
open Cedar.Spec (Policies Policy PolicyID)

/--
  Re-evaluating a residual with any substitution for the unknowns, gives the
  same result as first performing the substitution and then evaluating the
  original policy.
-/
theorem Residual.reeval_eqv_substituting_first {policy : Policy} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  Partial.evaluatePolicy policy req entities = some residual →
  residual.reEvaluateWithSubst subsmap (entities.subst subsmap) = Partial.evaluatePolicy policy req' (entities.subst subsmap)
:= by
  unfold Residual.reEvaluateWithSubst
  intro h_req h₁
  split
  · exact (EvaluatePolicy.subst_preserves_err wf_r wf_e wf_s h_req h₁).symm
  · rename_i pid eff cond
    unfold Partial.evaluatePolicy at *
    split at h₁ <;> simp at h₁
    replace ⟨h₁, h₁', h₁''⟩ := h₁ ; subst pid eff cond ; rename_i pv h₂ h₁
    cases pv <;> simp only [Partial.Value.value.injEq, imp_false, imp_self] at h₂
    case value v =>
      rw [Subst.subst_concrete_value, Partial.Evaluation.EvaluateValue.eval_spec_value v]
      rw [Partial.Evaluation.Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req h₁]
      rfl
    case residual r =>
      have h₂ := Partial.Evaluation.Reevaluation.reeval_eqv_substituting_first policy.toExpr req' subsmap wf_r wf_e wf_s h_req
      simp only at h₂
      split at h₂ <;> rename_i h₂'
      <;> simp at h₂' <;> replace ⟨h₂', h₂''⟩ := h₂'
      · -- the case where h₂' says they're both errors
        rename_i e e'
        simp only [h₁, Except.bind_ok] at h₂'
        simp only [h₂', h₂'']
      · rename_i hₑ -- the case where hₑ says they're not both errors
        subst h₂' h₂''
        simp only [h₁, Except.bind_ok] at h₂
        simp only [h₂]
        rfl

/--
  Main PE soundness theorem (for authorization):

  Partial-authorizing with any partial inputs, then performing any (valid)
  substitution for the unknowns and authorizing using the residuals, gives the
  same result as first performing the substitution and then authorizing using
  the original policies.

  Also implied by this: if a substitution is valid for the Partial.Request, then
  it is valid for `reEvaluateWithSubst`
-/
theorem authz_on_residuals_eqv_substituting_first {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  (Partial.isAuthorized req entities policies).reEvaluateWithSubst subsmap = some (Partial.isAuthorized req' (entities.subst subsmap) policies)
:= by
  intro h_req
  unfold Partial.Response.reEvaluateWithSubst Partial.isAuthorized
  simp only [Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq, Partial.Response.mk.injEq,
    and_true, exists_eq_right_right]
  rw [List.filterMap_filterMap]
  apply List.filterMap_congr _
  intro policy _
  cases h₁ : Partial.evaluatePolicy policy req entities <;> simp
  case none => exact (EvaluatePolicy.subst_preserves_none wf_r wf_e wf_s h_req h₁).symm
  case some r => exact Residual.reeval_eqv_substituting_first wf_r wf_e wf_s h_req h₁

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
  and_intros
  · exact partial_authz_decision_eqv_authz_decision_on_concrete wf h₁ h₂
  · exact overapproximate_determining_eqv_determining_on_concrete wf h₁ h₂
  · exact underapproximate_determining_eqv_determining_on_concrete wf h₁ h₂
  · exact partial_authz_errorPolicies_eqv_erroringPolicies_on_concrete wf h₁ h₂

end Cedar.Thm.Partial.Authorization
