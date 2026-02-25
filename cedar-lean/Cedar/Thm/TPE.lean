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

import Cedar.TPE
import Cedar.TPE.Authorizer
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.Conversion
import Cedar.Thm.TPE.Soundness
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.TPE.Policy
import Cedar.Thm.TPE.PolicySoundness
import Cedar.Thm.TPE.Authorizer
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.TPE.WellTypedCases
import Cedar.Thm.TPE.ErrorFree
import Cedar.Thm.Validation
import Cedar.Thm.Authorization

/-!
This file defines the main theorem of TPE soundness for authorization.

Significant lemmas proving soundness of policy and expression evaluation are in
`Cedar.Thm.TPE.Policy` and `Cedar.Thm.TPE.Soundness`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

/-- Main re-authorization soundness theorem: The result of reauthorizing a
partial authorization response with concrete request and entities is equivalent
to directly authorizing with the concrete request and entities.
-/
theorem reauthorize_is_sound
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  isValidAndConsistent schema req es preq pes = Except.ok () →
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  response.reauthorize req es = Spec.isAuthorized req es policies
:= by
  intro hv h_auth
  have ⟨_, _, h_resp⟩ := tpe_isAuthorized_forall₂ h_auth
  subst h_resp
  have equiv_satisfied := reauthorize_satisfied_policies_equiv hv h_auth
  have equiv_errors := reauthorize_error_policies_equiv hv h_auth
  simp only [isAuthorized.isAuthorizedFromResiduals] at equiv_satisfied equiv_errors
  simp [isAuthorized.isAuthorizedFromResiduals, Response.reauthorize, Spec.isAuthorized,
        equiv_satisfied .forbid, equiv_satisfied .permit, equiv_errors]

/-- Main partial authorization soundness theorem: If partial authorization
returns a decision, then concrete authorization will reach the same.
-/
theorem partial_authorize_decision_is_sound
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  {decision : Decision} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  response.decision = some decision →
  (Spec.isAuthorized req es policies).decision = decision
:= by
  intro h₁ h₂
  have ⟨rps, h₃, h₅⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₅
  simp only [isAuthorized.isAuthorizedFromResiduals]
  intro h₄
  split at h₄ <;> simp only [reduceCtorEq, Option.some.injEq] at h₄
  all_goals subst h₄
  -- Deny (satisfied forbid exists)
  · have hf : ¬ (isAuthorized.satisfiedPolicies .forbid rps).isEmpty := by grind
    exact forbid_trumps_permit _ _ _
      (satisfied_effect_if_non_empty_satisfied_policies h₁ h₂ hf)

  -- Deny (no satisfied permits)
  · have hp₁ : (isAuthorized.satisfiedPolicies .permit rps).isEmpty := by grind
    have hp₂ : (isAuthorized.residualPolicies .permit rps).isEmpty := by grind
    exact default_deny _ _ _
      (no_satisfied_effect_if_empty_satisfied_and_residual_policies h₁ h₂ hp₁ hp₂)

  -- Allow (satisfied permit exists, no satisfied/residual forbids)
  · have hf₁ : (isAuthorized.satisfiedPolicies .forbid rps).isEmpty := by grind
    have hf₂ : (isAuthorized.residualPolicies .forbid rps).isEmpty := by grind
    have hp : ¬ (isAuthorized.satisfiedPolicies .permit rps).isEmpty := by grind
    apply (allowed_iff_explicitly_permitted_and_not_denied _ _ _).mp
    exact .intro
      (satisfied_effect_if_non_empty_satisfied_policies h₁ h₂ hp)
      (no_satisfied_effect_if_empty_satisfied_and_residual_policies h₁ h₂ hf₁ hf₂)

/-- Trivial composition of the first two soundness theorems directly relating
the decision of partial authorization and subsequent re-authorization.-/
theorem partial_re_authorize_decision_eq
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  {decision : Decision} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  response.decision = some decision →
  (response.reauthorize req es).decision = decision
:= by
  intro h₁ h₂ h₃
  have h₄ := partial_authorize_decision_is_sound h₁ h₂ h₃
  have h₅ := reauthorize_is_sound h₂ h₁
  simp [h₅, h₄]

/-- All policies reported as erroring after partial authorization will appear in
the set of erroring policies after concrete authorization.  -/
theorem partial_authorize_erroring_policies_is_sound
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  (response.errorForbids ∪ response.errorPermits) ⊆ (Spec.isAuthorized req es policies).erroringPolicies
:= by
  intro h₁ h₂
  have ⟨_, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄
  have h_err_permit := partial_authorize_error_policies_is_sound .permit h₁ h₂
  have h_err_forbid := partial_authorize_error_policies_is_sound .forbid h₁ h₂
  rw [Set.union_subset]
  exact .intro h_err_forbid h_err_permit

/-- If the result of concrete authorization is `allow`, then all `permit`
policies satisfied after partial authorization are determining policies.-/
theorem partial_authorize_allow_determining_policies_is_sound
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  (Spec.isAuthorized req es policies).decision = .allow →
  response.satisfiedPermits ⊆ (Spec.isAuthorized req es policies).determiningPolicies
:= by
  intro h₁ h₂ h_allow
  replace h_allow' : (satisfiedPolicies Effect.forbid policies req es).isEmpty ∧ ¬ (satisfiedPolicies Effect.permit policies req es).isEmpty := by
    grind [Spec.isAuthorized]
  simp only [Spec.isAuthorized, h_allow', Bool.not_false, Bool.and_self, ↓reduceIte]
  exact partial_authorize_satisfied_permits_is_sound h₁ h₂

/-- If the result of concrete authorization is `deny`, then any permit policies
satisfied after partial authorization cannot be determining policies.  -/
theorem partial_authorize_satisfied_permits_not_determining_if_deny
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  (Spec.isAuthorized req es policies).decision = .deny →
  PolicyIdsUnique policies →
  (response.satisfiedPermits ∩ (Spec.isAuthorized req es policies).determiningPolicies).isEmpty
:= by
  intro h₁ h₂ h₃ h₄
  simp only [Set.empty_iff_not_exists, Set.mem_inter_iff, not_exists, not_and]
  intro pid hp₁ hp₂

  have hsatisfied : ∀ effect, (pid ∈ satisfiedPolicies effect policies req es ↔ (∃ policy, policy.id = pid ∧ policy ∈ policies ∧ policy.effect = effect ∧ satisfied policy req es)) := by
    simp only [satisfiedPolicies, satisfiedWithEffect, ←Set.make_mem]
    grind [PolicyIdsUnique]

  replace hp₂ : ∃ policy, policy.id = pid ∧ policy ∈ policies ∧ policy.effect = .forbid ∧ satisfied policy req es := by
    have hd := determiningPolicies_of req es policies
    simpa [hd, h₃, hsatisfied] using hp₂

  have hp₃ : ∃ policy, policy.id = pid ∧ policy ∈ policies ∧ policy.effect = .permit ∧ satisfied policy req es := by
    have hpermits := partial_authorize_satisfied_permits_is_sound h₁ h₂
    rw [Set.subset_def] at hpermits
    rw [←hsatisfied]
    exact hpermits pid hp₁

  grind [PolicyIdsUnique]

/-- Like `partial_authorize_allow_determining_policies_is_sound` for `forbid`
policies, but we can prove a stronger theorem because of `forbid_trumps_permit`.
Any forbid policy satisfied after partial evaluation will always be determining.-/
theorem partial_authorize_satisfied_forbid_is_determining
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  response.satisfiedForbids ⊆ (Spec.isAuthorized req es policies).determiningPolicies
:= by
  intro h₁ h₂
  have h_sub := partial_authorize_satisfied_forbids_is_sound h₁ h₂
  by_cases h_empty : response.satisfiedForbids.isEmpty
  · rw [Set.subset_def]; intro a ha
    rw [Set.empty_iff_not_exists] at h_empty
    exact absurd ⟨a, ha⟩ h_empty
  · have h_forbid_non_empty : ¬(satisfiedPolicies .forbid policies req es).isEmpty := by
      rw [Set.non_empty_iff_exists] at h_empty ⊢
      have ⟨pid, h_pid⟩ := h_empty
      exact ⟨pid, Set.subset_def.mp h_sub pid h_pid⟩
    have h_deny : (Spec.isAuthorized req es policies).decision = .deny :=
      forbid_trumps_permit _ _ _ (satisfied_iff_satisfiedPolicies_non_empty.mpr (by simpa using h_forbid_non_empty))
    have : (Spec.isAuthorized req es policies).determiningPolicies = satisfiedPolicies .forbid policies req es := by
      grind [Spec.isAuthorized]
    rw [this]; exact h_sub

/-- Like `partial_authorize_satisfied_permits_not_determining_if_deny` for
`forbid` policies, but we can prove a stronger theorem because any satisfied
forbid causes the decision to be `deny`.  If the result of concrete
authorization is `allow`, then there can be no satisfied forbid policies after
partial authorization. -/
theorem partial_authorize_no_satisfied_forbids_if_allow
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  (Spec.isAuthorized req es policies).decision = .allow →
  response.satisfiedForbids.isEmpty
:= by
  intro h₁ h₂ h₃
  rw [←allowed_iff_explicitly_permitted_and_not_denied] at h₃
  apply Set.superset_empty_subset_empty (partial_authorize_satisfied_forbids_is_sound h₁ h₂)
  simpa [explicitly_forbidden_iff_satisfying_forbid] using h₃.right

theorem partial_authorize_erroring_policies_is_complete
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  (Spec.isAuthorized req es policies).erroringPolicies ⊆ (response.errorForbids ∪ response.errorPermits ∪ response.residualPermits ∪ response.residualForbids)
:= by
  intro h₁ h₂
  have ⟨_, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄

  have h₅ : (Spec.isAuthorized req es policies).erroringPolicies = errorPolicies policies req es :=
    by grind [Spec.isAuthorized]
  simp only [errorPolicies, errored, hasError] at h₅
  simp only [h₅, isAuthorized.isAuthorizedFromResiduals, Set.subset_def, ← Set.make_mem,
    List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    forall_exists_index, and_imp]
  intro pid p hp₁ herr hpid

  replace ⟨_, herr⟩ : ∃ e, Spec.evaluate p.toExpr req es = .error e := by grind
  have h_in := errored_policy_in_error_or_residual h₁ h₂ hp₁ ⟨_, herr⟩
  simp only [isAuthorized.isAuthorizedFromResiduals] at h_in
  subst hpid
  rw [Set.mem_union_iff_mem_or] at h_in
  rw [Set.mem_union_iff_mem_or, Set.mem_union_iff_mem_or, Set.mem_union_iff_mem_or]
  rcases h_in with h_err | h_res
  · cases hp_eff : p.effect <;> simp [hp_eff] at h_err <;> simp [h_err]
  · cases hp_eff : p.effect <;> simp [hp_eff] at h_res <;> simp [h_res]

theorem partial_authorize_determining_policies_is_complete_allow
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  (Spec.isAuthorized req es policies).decision = .allow →
  (Spec.isAuthorized req es policies).determiningPolicies ⊆ (response.satisfiedPermits ∪ response.residualPermits)
:= by
  intro h₁ h₂ h_allow
  have ⟨_, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄

  have h_allow_det : (Spec.isAuthorized req es policies).determiningPolicies = satisfiedPolicies .permit policies req es := by
    grind [Spec.isAuthorized]
  rw [h_allow_det]

  simp only [satisfiedPolicies, satisfiedWithEffect, Set.subset_def, ← Set.make_mem,
    List.mem_filterMap, Bool.and_eq_true, beq_iff_eq, Option.ite_none_right_eq_some,
    Option.some.injEq, forall_exists_index, and_imp]
  intro pid p hp₁ heff hsat hpid
  subst hpid

  have h_in := satisfied_policy_in_satisfied_or_residual h₁ h₂ hp₁ (by grind [satisfied])
  simp only [heff, isAuthorized.isAuthorizedFromResiduals] at h_in
  exact h_in

theorem partial_authorize_determining_policies_is_complete_deny
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  (Spec.isAuthorized req es policies).decision = .deny →
  (Spec.isAuthorized req es policies).determiningPolicies ⊆ (response.satisfiedForbids ∪ response.residualForbids)
:= by
  intro h₁ h₂ h_deny
  have ⟨_, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄

  have h_deny_det : (Spec.isAuthorized req es policies).determiningPolicies = satisfiedPolicies .forbid policies req es := by
    grind [Spec.isAuthorized]
  rw [h_deny_det]

  simp only [satisfiedPolicies, satisfiedWithEffect, Set.subset_def, ← Set.make_mem,
    List.mem_filterMap, Bool.and_eq_true, beq_iff_eq, Option.ite_none_right_eq_some,
    Option.some.injEq, forall_exists_index, and_imp]
  intro pid p hp₁ heff hsat hpid
  subst hpid

  have h_in := satisfied_policy_in_satisfied_or_residual h₁ h₂ hp₁ (by grind [satisfied])
  simp only [heff, isAuthorized.isAuthorizedFromResiduals] at h_in
  exact h_in

theorem partial_authorize_determining_policies_is_complete
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  (Spec.isAuthorized req es policies).determiningPolicies ⊆ (response.satisfiedPermits ∪ response.satisfiedForbids ∪ response.residualPermits ∪ response.residualForbids)
:= by
  intro h₁ h₂
  cases h_dec : (Spec.isAuthorized req es policies).decision
  · have h_allow := partial_authorize_determining_policies_is_complete_allow h₁ h₂ h_dec
    grind [Set.mem_union_iff_mem_or, Set.subset_def]
  · have h_deny := partial_authorize_determining_policies_is_complete_deny h₁ h₂ h_dec
    grind [Set.mem_union_iff_mem_or, Set.subset_def]

end Cedar.Thm
