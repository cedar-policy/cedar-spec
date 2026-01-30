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
import Cedar.Thm.TPE.Authorizer
import Cedar.Thm.TPE.WellTyped
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

  simp only [TPE.isAuthorized] at h_auth
  cases h_auth₁ : List.mapM (λ p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;> simp [h_auth₁] at h_auth
  rename_i residuals
  subst h_auth

  rw [List.mapM_ok_iff_forall₂] at h_auth₁
  have equiv_satisfied := reauthorize_satisfied_policies_equiv hv h_auth₁
  have equiv_errors := reauthorize_error_policies_equiv hv h_auth₁
  simp [TPE.isAuthorized.isAuthorizedFromResiduals, Response.reauthorize, Spec.isAuthorized,
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
  simp only [TPE.isAuthorized] at h₁

  cases h₃ : List.mapM (λ p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;>
    simp [h₃] at h₁
  rename_i rps

  rw [List.mapM_ok_iff_forall₂] at h₃
  simp [isAuthorized.isAuthorizedFromResiduals] at h₁
  split at h₁ <;>
    simp only [← h₁, reduceCtorEq, false_implies]
  all_goals
    intro h₅
    simp only [Option.some.injEq] at h₅
    subst h₅
  -- Deny (satisfied forbid exists)
  · have hf : ¬ (isAuthorized.satisfiedPolicies .forbid rps).isEmpty := by grind
    have h_forbid : HasSatisfiedEffect Effect.forbid req es policies :=
      satisfied_effect_if_non_empty_satisfied_policies h₂ h₃ hf

    apply forbid_trumps_permit
    unfold IsExplicitlyForbidden
    exact h_forbid

  -- Deny (no satisfied permits)
  · have hp₁ : (isAuthorized.satisfiedPolicies .permit rps).isEmpty := by grind
    have hp₂ : (isAuthorized.residualPolicies .permit rps).isEmpty := by grind
    have h_not_permit : ¬HasSatisfiedEffect Effect.permit req es policies :=
      no_satisfied_effect_if_empty_satisfied_and_residual_policies h₂ h₃ hp₁ hp₂

    apply default_deny
    unfold IsExplicitlyPermitted
    exact h_not_permit

  -- Allow (satisfied permit exists, no satisfied/residual forbids)
  · have hf₁ : (isAuthorized.satisfiedPolicies .forbid rps).isEmpty := by grind
    have hf₂ : (isAuthorized.residualPolicies .forbid rps).isEmpty := by grind
    have h_not_forbid : ¬HasSatisfiedEffect Effect.forbid req es policies :=
      no_satisfied_effect_if_empty_satisfied_and_residual_policies h₂ h₃ hf₁ hf₂

    have hp : ¬ (isAuthorized.satisfiedPolicies .permit rps).isEmpty := by grind
    have h_permit : HasSatisfiedEffect Effect.permit req es policies :=
      satisfied_effect_if_non_empty_satisfied_policies h₂ h₃ hp

    apply (allowed_iff_explicitly_permitted_and_not_denied _ _ _).mp
    unfold IsExplicitlyPermitted IsExplicitlyForbidden
    exact .intro h_permit h_not_forbid

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
  simp only [TPE.isAuthorized] at h₁

  cases h₃ : List.mapM (λ p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;>
    simp [h₃] at h₁
  rename_i rps
  rw [List.mapM_ok_iff_forall₂] at h₃
  subst response

  have h_err_permit := partial_authorize_error_policies_is_sound .permit h₃ h₂
  have h_err_forbid := partial_authorize_error_policies_is_sound .forbid h₃ h₂
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
  simp only [TPE.isAuthorized] at h₁

  replace h_allow' : (satisfiedPolicies Effect.forbid policies req es).isEmpty ∧ ¬ (satisfiedPolicies Effect.permit policies req es).isEmpty := by
    grind [Spec.isAuthorized]
  simp only [Spec.isAuthorized, h_allow', Bool.not_false, Bool.and_self, ↓reduceIte]

  cases h₃ : List.mapM (λ p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;>
    simp [h₃] at h₁
  rename_i rps
  rw [List.mapM_ok_iff_forall₂] at h₃
  subst response

  simp [isAuthorized.isAuthorizedFromResiduals, isAuthorized.satisfiedPolicies,
    satisfiedPolicies, satisfiedWithEffect, satisfied, Bool.and_eq_true,
    decide_eq_true_eq, Set.subset_def, ← Set.make_mem, List.mem_filterMap,
    ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied, Residual.isTrue,
    Option.ite_none_right_eq_some, forall_exists_index, and_imp]
  intro pid rp hrp heff hs hpid
  split at hs <;> try contradiction

  have ⟨p, hp₁, hp₂⟩ := List.forall₂_implies_all_right h₃ rp hrp
  cases hp₃ : evaluatePolicy schema p preq pes <;>
   simp only [hp₃, Except.map_error, Except.map_ok, reduceCtorEq, Except.ok.injEq] at hp₂

  exists p
  and_intros
  · exact hp₁
  · rw [←hp₂] at heff
    exact heff
  · rename_i ty hr r
    replace hr : r = .val (.prim (.bool true)) ty := by grind
    have ha := partial_evaluate_policy_is_sound hp₃ h₂
    simp only [hr, Residual.evaluate] at ha
    exact to_option_right_ok' ha
  · rw [←hp₂] at hpid
    exact hpid

/-- We can prove a stronger theorem for `satisfiedForbid`:
because `forbid_trumps_permit` any satisfied forbid policy will always be determining.-/
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
  simp only [TPE.isAuthorized] at h₁

  cases h₃ : List.mapM (λ p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;>
    simp only [bind_pure_comp, h₃, Except.map_ok, Except.map_error, Except.ok.injEq, reduceCtorEq] at h₁
  rename_i rps
  rw [List.mapM_ok_iff_forall₂] at h₃
  subst response

  simp only [isAuthorized.isAuthorizedFromResiduals, isAuthorized.satisfiedPolicies, Set.subset_def,
    ← Set.make_mem, List.mem_filterMap, ResidualPolicy.satisfiedWithEffect,
    ResidualPolicy.satisfied, Residual.isTrue, Bool.and_eq_true, beq_iff_eq,
    Option.ite_none_right_eq_some, Option.some.injEq, forall_exists_index, and_imp]
  intro pid rp hrp heff hs hpid
  split at hs <;> try contradiction

  have ⟨p, hp₁, hp₂⟩ := List.forall₂_implies_all_right h₃ rp hrp
  cases hp₃ : evaluatePolicy schema p preq pes <;>
    simp only [hp₃, Except.map_error, Except.map_ok, reduceCtorEq, Except.ok.injEq] at hp₂
  rename_i ty hr r

  have ha : Spec.evaluate p.toExpr req es = .ok (.prim (.bool true)) := by
    replace hr : r = .val (.prim (.bool true)) ty := by grind
    have ha := partial_evaluate_policy_is_sound hp₃ h₂
    simp only [hr, Residual.evaluate] at ha
    exact to_option_right_ok' ha

  suffices h : pid ∈ satisfiedPolicies Effect.forbid policies req es by
    have hd : IsExplicitlyForbidden req es policies := by
      exists p
      and_intros <;> grind [satisfied]
    replace hd : (Spec.isAuthorized req es policies).decision = .deny :=
      forbid_trumps_permit _ _ _ hd
    grind [Spec.isAuthorized]

  simp only [satisfiedPolicies, satisfiedWithEffect, satisfied, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, ← Set.make_mem, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq]
  exists p
  and_intros
  · exact hp₁
  · simpa [←hp₂] using heff
  · exact ha
  · simpa [←hp₂] using hpid

end Cedar.Thm
