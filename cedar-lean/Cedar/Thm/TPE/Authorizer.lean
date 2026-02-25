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
import Cedar.Thm.TPE.Policy
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.Authorization

namespace Cedar.Thm

open Cedar.Data
open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

/-- Establishes a useful starting point for different lemmas, roughly stating
that residual policies are the result of evaluating the input policies. In most
cases it should be nicer to use `residual_to_policy` and `policy_to_residual`.
When you need to relate residual and input policies. -/
theorem residual_policies_are_evaluated_policies
  {schema : Schema}
  {policies : List Policy}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  ∃ rps,
    List.Forall₂ (λ p rp => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes = Except.ok rp) policies rps ∧
    response = isAuthorized.isAuthorizedFromResiduals rps
:= by
  intro h
  simp only [TPE.isAuthorized] at h
  cases h₁ : List.mapM (λ p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;>
    simp only [bind_pure_comp, h₁, Except.map_ok, Except.map_error, Except.ok.injEq, reduceCtorEq] at h
  rw [List.mapM_ok_iff_forall₂] at h₁
  exact ⟨_, h₁, h.symm⟩

theorem is_authorized_has_residuals
  {schema : Schema}
  {policies : List Policy}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  ∃ rps, response = isAuthorized.isAuthorizedFromResiduals rps
:= by
  intro h
  have ⟨rps, _, h_resp⟩ := residual_policies_are_evaluated_policies h
  exact ⟨rps, h_resp⟩

/-- If `TPE.isAuthorized` succeeds and a residual policy `rp` is in the
response's residual list, then there exists a corresponding policy `p` in the
original list with matching id and effect, and `evaluatePolicy` produced the
residual. -/
theorem residual_to_policy
  {schema : Schema}
  {policies : List Policy}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  {rp : ResidualPolicy}
  (h_auth : TPE.isAuthorized schema policies preq pes = Except.ok response)
  (h_mem : rp ∈ response.residuals) :
  ∃ p ∈ policies, ∃ r, evaluatePolicy schema p preq pes = .ok r ∧ rp = ⟨p.id, p.effect, r⟩
:= by
  obtain ⟨rps, h_forall, rfl⟩ := residual_policies_are_evaluated_policies h_auth
  simp only [isAuthorized.isAuthorizedFromResiduals] at h_mem
  have ⟨p, hp₁, hp₂⟩ := List.forall₂_implies_all_right h_forall rp h_mem
  cases hp₃ : evaluatePolicy schema p preq pes <;>
    simp only [hp₃, Except.map_error, Except.map_ok, reduceCtorEq, Except.ok.injEq] at hp₂
  exact ⟨p, hp₁, _, hp₃, hp₂.symm⟩

/-- If `TPE.isAuthorized` succeeds and a policy `p` is in the original list,
then there exists a corresponding residual policy in the response's residual
list, and `evaluatePolicy` produced the residual. -/
theorem policy_to_residual
  {schema : Schema}
  {policies : List Policy}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  {p : Policy}
  (h_auth : TPE.isAuthorized schema policies preq pes = Except.ok response)
  (h_mem : p ∈ policies) :
  ∃ rp ∈ response.residuals, ∃ r, evaluatePolicy schema p preq pes = .ok r ∧ rp = ⟨p.id, p.effect, r⟩
:= by
  obtain ⟨rps, h_forall, rfl⟩ := residual_policies_are_evaluated_policies h_auth
  simp only [isAuthorized.isAuthorizedFromResiduals]
  have ⟨rp, hrp₁, hrp₂⟩ := List.forall₂_implies_all_left h_forall p h_mem
  cases hrp₃ : evaluatePolicy schema p preq pes <;>
    simp only [hrp₃, Except.map_error, Except.map_ok, reduceCtorEq, Except.ok.injEq] at hrp₂
  exact ⟨rp, hrp₁, _, rfl, hrp₂.symm⟩

theorem reauthorize_satisfied_policies_equiv
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  (hv : isValidAndConsistent schema req es preq pes = Except.ok ())
  (h_auth : TPE.isAuthorized schema policies preq pes = Except.ok response) :
  ∀ effect,
    TPE.Response.reauthorize.satisfiedPolicies effect response.residuals req es = Spec.satisfiedPolicies effect policies req es
:= by
  obtain ⟨rps, h_forall, rfl⟩ := residual_policies_are_evaluated_policies h_auth
  intro effect
  have h_auth₁ := List.forall₂_implies_all_right h_forall
  have h_auth₂ := List.forall₂_implies_all_left h_forall
  clear h_auth
  simp [Response.reauthorize.satisfiedPolicies, satisfiedPolicies, satisfiedWithEffect, Response.reauthorize.satisfiedWithEffect]
  rw [←Data.Set.subset_iff_eq (Data.Set.make_wf _) (Data.Set.make_wf _)]
  simp [Data.Set.subset_def, ←Data.Set.make_mem, List.mem_filterMap]
  and_intros
  · intro pid rp h₁ h₂ h₃ h₄
    replace ⟨p, h_auth₁, h_auth₂⟩ := h_auth₁ rp h₁
    cases h_auth₃ : evaluatePolicy schema p preq pes <;> simp [h_auth₃] at h_auth₂
    simp only [← h_auth₂] at h₁ h₂ h₃ h₄
    subst h₄ h₂
    exists p
    simp only [h_auth₁, true_and, and_true]
    rw [policy_satisfied_iff_residual_eval_true h_auth₃ hv]
    simpa [Response.reauthorize.satisfied] using h₃
  · intro pid p h₁ h₂ h₃ h₄
    replace ⟨rp, h_auth₁, h_auth₂⟩ := h_auth₂ _ h₁
    exists rp
    simp [isAuthorized.isAuthorizedFromResiduals, h_auth₁, true_and]
    cases h_auth₃ : evaluatePolicy schema p preq pes <;> simp [h_auth₃] at h_auth₂
    subst h_auth₂
    simp only [h₂, Response.reauthorize.satisfied, decide_eq_true_eq, true_and, h₄, and_true]
    rw [←policy_satisfied_iff_residual_eval_true h_auth₃ hv]
    exact h₃

theorem reauthorize_error_policies_equiv
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  (hv : isValidAndConsistent schema req es preq pes = Except.ok ())
  (h_auth : TPE.isAuthorized schema policies preq pes = Except.ok response) :
  TPE.Response.reauthorize.errorPolicies response.residuals req es = Spec.errorPolicies policies req es
:= by
  obtain ⟨rps, _, rfl⟩ := residual_policies_are_evaluated_policies h_auth
  simp [Spec.errorPolicies, TPE.Response.reauthorize.errorPolicies, Response.reauthorize.errored, Spec.errored]
  rw [←Data.Set.subset_iff_eq (Data.Set.make_wf _) (Data.Set.make_wf _)]
  simp [Data.Set.subset_def, ←Data.Set.make_mem, List.mem_filterMap]
  and_intros
  · intro pid rp h₁ h₂ h₃
    have ⟨p, h_auth₁, r, h_auth₂, h_auth₃⟩ := residual_to_policy h_auth h₁
    simp only [h_auth₃] at h₁ h₂ h₃
    simp only [Response.reauthorize.hasError] at h₂
    split at h₂ <;> simp only [Bool.false_eq_true] at h₂
    rename_i h₄
    have h₅ := policy_error_iff_residual_eval_error h_auth₂ hv
    exists p
    simp [h_auth₁, h₃, h₄, h₅]
  · intro pid p h₁ h₂ h₃
    have ⟨rp, h_auth₁, _, h_auth₂, h_auth₃⟩ := policy_to_residual h_auth h₁
    cases h_auth₃ : evaluatePolicy schema p preq pes <;>
      simp only [h_auth₃, reduceCtorEq, Except.ok.injEq] at h_auth₂
    rw [policy_error_iff_residual_eval_error h_auth₃ hv] at h₂
    grind [Response.reauthorize.hasError, isAuthorized.isAuthorizedFromResiduals]

theorem no_satisfied_effect_if_empty_satisfied_and_residual_policies
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  {effect : Effect}
  (h₁ : TPE.isAuthorized schema policies preq pes = Except.ok response)
  (h₂ : isValidAndConsistent schema req es preq pes = Except.ok ())
  (h_satisfied_empty : (isAuthorized.satisfiedPolicies effect response.residuals).isEmpty)
  (h_residual_empty : (isAuthorized.residualPolicies effect response.residuals).isEmpty) :
  ¬HasSatisfiedEffect effect req es policies
:= by
  obtain ⟨_, rfl⟩ := is_authorized_has_residuals h₁
  simp only [isAuthorized.isAuthorizedFromResiduals] at h_satisfied_empty h_residual_empty
  simp only [HasSatisfiedEffect, not_exists, not_and]
  intro p hp₁ hp₂ h
  have ⟨rp, h₅, r, he, hrp⟩ := policy_to_residual h₁ hp₁
  simp only [isAuthorized.isAuthorizedFromResiduals] at h₅

  replace ⟨_, hp⟩ :
    ∃ ty, r = .val (.prim (.bool false)) ty ∨ r = .error ty
  := by
    simp only [isAuthorized.satisfiedPolicies, Set.empty_iff_not_exists, ← Set.make_mem,
      List.mem_filterMap, ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied,
      Residual.isTrue, Option.ite_none_right_eq_some] at h_satisfied_empty
    simp only [isAuthorized.residualPolicies, Set.empty_iff_not_exists, ← Set.make_mem,
      List.mem_filterMap, ResidualPolicy.residualWithEffect, ResidualPolicy.isResidual,
      ResidualPolicy.satisfied, Residual.isTrue, ResidualPolicy.isFalse, Residual.isFalse,
      ResidualPolicy.hasError, Residual.isError, Option.ite_none_right_eq_some, not_exists] at h_residual_empty
    grind

  rw [policy_satisfied_iff_residual_eval_true he h₂] at h
  cases hp
  · rename_i hp; simp only at hp; simp [hp, Residual.evaluate] at h
  · rename_i hp; subst hp; simp [Residual.evaluate] at h

theorem satisfied_effect_if_non_empty_satisfied_policies
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  {effect : Effect}
  (h₁ : TPE.isAuthorized schema policies preq pes = Except.ok response)
  (h₂ : isValidAndConsistent schema req es preq pes = Except.ok ())
  (h_non_empty : ¬(isAuthorized.satisfiedPolicies effect response.residuals).isEmpty) :
  HasSatisfiedEffect effect req es policies
:= by
  obtain ⟨_, rfl⟩ := is_authorized_has_residuals h₁
  simp only [isAuthorized.isAuthorizedFromResiduals] at h_non_empty
  rw [Set.non_empty_iff_exists] at h_non_empty
  replace ⟨_, hf⟩ := h_non_empty
  simp [isAuthorized.satisfiedPolicies] at hf
  rw [←Set.make_mem] at hf
  simp [List.mem_filterMap] at hf
  simp [ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied, Residual.isTrue] at hf
  have ⟨rp, hf₁, ⟨ hf₂, hf₃⟩, hf₄⟩ := hf ; clear hf
  split at hf₃ <;> try contradiction
  rename_i hf₅

  have ⟨p, hp₁, r, hp₃, hp₂⟩ := residual_to_policy h₁ hf₁
  rw [hp₂] at hf₅; subst hf₅

  exists p
  and_intros
  · exact hp₁
  · rw [hp₂] at hf₂; exact hf₂
  · exact residual_true_implies_policy_satisfied hp₃ h₂ (by simp [Residual.isTrue])

theorem partial_authorize_error_policies_is_sound
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  (effect : Effect) :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  isAuthorized.errorPolicies effect response.residuals ⊆ (Spec.isAuthorized req es policies).erroringPolicies
:= by
  intro h₁ h₂
  obtain ⟨_, rfl⟩ := is_authorized_has_residuals h₁
  simp only [isAuthorized.isAuthorizedFromResiduals]
  have h₅ : (Spec.isAuthorized req es policies).erroringPolicies = errorPolicies policies req es :=
    by grind [Spec.isAuthorized]
  simp only [errorPolicies, errored] at h₅
  simp only [h₅, isAuthorized.errorPolicies, Set.subset_def, ← Set.make_mem, List.mem_filterMap,
    ResidualPolicy.erroredWithEffect, Bool.and_eq_true, beq_iff_eq,
    Option.ite_none_right_eq_some, Option.some.injEq, forall_exists_index, and_imp]
  intro pid rp hrp hef herr hpid

  have ⟨p, hp₁, r, hp₃, hp₂⟩ := residual_to_policy h₁ hrp

  exists p
  and_intros
  · exact hp₁
  · exact residual_error_implies_policy_error hp₃ h₂ (by rw [hp₂] at herr; exact herr)
  · simp [hp₂] at hpid; exact hpid

theorem partial_authorize_satisfied_policies_is_sound
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  (effect : Effect) :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  isAuthorized.satisfiedPolicies effect response.residuals ⊆ Spec.satisfiedPolicies effect policies req es
:= by
  intro h₁ h₂
  obtain ⟨_, rfl⟩ := is_authorized_has_residuals h₁
  simp only [isAuthorized.isAuthorizedFromResiduals]
  simp only [isAuthorized.satisfiedPolicies, satisfiedPolicies, satisfiedWithEffect,
    Bool.and_eq_true, beq_iff_eq, Set.subset_def, ← Set.make_mem, List.mem_filterMap,
    ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied, Option.ite_none_right_eq_some,
    Option.some.injEq, forall_exists_index, and_imp]
  intro pid rp hrp hef htrue hpid

  have ⟨p, hp₁, r, hp₃, hp₂⟩ := residual_to_policy h₁ hrp

  exists p
  and_intros
  · exact hp₁
  · simp [hp₂] at hef; exact hef
  · exact residual_true_implies_policy_satisfied hp₃ h₂ (by rw [hp₂] at htrue; exact htrue)
  · simp [hp₂] at hpid; exact hpid

theorem partial_authorize_satisfied_forbids_is_sound
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  response.satisfiedForbids ⊆ Spec.satisfiedPolicies .forbid policies req es
:= by
  intro h₁ h₂
  obtain ⟨_, rfl⟩ := is_authorized_has_residuals h₁
  simp only [isAuthorized.isAuthorizedFromResiduals]
  exact partial_authorize_satisfied_policies_is_sound .forbid h₁ h₂

theorem partial_authorize_satisfied_permits_is_sound
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  response.satisfiedPermits ⊆ Spec.satisfiedPolicies .permit policies req es
:= by
  intro h₁ h₂
  obtain ⟨_, rfl⟩ := is_authorized_has_residuals h₁
  simp only [isAuthorized.isAuthorizedFromResiduals]
  exact partial_authorize_satisfied_policies_is_sound .permit h₁ h₂

theorem satisfied_policy_in_satisfied_or_residual
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  {p : Policy}
  (h₁ : TPE.isAuthorized schema policies preq pes = Except.ok response)
  (h₂ : isValidAndConsistent schema req es preq pes = Except.ok ())
  (h_mem : p ∈ policies)
  (h_sat : satisfied p req es) :
  p.id ∈ isAuthorized.satisfiedPolicies p.effect response.residuals ∪
         isAuthorized.residualPolicies p.effect response.residuals
:= by
  obtain ⟨_, rfl⟩ := is_authorized_has_residuals h₁
  simp only [isAuthorized.isAuthorizedFromResiduals]
  have ⟨rp, hrp₁, r, hrp₃, hrp₂⟩ := policy_to_residual h₁ h_mem
  rw [Set.mem_union_iff_mem_or]
  by_cases h_true : r.isTrue
  · left
    simp only [isAuthorized.satisfiedPolicies, ← Set.make_mem, List.mem_filterMap,
      ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied,
      Bool.and_eq_true, beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq]
    exists rp
    subst hrp₂
    simp only [isAuthorized.isAuthorizedFromResiduals] at hrp₁
    simp [hrp₁, h_true]
  · right
    rw [policy_satisfied_iff_residual_eval_true hrp₃ h₂] at h_sat
    have h_not_false : r.isFalse = false := by
      simp only [Bool.eq_false_iff]; intro h_false
      cases r <;> simp [Residual.isFalse] at h_false; simp [Residual.evaluate] at h_sat; grind
    have h_not_err : r.isError = false := by
      simp only [Bool.eq_false_iff]; intro h_err
      cases r <;> simp [Residual.isError] at h_err; simp [Residual.evaluate] at h_sat
    simp only [isAuthorized.residualPolicies, ← Set.make_mem, List.mem_filterMap,
      ResidualPolicy.residualWithEffect, Bool.and_eq_true, beq_iff_eq,
      Option.ite_none_right_eq_some, Option.some.injEq]
    exists rp
    subst hrp₂
    simp only [isAuthorized.isAuthorizedFromResiduals] at hrp₁
    simp [hrp₁, ResidualPolicy.isResidual, ResidualPolicy.satisfied, ResidualPolicy.isFalse,
      ResidualPolicy.hasError, h_true, h_not_false, h_not_err]

theorem errored_policy_in_error_or_residual
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response}
  {p : Policy}
  (h₁ : TPE.isAuthorized schema policies preq pes = Except.ok response)
  (h₂ : isValidAndConsistent schema req es preq pes = Except.ok ())
  (h_mem : p ∈ policies)
  (h_err : hasError p req es) :
  p.id ∈ isAuthorized.errorPolicies p.effect response.residuals ∪
         isAuthorized.residualPolicies p.effect response.residuals
:= by
  obtain ⟨_, rfl⟩ := is_authorized_has_residuals h₁
  simp only [isAuthorized.isAuthorizedFromResiduals]
  have ⟨rp, hrp₁, r, hrp₃, hrp₂⟩ := policy_to_residual h₁ h_mem
  rw [Set.mem_union_iff_mem_or]
  by_cases h_isErr : r.isError
  · left
    simp only [isAuthorized.errorPolicies, ← Set.make_mem, List.mem_filterMap,
      ResidualPolicy.erroredWithEffect, ResidualPolicy.hasError,
      Bool.and_eq_true, beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq]
    exists rp
    subst hrp₂
    simp only [isAuthorized.isAuthorizedFromResiduals] at hrp₁
    simp [hrp₁, h_isErr]
  · right
    rw [policy_error_iff_residual_eval_error hrp₃ h₂] at h_err
    have h_not_sat : r.isTrue = false := by
      simp only [Bool.eq_false_iff]; intro h_sat
      cases r <;> simp [Residual.isTrue] at h_sat; simp [Residual.evaluate] at h_err
    have h_not_false : r.isFalse = false := by
      simp only [Bool.eq_false_iff]; intro h_false
      cases r <;> simp [Residual.isFalse] at h_false; simp [Residual.evaluate] at h_err
    simp only [isAuthorized.residualPolicies, ← Set.make_mem, List.mem_filterMap,
      ResidualPolicy.residualWithEffect, Bool.and_eq_true, beq_iff_eq,
      Option.ite_none_right_eq_some, Option.some.injEq]
    exists rp
    subst hrp₂
    simp only [isAuthorized.isAuthorizedFromResiduals] at hrp₁
    simp [hrp₁, ResidualPolicy.isResidual, ResidualPolicy.satisfied, ResidualPolicy.isFalse,
      ResidualPolicy.hasError, h_not_sat, h_not_false, h_isErr]

end Cedar.Thm
