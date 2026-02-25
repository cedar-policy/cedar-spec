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
import Cedar.Thm.TPE.PolicySoundness
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

private theorem reauthorize_satisfied_policies_equiv'
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {residuals : List ResidualPolicy}
  (hv : isValidAndConsistent schema req es preq pes = Except.ok ())
  (h_auth : List.Forall₂ (λ x y => ResidualPolicy.mk x.id x.effect <$> evaluatePolicy schema x preq pes = .ok y) policies residuals) :
  ∀ effect,
    TPE.Response.reauthorize.satisfiedPolicies effect residuals req es = Spec.satisfiedPolicies effect policies req es
:= by
  intro effect
  have h_auth₁ := List.forall₂_implies_all_right h_auth
  have h_auth₂ := List.forall₂_implies_all_left h_auth
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
    simp only [h_auth₁, true_and, and_true, satisfied, decide_eq_true_eq]
    simp only [Response.reauthorize.satisfied, decide_eq_true_eq] at h₃
    exact to_option_right_ok (partial_evaluate_policy_is_sound h_auth₃ hv) h₃
  · intro pid p h₁ h₂ h₃ h₄
    replace ⟨rp, h_auth₁, h_auth₂⟩ := h_auth₂ _ h₁
    exists rp
    simp only [h_auth₁, true_and]
    cases h_auth₃ : evaluatePolicy schema p preq pes <;> simp [h_auth₃] at h_auth₂
    subst h_auth₂
    simp only [h₂, Response.reauthorize.satisfied, decide_eq_true_eq, true_and, h₄, and_true]
    rename_i r
    simp only [satisfied, decide_eq_true_eq] at h₃
    exact to_option_left_ok (partial_evaluate_policy_is_sound h_auth₃ hv) h₃

private theorem reauthorize_error_policies_equiv'
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {residuals : List ResidualPolicy}
  (hv : isValidAndConsistent schema req es preq pes = Except.ok ())
  (h_auth : List.Forall₂ (λ x y => ResidualPolicy.mk x.id x.effect <$> evaluatePolicy schema x preq pes = .ok y) policies residuals) :
  TPE.Response.reauthorize.errorPolicies residuals req es = Spec.errorPolicies policies req es
:= by
  have h_auth₁ := List.forall₂_implies_all_right h_auth
  have h_auth₂ := List.forall₂_implies_all_left h_auth
  clear h_auth
  simp [Spec.errorPolicies, TPE.Response.reauthorize.errorPolicies, Response.reauthorize.errored, Spec.errored]
  rw [←Data.Set.subset_iff_eq (Data.Set.make_wf _) (Data.Set.make_wf _)]
  simp [Data.Set.subset_def, ←Data.Set.make_mem, List.mem_filterMap]
  and_intros
  · intro pid rp h₁ h₂ h₃
    replace ⟨p, h_auth₁, h_auth₂⟩ := h_auth₁ rp h₁
    cases h_auth₃ : evaluatePolicy schema p preq pes <;> simp [h_auth₃] at h_auth₂
    simp only [←h_auth₂] at h₁ h₂ h₃
    simp only [Response.reauthorize.hasError] at h₂
    split at h₂ <;> simp only [Bool.false_eq_true] at h₂
    rename_i h₃
    replace ⟨_, h_auth₃⟩ : ∃ e, Spec.evaluate p.toExpr req es = Except.error e := by
      replace h_auth₃ := partial_evaluate_policy_is_sound h_auth₃ hv
      rw [h₃] at h_auth₃
      exact to_option_right_err h_auth₃
    grind [hasError]
  · intro pid p h₁ h₂ h₃
    replace ⟨_, _, h_auth₂⟩ := h_auth₂ _ h₁
    cases h_auth₃ : evaluatePolicy schema p preq pes <;>
      simp only [h_auth₃, Except.map_error, reduceCtorEq, Except.map_ok, Except.ok.injEq] at h_auth₂
    rename_i r
    replace ⟨_, h_auth₃⟩ : ∃ e, r.evaluate req es = Except.error e := by
      replace h_auth₃ := partial_evaluate_policy_is_sound h_auth₃ hv
      have ⟨_, h₃⟩ : ∃ e, Spec.evaluate p.toExpr req es = Except.error e := by
        grind [hasError]
      rw [h₃] at h_auth₃
      exact to_option_left_err h_auth₃
    grind [Response.reauthorize.hasError]
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
  have ⟨rps, h_forall, h_resp⟩ := tpe_isAuthorized_forall₂ h_auth
  subst h_resp
  exact reauthorize_satisfied_policies_equiv' hv h_forall

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
  have ⟨rps, h_forall, h_resp⟩ := tpe_isAuthorized_forall₂ h_auth
  subst h_resp
  exact reauthorize_error_policies_equiv' hv h_forall

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
  have ⟨rps, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄
  simp only [isAuthorized.isAuthorizedFromResiduals] at h_satisfied_empty h_residual_empty
  simp [HasSatisfiedEffect, satisfied]
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

  have ha : r.evaluate req es = Except.ok (Value.prim (Prim.bool true)) :=
    policy_satisfied_implies_residual_eval_true he h₂ h

  cases hp
  · rename_i hp; simp only at hp; simp [hp, Residual.evaluate] at ha
  · rename_i hp; subst hp; simp [Residual.evaluate] at ha

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
  have ⟨rps, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄
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
  · simpa [satisfied] using residual_true_implies_policy_satisfied hp₃ h₂ (by simp [Residual.isTrue])
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
  have ⟨rps, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄
  simp only [isAuthorized.isAuthorizedFromResiduals]
  have h₅ : (Spec.isAuthorized req es policies).erroringPolicies = errorPolicies policies req es :=
    by grind [Spec.isAuthorized]
  simp only [errorPolicies, errored, hasError] at h₅
  simp only [h₅, isAuthorized.errorPolicies, Set.subset_def, ← Set.make_mem, List.mem_filterMap,
    ResidualPolicy.erroredWithEffect, ResidualPolicy.hasError, Residual.isError, Bool.and_eq_true,
    beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq, forall_exists_index, and_imp]
  intro pid rp hrp hef herr hpid

  have ⟨p, hp₁, r, hp₃, hp₂⟩ := residual_to_policy h₁ hrp

  exists p
  and_intros
  · exact hp₁
  · have ⟨_, ha⟩ := residual_error_implies_policy_error hp₃ h₂ (by rw [hp₂] at herr; exact herr)
    simp [ha]
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
  have ⟨rps, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄
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
  · simp only [satisfied, decide_eq_true_eq]
    exact residual_true_implies_policy_satisfied hp₃ h₂ (by rw [hp₂] at htrue; exact htrue)
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
  have ⟨rps, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄
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
  have ⟨rps, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄
  simp only [isAuthorized.isAuthorizedFromResiduals]
  exact partial_authorize_satisfied_policies_is_sound .permit h₁ h₂

/-- Completeness for satisfied policies: if a concrete policy is satisfied,
its ID appears in either the satisfied or residual bucket of the response
for the matching effect. -/
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
  have ⟨rps, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄
  simp only [isAuthorized.isAuthorizedFromResiduals]
  have ⟨rp, hrp₁, r, hrp₃, hrp₂⟩ := policy_to_residual h₁ h_mem
  subst hrp₂
  replace h_sat : Spec.evaluate p.toExpr req es = .ok (.prim (.bool true)) := by grind [satisfied]
  have ha := policy_satisfied_implies_residual_eval_true hrp₃ h₂ h_sat
  rw [Set.mem_union_iff_mem_or]
  by_cases h_true : r.isTrue
  · left
    simp only [isAuthorized.satisfiedPolicies, ← Set.make_mem, List.mem_filterMap,
      ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied,
      Bool.and_eq_true, beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq]
    exact ⟨⟨p.id, p.effect, r⟩, hrp₁, ⟨rfl, h_true⟩, rfl⟩
  · right
    have h_not_false : r.isFalse = false := by
      simp only [Bool.eq_false_iff]; intro h_false
      cases r <;> simp [Residual.isFalse] at h_false; simp [Residual.evaluate] at ha; grind
    have h_not_err : r.isError = false := by
      simp only [Bool.eq_false_iff]; intro h_err
      cases r <;> simp [Residual.isError] at h_err; simp [Residual.evaluate] at ha
    simp only [isAuthorized.residualPolicies, ← Set.make_mem, List.mem_filterMap,
      ResidualPolicy.residualWithEffect, Bool.and_eq_true, beq_iff_eq,
      Option.ite_none_right_eq_some, Option.some.injEq]
    refine ⟨⟨p.id, p.effect, r⟩, hrp₁, ⟨rfl, ?_⟩, rfl⟩
    simp [ResidualPolicy.isResidual, ResidualPolicy.satisfied, ResidualPolicy.isFalse,
      ResidualPolicy.hasError, h_true, h_not_false, h_not_err]

/-- Completeness for errored policies: if a concrete policy errors,
its ID appears in either the error or residual bucket of the response. -/
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
  (h_err : ∃ e, Spec.evaluate p.toExpr req es = .error e) :
  p.id ∈ isAuthorized.errorPolicies p.effect response.residuals ∪
         isAuthorized.residualPolicies p.effect response.residuals
:= by
  have ⟨rps, _, h₄⟩ := tpe_isAuthorized_forall₂ h₁
  subst h₄
  simp only [isAuthorized.isAuthorizedFromResiduals]
  have ⟨rp, hrp₁, r, hrp₃, hrp₂⟩ := policy_to_residual h₁ h_mem
  subst hrp₂
  have ⟨_, hr⟩ := policy_error_implies_residual_eval_error hrp₃ h₂ h_err
  rw [Set.mem_union_iff_mem_or]
  by_cases h_isErr : r.isError
  · left
    simp only [isAuthorized.errorPolicies, ← Set.make_mem, List.mem_filterMap,
      ResidualPolicy.erroredWithEffect, ResidualPolicy.hasError,
      Bool.and_eq_true, beq_iff_eq, Option.ite_none_right_eq_some, Option.some.injEq]
    exact ⟨⟨p.id, p.effect, r⟩, hrp₁, ⟨rfl, h_isErr⟩, rfl⟩
  · right
    have h_not_sat : r.isTrue = false := by
      simp only [Bool.eq_false_iff]; intro h_sat
      cases r <;> simp [Residual.isTrue] at h_sat; simp [Residual.evaluate] at hr
    have h_not_false : r.isFalse = false := by
      simp only [Bool.eq_false_iff]; intro h_false
      cases r <;> simp [Residual.isFalse] at h_false; simp [Residual.evaluate] at hr
    simp only [isAuthorized.residualPolicies, ← Set.make_mem, List.mem_filterMap,
      ResidualPolicy.residualWithEffect, Bool.and_eq_true, beq_iff_eq,
      Option.ite_none_right_eq_some, Option.some.injEq]
    refine ⟨⟨p.id, p.effect, r⟩, hrp₁, ⟨rfl, ?_⟩, rfl⟩
    simp [ResidualPolicy.isResidual, ResidualPolicy.satisfied, ResidualPolicy.isFalse,
      ResidualPolicy.hasError, h_not_sat, h_not_false, h_isErr]

end Cedar.Thm
