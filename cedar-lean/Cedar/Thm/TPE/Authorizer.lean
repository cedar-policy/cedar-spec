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

def ResidualPoliciesEquiv
  (policies : List Policy)
  (residuals : List ResidualPolicy)
  (req : Request)
  (es : Entities) : Prop :=
  List.Forall₂ (λ p rp =>
    rp.id = p.id ∧
    rp.effect = p.effect ∧
    (rp.residual.evaluate req es).toOption = (Spec.evaluate p.toExpr req es).toOption
  ) policies residuals

theorem isValidAndConsistent_env
  {schema : Schema} {req : Request} {es : Entities}
  {preq : PartialRequest} {pes : PartialEntities} :
  isValidAndConsistent schema req es preq pes = .ok () →
  ∃ env,
    schema.environment? preq.principal.ty preq.resource.ty preq.action = .some env ∧
    InstanceOfWellFormedEnvironment req es env
:= by
  intro h_valid
  simp only [isValidAndConsistent] at h_valid
  split at h_valid <;> try cases h_valid
  rename_i env heq
  exists env; refine ⟨heq, ?_⟩
  rcases do_eq_ok₂ h_valid with ⟨h₁, h₂⟩
  simp only [isValidAndConsistent.requestIsConsistent, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.and_eq_true, decide_eq_true_eq] at h₁
  split at h₁ <;> try cases h₁
  rename_i h_guard; simp only [not_or, Bool.not_eq_false] at h_guard
  simp only [isValidAndConsistent.entitiesIsConsistent, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h₂
  split at h₂ <;> try cases h₂
  rename_i heq₄; simp only [not_or, Bool.not_eq_false] at heq₄
  rcases heq₄ with ⟨_, heq₄⟩
  simp only [Except.isOk, Except.toBool] at heq₄
  split at heq₄ <;> cases heq₄; rename_i heq₄
  simp only [bind, Except.bind, isValidAndConsistent.envIsWellFormed, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h₂
  split at h₂ <;> try cases h₂
  simp only [ite_eq_right_iff, reduceCtorEq, imp_false, Bool.not_eq_false] at h₂
  simp only [Except.isOk, Except.toBool] at h₂
  split at h₂ <;> cases h₂; rename_i heq₅
  exact instance_of_well_formed_env heq₅ h_guard.2 heq₄

theorem evaluatePolicies_residuals_equiv
  {schema : Schema}
  {policies : List Policy}
  {rps : List ResidualPolicy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  (hv : isValidAndConsistent schema req es preq pes = Except.ok ())
  (h : isAuthorized.evaluatePolicies schema policies preq pes = Except.ok rps) :
  ResidualPoliciesEquiv policies rps req es
:= by
  have h_ref := consistent_checks_ensure_refinement hv
  have ⟨env, h_schema_env, h_wf⟩ := isValidAndConsistent_env hv
  simp only [isAuthorized.evaluatePolicies, bind_pure_comp, List.mapM_ok_iff_forall₂] at h
  apply List.Forall₂.imp _ h
  intro p rp h₂
  cases h_ep : evaluatePolicy schema p preq pes <;> simp only [h_ep, Except.map_error, reduceCtorEq] at h₂
  simp only [Except.map_ok, Except.ok.injEq] at h₂
  simp only [true_and, ←h₂]
  exact (partial_evaluate_policy_is_sound h_ep h_schema_env h_wf h_ref).symm

theorem reauthorize_satisfied_policies_equiv
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {residuals : List ResidualPolicy}
  (h_auth : ResidualPoliciesEquiv policies residuals req es) :
  ∀ effect,
    TPE.Response.reauthorize.satisfiedPolicies effect residuals req es = Spec.satisfiedPolicies effect policies req es
:= by
  intro effect
  have h_auth₁ := List.forall₂_implies_all_right h_auth
  have h_auth₂ := List.forall₂_implies_all_left h_auth
  clear h_auth
  simp [Response.reauthorize.satisfiedPolicies, satisfiedPolicies, satisfiedWithEffect, Response.reauthorize.satisfiedWithEffect]
  rw [←Data.Set.subset_iff_eq (Data.Set.make_wf _) (Data.Set.make_wf _)]
  simp [Data.Set.subset_def, Data.Set.mem_make, List.mem_filterMap]
  and_intros
  · intro pid rp h₁ h₂ h₃ h₄
    replace ⟨p, h_auth₁, h_auth₂, h_auth₃, h_auth₄⟩ := h_auth₁ rp h₁
    exists p
    simp only [h_auth₁, ← h_auth₃, h₂, satisfied, decide_eq_true_eq, true_and, ← h_auth₂, h₄, and_true]
    simp only [Response.reauthorize.satisfied, decide_eq_true_eq] at h₃
    rw [h₃] at h_auth₄
    exact to_option_left_ok h_auth₄ rfl
  · intro pid p h₁ h₂ h₃ h₄
    replace ⟨rp, h_auth₁, h_auth₂, h_auth₃, h_auth₄⟩ := h_auth₂ _ h₁
    exists rp
    simp only [h_auth₁, h_auth₃, h₂, true_and, h_auth₂, h₄, and_true, Response.reauthorize.satisfied, decide_eq_true_eq]
    simp only [satisfied, decide_eq_true_eq] at h₃
    rw [h₃] at h_auth₄
    exact to_option_right_ok h_auth₄ rfl

theorem reauthorize_error_policies_equiv
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {residuals : List ResidualPolicy}
  (h_auth : ResidualPoliciesEquiv policies residuals req es) :
  TPE.Response.reauthorize.errorPolicies residuals req es = Spec.errorPolicies policies req es
:= by
  have h_auth₁ := List.forall₂_implies_all_right h_auth
  have h_auth₂ := List.forall₂_implies_all_left h_auth
  clear h_auth
  simp [Spec.errorPolicies, TPE.Response.reauthorize.errorPolicies, Response.reauthorize.errored, Spec.errored]
  rw [←Data.Set.subset_iff_eq (Data.Set.make_wf _) (Data.Set.make_wf _)]
  simp [Data.Set.subset_def, Data.Set.mem_make, List.mem_filterMap]
  and_intros
  · intro pid rp h₁ h₂ h₃
    replace ⟨p, h_auth₁, h_auth₂, h_auth₃, h_auth₄⟩ := h_auth₁ rp h₁
    simp only [Response.reauthorize.hasError] at h₂
    split at h₂ <;> simp only [Bool.false_eq_true] at h₂
    rename_i h_err
    have ⟨_, h_spec_err⟩ : ∃ e, Spec.evaluate p.toExpr req es = Except.error e := by
      rw [h_err] at h_auth₄
      exact to_option_left_err h_auth₄
    exists p
    refine ⟨h_auth₁, ?_, h_auth₂ ▸ h₃⟩
    grind [hasError]
  · intro pid p h₁ h₂ h₃
    replace ⟨rp, h_auth₁, h_auth₂, h_auth₃, h_auth₄⟩ := h_auth₂ _ h₁
    exists rp
    have ⟨_, h_spec_err⟩ : ∃ e, Spec.evaluate p.toExpr req es = Except.error e :=
      if_hasError_then_exists_error h₂
    have ⟨_, h_res_err⟩ : ∃ e, rp.residual.evaluate req es = Except.error e := by
      rw [h_spec_err] at h_auth₄
      exact to_option_right_err h_auth₄
    refine ⟨h_auth₁, ?_, h_auth₂ ▸ h₃⟩
    grind [Response.reauthorize.hasError]


theorem no_satisfied_effect_if_empty_satisfied_and_residual_policies
  {policies : List Policy}
  {rps : List ResidualPolicy}
  {req : Request}
  {es : Entities}
  {effect : Effect}
  (h₃ : ResidualPoliciesEquiv policies rps req es)
  (h_satisfied_empty : (isAuthorizedFromResiduals.satisfiedPolicies effect rps).isEmpty)
  (h_residual_empty : (isAuthorizedFromResiduals.residualPolicies effect rps).isEmpty) :
  ¬HasSatisfiedEffect effect req es policies
:= by
  simp [HasSatisfiedEffect, satisfied]
  intro p hp₁ hp₂ h
  replace ⟨rp, h₅, h_id, h_eff, h_eval⟩ := List.forall₂_implies_all_left h₃ p hp₁

  replace ⟨_, hp⟩ :
    ∃ ty, rp.residual = .val (.prim (.bool false)) ty ∨ rp.residual = .error ty
  := by
    simp only [isAuthorizedFromResiduals.satisfiedPolicies, Set.empty_iff_not_exists, Set.mem_make,
      List.mem_filterMap, ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied,
      Residual.isTrue, Option.ite_none_right_eq_some] at h_satisfied_empty
    simp only [isAuthorizedFromResiduals.residualPolicies, Set.empty_iff_not_exists, Set.mem_make,
      List.mem_filterMap, ResidualPolicy.residualWithEffect, ResidualPolicy.isResidual,
      ResidualPolicy.satisfied, Residual.isTrue, ResidualPolicy.isFalse, Residual.isFalse,
      ResidualPolicy.hasError, Residual.isError, Option.ite_none_right_eq_some, not_exists] at h_residual_empty
    grind

  have ha : rp.residual.evaluate req es = Except.ok (Value.prim (Prim.bool true)) :=
    to_option_right_ok h_eval h

  cases hp
  · rename_i hp; simp [hp, Residual.evaluate] at ha
  · rename_i hp; simp [hp, Residual.evaluate] at ha

theorem satisfied_effect_if_non_empty_satisfied_policies
  {policies : List Policy}
  {rps : List ResidualPolicy}
  {req : Request}
  {es : Entities}
  {effect : Effect}
  (h₃ : ResidualPoliciesEquiv policies rps req es)
  (h_non_empty : ¬(isAuthorizedFromResiduals.satisfiedPolicies effect rps).isEmpty) :
  HasSatisfiedEffect effect req es policies
:= by
  rw [Set.non_empty_iff_exists] at h_non_empty
  replace ⟨_, hf⟩ := h_non_empty
  simp [isAuthorizedFromResiduals.satisfiedPolicies] at hf
  simp [ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied, Residual.isTrue] at hf
  have ⟨rp, hf₁, ⟨hf₂, hf₃⟩, hf₄⟩ := hf ; clear hf
  split at hf₃ <;> try contradiction
  rename_i hf₅

  have ⟨p, hp₁, h_id, h_eff, h_eval⟩ := List.forall₂_implies_all_right h₃ rp hf₁

  exists p
  and_intros
  · exact hp₁
  · exact h_eff ▸ hf₂
  · simp only [hf₅, Residual.evaluate] at h_eval
    simpa [satisfied] using to_option_left_ok' h_eval

theorem residuals_decision_agrees
  {policies : List Policy}
  {rps : List ResidualPolicy}
  {req : Request}
  {es : Entities}
  {d : Decision}
  (h₃ : ResidualPoliciesEquiv policies rps req es)
  (h_dec : (isAuthorizedFromResiduals rps).decision = some d) :
  (Spec.isAuthorized req es policies).decision = d
:= by
  simp [isAuthorizedFromResiduals] at h_dec
  split at h_dec <;>
    simp only [Option.some.injEq, reduceCtorEq] at h_dec
  all_goals subst h_dec
  -- Deny (satisfied forbid exists)
  · have hf : ¬ (isAuthorizedFromResiduals.satisfiedPolicies .forbid rps).isEmpty := by grind
    exact forbid_trumps_permit _ _ _ (satisfied_effect_if_non_empty_satisfied_policies h₃ hf)
  -- Deny (no satisfied permits, no residual permits)
  · have hp₁ : (isAuthorizedFromResiduals.satisfiedPolicies .permit rps).isEmpty := by grind
    have hp₂ : (isAuthorizedFromResiduals.residualPolicies .permit rps).isEmpty := by grind
    exact default_deny _ _ _ (no_satisfied_effect_if_empty_satisfied_and_residual_policies h₃ hp₁ hp₂)
  -- Allow (no satisfied/residual forbids, satisfied permit exists)
  · have hf₁ : (isAuthorizedFromResiduals.satisfiedPolicies .forbid rps).isEmpty := by grind
    have hf₂ : (isAuthorizedFromResiduals.residualPolicies .forbid rps).isEmpty := by grind
    have hp : ¬ (isAuthorizedFromResiduals.satisfiedPolicies .permit rps).isEmpty := by grind
    exact (allowed_iff_explicitly_permitted_and_not_denied _ _ _).mp
      ⟨satisfied_effect_if_non_empty_satisfied_policies h₃ hp,
       no_satisfied_effect_if_empty_satisfied_and_residual_policies h₃ hf₁ hf₂⟩

theorem partial_authorize_error_policies_is_sound
  {policies : List Policy}
  {rps : List ResidualPolicy}
  {req : Request}
  {es : Entities}
  (effect : Effect)
  (h₁ : ResidualPoliciesEquiv policies rps req es) :
  isAuthorizedFromResiduals.errorPolicies effect rps ⊆ (Spec.isAuthorized req es policies).erroringPolicies
:= by
  have h₄ : (Spec.isAuthorized req es policies).erroringPolicies = errorPolicies policies req es :=
    by grind [Spec.isAuthorized]
  simp only [errorPolicies, errored, hasError] at h₄
  simp only [isAuthorizedFromResiduals.errorPolicies, h₄, Set.subset_def, Set.mem_make, List.mem_filterMap,
    ResidualPolicy.erroredWithEffect, Bool.and_eq_true, Option.ite_none_right_eq_some, forall_exists_index, and_imp]
  intro pid rp hrp hef herr hpid
  have ⟨p, hp₁, h_id, h_eff, h_eval⟩ := List.forall₂_implies_all_right h₁ rp hrp
  exists p
  and_intros
  · exact hp₁
  · replace ⟨_, ha⟩ : ∃ e, Spec.evaluate p.toExpr req es = .error e := by
      replace herr := isError_evaluate_err herr req es
      rw [herr.choose_spec] at h_eval
      exact to_option_left_err h_eval
    simp [ha]
  · exact h_id ▸ hpid

theorem partial_authorize_satisfied_policies_is_sound
  {policies : List Policy}
  {rps : List ResidualPolicy}
  {req : Request}
  {es : Entities}
  (effect : Effect)
  (h₁ : ResidualPoliciesEquiv policies rps req es) :
  isAuthorizedFromResiduals.satisfiedPolicies effect rps ⊆ Spec.satisfiedPolicies effect policies req es
:= by
  simp only [isAuthorizedFromResiduals.satisfiedPolicies, satisfiedPolicies, satisfiedWithEffect,
    Bool.and_eq_true, beq_iff_eq, Set.subset_def, Set.mem_make, List.mem_filterMap,
    ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied, Option.ite_none_right_eq_some,
    Option.some.injEq, forall_exists_index, and_imp]
  intro pid rp hrp hef htrue hpid
  have ⟨p, hp₁, h_id, h_eff, h_eval⟩ := List.forall₂_implies_all_right h₁ rp hrp
  exists p
  and_intros
  · exact hp₁
  · exact h_eff ▸ hef
  · replace htrue : Spec.evaluate p.toExpr req es = .ok (.prim (.bool true)) := by
      replace ⟨_, htrue⟩ : ∃ ty, rp.residual = .val true ty := by
        simp only [Residual.isTrue] at htrue; grind
      simp only [htrue, Residual.evaluate] at h_eval
      exact to_option_left_ok' h_eval
    simp only [satisfied, decide_eq_true_eq]
    exact htrue
  · exact h_id ▸ hpid

theorem partial_authorize_satisfied_forbids_is_sound
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  response.satisfiedForbids ⊆ Spec.satisfiedPolicies .forbid policies req es
:= by
  intro h₁ h₂
  simp only [TPE.isAuthorized] at h₁
  cases h₃ : isAuthorized.evaluatePolicies schema policies preq pes <;>
    simp [h₃] at h₁
  subst h₁
  simp only [isAuthorizedFromResiduals]
  exact partial_authorize_satisfied_policies_is_sound .forbid (evaluatePolicies_residuals_equiv h₂ h₃)

theorem partial_authorize_satisfied_permits_is_sound
  {schema : Schema}
  {policies : List Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  isValidAndConsistent schema req es preq pes = Except.ok () →
  response.satisfiedPermits ⊆ Spec.satisfiedPolicies .permit policies req es
:= by
  intro h₁ h₂
  simp only [TPE.isAuthorized] at h₁
  cases h₃ : isAuthorized.evaluatePolicies schema policies preq pes <;>
    simp [h₃] at h₁
  subst h₁
  simp only [isAuthorizedFromResiduals]
  exact partial_authorize_satisfied_policies_is_sound .permit (evaluatePolicies_residuals_equiv h₂ h₃)
