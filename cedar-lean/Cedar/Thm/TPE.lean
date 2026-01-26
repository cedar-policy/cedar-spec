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
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.Authorization

/-!
This file defines the main theorem of TPE soundness and its associated lemmas.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

/-- The main lemma: Evaluating a residual derived from partially evaluating
a well-typed expression is equivalent to that of evaluating the original
expression, provided that requests and entities are consistent. The equivalency
is defined using `Except.toOption`.
-/
theorem partial_evaluate_is_sound
  {x : Residual}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {env : TypeEnv} :
  Residual.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  (x.evaluate req es).toOption = ((Cedar.TPE.evaluate x preq pes).evaluate req es).toOption
:= by
  intro h₁ h₂ h₃
  induction h₁
  case val =>
    exact partial_evaluate_is_sound_val
  case var =>
    exact partial_evaluate_is_sound_var h₃
  case ite x₁ x₂ x₃ hwt _ _ hₜ _ hᵢ₁ hᵢ₂ hᵢ₃ =>
    exact partial_evaluate_is_sound_ite h₂ hwt hₜ hᵢ₁ hᵢ₂ hᵢ₃
  case and x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    exact partial_evaluate_is_sound_and h₂ h₃ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆
  case or x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    exact partial_evaluate_is_sound_or h₂ h₃ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆
  case unaryApp op₁ x₁ ty hᵢ₁ =>
    exact partial_evaluate_is_sound_unary_app hᵢ₁
  case binaryApp op₂ x₁ x₂ ty _ hwt howt hᵢ₁ hᵢ₂ =>
    exact partial_evaluate_is_sound_binary_app h₂ h₃ hwt howt hᵢ₁ hᵢ₂
  case hasAttr_entity ety x₁ attr hᵢ₁ =>
    exact partial_evaluate_is_sound_has_attr h₃ hᵢ₁
  case hasAttr_record rty x₁ attr hᵢ₁ =>
    exact partial_evaluate_is_sound_has_attr h₃ hᵢ₁
  case getAttr_entity ety rty x₁ attr ty hᵢ₁ =>
    exact partial_evaluate_is_sound_get_attr h₃ hᵢ₁
  case getAttr_record rty x₁ attr ty hᵢ₁ =>
    exact partial_evaluate_is_sound_get_attr h₃ hᵢ₁
  case set ls ty hᵢ₁ =>
    exact partial_evaluate_is_sound_set hᵢ₁
  case record rty m hᵢ₁ hᵢ₁ =>
    exact partial_evaluate_is_sound_record hᵢ₁
  case call xfn args ty hᵢ₁ =>
    exact partial_evaluate_is_sound_call hᵢ₁
  case error ty =>
    exact partial_evaluate_is_sound_error

/-- The main theorem of TPE: Evaluating a result residual is equivalent to
evaluating the input policy, given valid and consistent requests and entities.
The equivalence is w.r.t authorization results. That is, the evaluation results
are strictly equal when they are `.ok` or both errors (captured by
`Except.toOption`). We do not care if the error types match because they do not
impact authorization results. As a matter of fact, they do not match because all
errors encountered during TPE are represented by an `error` residual, whose
interpretation always produces an `extensionError`.
-/
theorem partial_evaluate_policy_is_sound
  {schema : Schema}
  {residual : Residual}
  {policy : Policy}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities} :
  evaluatePolicy schema policy preq pes = .ok residual   →
  isValidAndConsistent schema req es preq pes = .ok () →
  (Spec.evaluate policy.toExpr req es).toOption = (Residual.evaluate residual req es).toOption
:= by
  intro h₁ h₂
  have h₃ := consistent_checks_ensure_refinement h₂
  simp [evaluatePolicy] at h₁
  split at h₁ <;> try cases h₁
  split at h₁ <;> try cases h₁
  simp [do_ok_eq_ok] at h₁
  rcases h₁ with ⟨_, ⟨_, h₁₁⟩, h₁₂⟩
  simp [Except.mapError] at h₁₁
  split at h₁₁ <;> try cases h₁₁
  rename_i env heq₁ _ ty _ _ heq₂
  simp [isValidAndConsistent] at h₂
  split at h₂ <;> try cases h₂
  rename_i heq₃
  simp [heq₁] at heq₃
  subst heq₃
  have ⟨h₂₁, h₂₂⟩ := do_eq_ok₂ h₂
  simp only [isValidAndConsistent.requestIsConsistent, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.and_eq_true, decide_eq_true_eq] at h₂₁
  split at h₂₁ <;> try cases h₂₁
  rename_i heq₃
  simp only [not_or, Bool.not_eq_false] at heq₃
  rcases heq₃ with ⟨_, heq₃⟩
  simp only [isValidAndConsistent.entitiesIsConsistent, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h₂₂
  split at h₂₂ <;> try cases h₂₂
  rename_i heq₄
  simp only [not_or, Bool.not_eq_false] at heq₄
  rcases heq₄ with ⟨_, heq₄⟩
  simp [Except.isOk, Except.toBool] at heq₄
  split at heq₄ <;> cases heq₄
  rename_i heq₄
  simp only [bind, Except.bind, isValidAndConsistent.envIsWellFormed, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h₂₂
  split at h₂₂ <;> try cases h₂₂
  simp only [ite_eq_right_iff, reduceCtorEq, imp_false, Bool.not_eq_false] at h₂₂
  have heq₅ := h₂₂
  simp [Except.isOk, Except.toBool] at heq₅
  split at heq₅ <;> cases heq₅
  rename_i heq₅
  have h₄ := instance_of_well_formed_env heq₅ heq₃ heq₄
  have h₅ := typechecked_is_well_typed_after_lifting heq₂
  let old_residual := (TypedExpr.toResidual ty.liftBoolTypes)

  have h₉ : Residual.WellTyped env old_residual := by {
    have h := conversion_preserves_typedness h₅
    exact h
  }
  have h₆ := partial_evaluate_is_sound h₉ h₄ h₃
  subst h₁₂
  have h₇ := type_of_preserves_evaluation_results (empty_capabilities_invariant req es) h₄ heq₂
  have h₈ : Spec.evaluate (substituteAction env.reqty.action policy.toExpr) req es = Spec.evaluate policy.toExpr req es := by
    simp [InstanceOfWellFormedEnvironment] at h₄
    rcases h₄ with ⟨_, h₄, _⟩
    simp [InstanceOfRequestType] at h₄
    rcases h₄ with ⟨_, h₄, _⟩
    rw [←h₄]
    exact substitute_action_preserves_evaluation policy.toExpr req es
  simp [h₈] at h₇
  rw [h₇, type_lifting_preserves_expr]
  rw [← h₆]
  subst old_residual
  congr
  apply conversion_preserves_evaluation

/-- Re-authorization soundness: The result of reauthorizing a partial
authorization response with concrete request and entities is equivalent to
directly authorizing with the concrete request and entities.
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
  cases h_auth₁ : List.mapM (fun p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;> simp [h_auth₁] at h_auth
  rename_i residuals
  subst h_auth

  rw [List.mapM_ok_iff_forall₂] at h_auth₁
  have h_auth₂ := List.forall₂_implies_all_left h_auth₁
  replace h_auth₁ := List.forall₂_implies_all_right h_auth₁

  have equiv_satisfied : ∀ effect,
    TPE.Response.reauthorize.satisfiedPolicies effect residuals req es =
    Spec.satisfiedPolicies effect policies req es := by
    intro effect
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

  have equiv_errors :
    TPE.Response.reauthorize.errorPolicies residuals req es =
    Spec.errorPolicies policies req es := by
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

  simp [TPE.isAuthorized.isAuthorizedFromResiduals, Response.reauthorize, Spec.isAuthorized,
        equiv_satisfied .forbid, equiv_satisfied .permit, equiv_errors]

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
  (response.decision = some decision → (Spec.isAuthorized req es policies).decision = decision)
:= by
  intro h₁ h₂
  simp [TPE.isAuthorized] at h₁
  cases h₃ : List.mapM (fun p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;> simp [h₃] at h₁
  rename_i rps

  rw [List.mapM_ok_iff_forall₂] at h₃
  have h₄ := List.forall₂_implies_all_left h₃
  replace h₃ := List.forall₂_implies_all_right h₃

  simp [isAuthorized.isAuthorizedFromResiduals] at h₁
  split at h₁ <;> simp [←h₁]
  all_goals
   intro h₅
   subst h₅
  · have ⟨rp, ty, hf₁, hf₂, hf₅⟩ :
      ∃ (rp : ResidualPolicy) (ty : CedarType),
        rp ∈ rps ∧
        rp.effect = .forbid ∧
        rp.residual = .val (.prim (.bool true)) ty
    := by
      have hf : ¬ (isAuthorized.satisfiedPolicies .forbid rps).isEmpty := by grind
      rw [Set.non_empty_iff_exists] at hf
      replace ⟨_, hf⟩ := hf
      simp [isAuthorized.satisfiedPolicies] at hf
      rw [←Set.make_mem] at hf
      simp [List.mem_filterMap] at hf
      simp [ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied, Residual.isTrue] at hf
      have ⟨rp, hf₁, ⟨ hf₂, hf₃⟩, hf₄⟩ := hf ; clear hf
      split at hf₃ <;> try contradiction
      rename_i hf₅
      exists rp
      simp [hf₁, hf₂, hf₅]

    have ⟨p, hp₁, hp₂, hp₃⟩ :
      ∃ (p : Policy),
        p ∈ policies ∧
        p.effect = .forbid ∧
        evaluatePolicy schema p preq pes = .ok (.val (.prim (.bool true)) ty)
    := by
      have ⟨p, hp₁, hp₂⟩ := h₃ rp hf₁
      cases hp₃ : evaluatePolicy schema p preq pes <;>
       simp only [hp₃, Except.map_error, Except.map_ok, reduceCtorEq, Except.ok.injEq] at hp₂
      subst hp₂
      subst hf₅
      exists p

    apply forbid_trumps_permit
    exists p
    and_intros
    · exact hp₁
    · exact hp₂
    · have ha := partial_evaluate_policy_is_sound hp₃ h₂
      simp only [Residual.evaluate] at ha
      simpa [satisfied] using to_option_right_ok' ha
  · have hp :
      ∀ rp ∈ rps,
       rp.effect = .permit →
       ∃ ty,
       rp.residual = .val (.prim (.bool false)) ty ∨
       rp.residual = .error ty
    := by
      intro rp
      intro hr₁ hr₂
      have hp₁ : (isAuthorized.satisfiedPolicies .permit rps).isEmpty := by grind
      have hp₂ : (isAuthorized.residualPolicies .permit rps).isEmpty := by grind
      simp [Set.empty_iff_not_exists] at hp₁ hp₂
      simp [isAuthorized.satisfiedPolicies] at hp₁
      simp [isAuthorized.residualPolicies] at hp₂
      simp [←Set.make_mem] at hp₁ hp₂
      simp [ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied, Residual.isTrue] at hp₁
      simp [ResidualPolicy.residualWithEffect, ResidualPolicy.isResidual, ResidualPolicy.satisfied, Residual.isTrue, ResidualPolicy.isFalse, Residual.isFalse, ResidualPolicy.hasError, Residual.isError] at hp₂
      grind

    apply default_deny
    simp [IsExplicitlyPermitted, HasSatisfiedEffect, satisfied]
    intro p hp₁ hp₂ h

    replace ⟨rp, h₅, h₄⟩ := h₄ p hp₁
    cases he : evaluatePolicy schema p preq pes <;>
     simp [he] at h₄

    rename_i r
    replace ⟨_, hp⟩ :
      ∃ ty,
      r = Residual.val (Value.prim (Prim.bool false)) ty ∨
      r = Residual.error ty
    := by
      specialize hp rp h₅
      rw [←h₄] at hp
      specialize hp hp₂
      simpa using hp

    have ha : r.evaluate req es = Except.ok (Value.prim (Prim.bool true)) :=
      to_option_left_ok (partial_evaluate_policy_is_sound he h₂) h

    cases hp
    · rename_i hp
      simp only at hp
      simp [hp, Residual.evaluate] at ha
    · rename_i hp
      subst hp
      simp [Residual.evaluate] at ha
  · have ⟨rp, ty, hf₁, hf₂, hf₅⟩ :
      ∃ (rp : ResidualPolicy) (ty : CedarType),
        rp ∈ rps ∧
        rp.effect = .permit ∧
        rp.residual = .val (.prim (.bool true)) ty
    := by
      have hf : ¬ (isAuthorized.satisfiedPolicies .permit rps).isEmpty := by grind
      rw [Set.non_empty_iff_exists] at hf
      replace ⟨_, hf⟩ := hf
      simp [isAuthorized.satisfiedPolicies] at hf
      rw [←Set.make_mem] at hf
      simp [List.mem_filterMap] at hf
      simp [ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied, Residual.isTrue] at hf
      have ⟨rp, hf₁, ⟨ hf₂, hf₃⟩, hf₄⟩ := hf ; clear hf
      split at hf₃ <;> try contradiction
      rename_i hf₅
      exists rp
      simp [hf₁, hf₂, hf₅]

    have hp :
      ∀ rp ∈ rps,
       rp.effect = .forbid →
       ∃ ty,
       rp.residual = .val (.prim (.bool false)) ty ∨
       rp.residual = .error ty
    := by
      intro rp
      intro hr₁ hr₂
      have hp₁ : (isAuthorized.satisfiedPolicies .forbid rps).isEmpty := by grind
      have hp₂ : (isAuthorized.residualPolicies .forbid rps).isEmpty := by grind
      simp [Set.empty_iff_not_exists] at hp₁ hp₂
      simp [isAuthorized.satisfiedPolicies] at hp₁
      simp [isAuthorized.residualPolicies] at hp₂
      simp [←Set.make_mem] at hp₁ hp₂
      simp [ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied, Residual.isTrue] at hp₁
      simp [ResidualPolicy.residualWithEffect, ResidualPolicy.isResidual, ResidualPolicy.satisfied, Residual.isTrue, ResidualPolicy.isFalse, Residual.isFalse, ResidualPolicy.hasError, Residual.isError] at hp₂
      grind

    -- There is at least one satisfied permit. Use this to show `(satisfiedPolicies Effect.permit policies req es).isEmpty = false`
    -- There are no satisfied or residual forbids. Use this to show `(satisfiedPolicies Effect.forbid policies req es).isEmpty = true`
    -- This implies the concrete decision is allow.
    sorry

theorem partial_authorize_satisfied_permits_is_sound
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
  response.decision = some .allow →
  response.satisfiedPermits ⊆ (Spec.isAuthorized req es policies).determiningPolicies
:= by
   intro h₁ h₂
   simp [TPE.isAuthorized] at h₁
   cases h₃ : List.mapM (fun p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;> simp [h₃] at h₁
   rename_i rps

   simp [isAuthorized.isAuthorizedFromResiduals] at h₁
   split at h₁ <;> simp [←h₁]
   rw [List.mapM_ok_iff_forall₂] at h₃
   have h₄ := List.forall₂_implies_all_left h₃
   replace h₃ := List.forall₂_implies_all_right h₃

   simp [isAuthorized.satisfiedPolicies]
   simp [Spec.isAuthorized]
   split <;> simp [satisfiedPolicies]
   · sorry
   · sorry

-- theorem partial_authorize_is_sound
--   {schema : Schema}
--   {policies : List Policy}
--   {req : Request}
--   {es : Entities}
--   {preq : PartialRequest}
--   {pes : PartialEntities}
--   {response : TPE.Response}
--   {decision : Decision} :
--   TPE.isAuthorized schema policies preq pes = Except.ok response →
--   isValidAndConsistent schema req es preq pes = Except.ok () →
--   (response.errorForbids ∪ response.errorPermits) ⊆ (Spec.isAuthorized req es policies).erroringPolicies ∧
--   (response.decision = some decision → (Spec.isAuthorized req es policies).decision = decision) ∧
--   (response.decision = some .allow → response.satisfiedPermits ⊆ (Spec.isAuthorized req es policies).determiningPolicies) ∧
--   (response.decision = some .deny → response.satisfiedForbids ⊆ (Spec.isAuthorized req es policies).determiningPolicies) ∧
--   (response.satisfiedForbids ⊆ (Spec.isAuthorized req es policies).determiningPolicies ∨ response.satisfiedPermits ⊆ (Spec.isAuthorized req es policies).determiningPolicies)
-- := by
--   intro h₁ h₂
--   simp [TPE.isAuthorized] at h₁
--   cases h₃ : List.mapM (fun p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;> simp [h₃] at h₁
--   rename_i rps
--
--   simp [isAuthorized.isAuthorizedFromResiduals] at h₁
--   split at h₁ <;> simp [←h₁]
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--
--   subst h₁
--
--   rw [List.mapM_ok_iff_forall₂] at h₃
--   have h₄ := List.forall₂_implies_all_left h₃
--   replace h₃ := List.forall₂_implies_all_right h₃
--
--
--
--
--
--   sorry

end Cedar.Thm
