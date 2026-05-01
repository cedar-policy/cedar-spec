import Cedar.TPE.Input
import Cedar.TPE.BatchedEvaluator
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Validation
import Cedar.Thm.TPE
import Cedar.Thm.Authorization
import Cedar.Thm.BatchedEvaluator.Common

/-!
Soundness of batched authorization: if the batched authorizer reaches a
definitive decision, that decision agrees with the concrete authorizer.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm
open Cedar.Data

theorem evaluatePolicy_ok_implies_env_some {schema : Schema} {p : Policy}
  {preq : PartialRequest} {pes : PartialEntities} {r : Residual} :
  evaluatePolicy schema p preq pes = .ok r →
  ∃ env, schema.environment? preq.principal.ty preq.resource.ty preq.action = .some env
:= by
  intro h
  simp only [evaluatePolicy] at h
  split at h <;> grind

private theorem requestIsValid_asPartialRequest_eq {env : TypeEnv} {req : Request} :
  requestIsValid env req.asPartialRequest = instanceOfRequestType req env
:= by
  simp only [requestIsValid, Request.asPartialRequest, PartialEntityUID.asEntityUID,
    partialIsValid, Option.map_some, Option.getD_some, instanceOfRequestType]

theorem evaluatePolicy_ok_implies_requestMatchesEnvironment
  {schema : Schema} {p : Policy} {req : Request} {r : Residual} :
  evaluatePolicy schema p req.asPartialRequest Map.empty = .ok r →
  ∀ env, schema.environment? req.asPartialRequest.principal.ty req.asPartialRequest.resource.ty req.asPartialRequest.action = .some env →
  requestMatchesEnvironment env req
:= by
  intro h env h_env
  simp only [evaluatePolicy, h_env] at h
  split at h <;> try cases h
  rename_i h_valid
  simp only [requestAndEntitiesIsValid, Bool.and_eq_true] at h_valid
  simp only [requestMatchesEnvironment, ← requestIsValid_asPartialRequest_eq]
  exact h_valid.1

/--
If `evaluatePolicy` succeeds on a concrete request, and the schema and entities
pass validation, then `InstanceOfWellFormedEnvironment` holds for the
environment determined by the schema and request.
-/
theorem evaluatePolicy_ok_implies_well_formed_env
  {schema : Schema} {p : Policy} {req : Request} {es : Entities} {r : Residual} :
  evaluatePolicy schema p req.asPartialRequest Map.empty = .ok r →
  schema.validateWellFormed = .ok () →
  validateEntities schema es = .ok () →
  ∃ env,
    schema.environment? req.asPartialRequest.principal.ty req.asPartialRequest.resource.ty req.asPartialRequest.action = .some env ∧
    InstanceOfWellFormedEnvironment req es env
:= by
  intro h_ep h_schema_wf h_entities
  obtain ⟨env, h_env⟩ := evaluatePolicy_ok_implies_env_some h_ep
  have h_mem := environment_some_mem_environments h_env
  exact ⟨env, h_env, instance_of_well_formed_env
    (List.forM_ok_implies_all_ok _ _ h_schema_wf _ h_mem)
    (evaluatePolicy_ok_implies_requestMatchesEnvironment h_ep env h_env)
    (List.forM_ok_implies_all_ok _ _ h_entities _ h_mem)⟩

def ResidualPoliciesEquivAndWellTyped
  (env : TypeEnv)
  (policies : List Policy)
  (residuals : List ResidualPolicy)
  (req : Request)
  (es : Entities) : Prop :=
  List.Forall₂ (λ p rp =>
    rp.id = p.id ∧
    rp.effect = p.effect ∧
    (rp.residual.evaluate req es).toOption = (Spec.evaluate p.toExpr req es).toOption ∧
    Residual.WellTyped env rp.residual
  ) policies residuals

theorem equiv_well_typed_implies_equiv
  (h : ResidualPoliciesEquivAndWellTyped env policies residuals req es) :
  ResidualPoliciesEquiv policies residuals req es :=
  List.Forall₂.imp (fun _ _ ⟨a, b, c, _⟩ => ⟨a, b, c⟩) h

theorem residuals_equiv_preserved
  {env : TypeEnv} {policies : List Policy} {residuals : List ResidualPolicy}
  {req : Request} {es : Entities} {pes : PartialEntities}
  (h_sound : ResidualPoliciesEquivAndWellTyped env policies residuals req es)
  (h_wf : InstanceOfWellFormedEnvironment req es env)
  (h_ref : RequestAndEntitiesRefine req es req.asPartialRequest pes) :
  ResidualPoliciesEquivAndWellTyped env policies
    (residuals.map λ rp => ⟨rp.id, rp.effect, Cedar.TPE.evaluate rp.residual req.asPartialRequest pes⟩)
    req es
:= by
  unfold ResidualPoliciesEquivAndWellTyped at *
  rw [← List.map_id policies]
  exact List.map_preserves_forall₂ (fun p rp ⟨h_id, h_eff, h_eval, h_wt⟩ =>
    ⟨h_id, h_eff,
     by rw [← partial_evaluate_is_sound h_wt h_wf h_ref]; exact h_eval,
     partial_eval_preserves_well_typed h_wf h_ref h_wt⟩
  ) h_sound

theorem batched_authorize_loop_decision_agrees
  {policies : List Policy} {residuals : List ResidualPolicy} {req : Request}
  (es : Entities) {current_store : PartialEntities} {env : TypeEnv} {d : Decision} :
  EntityLoader.WellBehaved es loader →
  ResidualPoliciesEquivAndWellTyped env policies residuals req es →
  RequestAndEntitiesRefine req es req.asPartialRequest current_store →
  InstanceOfWellFormedEnvironment req es env →
  (batchedAuthorizeLoop residuals req loader current_store iters).decision = some d →
  (Spec.isAuthorized req es policies).decision = d
:= by
  intro h₀ h₁ h₂ h₃ h_dec
  unfold batchedAuthorizeLoop at h_dec
  simp only at h_dec
  split at h_dec
  case isTrue =>
    exact residuals_decision_agrees (equiv_well_typed_implies_equiv h₁) h_dec
  case isFalse =>
    cases iters with
    | zero =>
      exact residuals_decision_agrees (equiv_well_typed_implies_equiv h₁) h_dec
    | succ n =>
      have h₆ : RequestAndEntitiesRefine req es req.asPartialRequest
        (((loader
          (Set.filter (fun uid => (Map.find? current_store uid).isNone)
            (List.mapUnion (fun rp => rp.residual.allLiteralUIDs) residuals))).mapOnValues
            MaybeEntityData.asPartial) ++ current_store) := by
        constructor
        · exact as_partial_request_refines
        · apply entities_refine_append
          · exact h₂.right
          · exact (h₀ _).2
      exact batched_authorize_loop_decision_agrees es h₀
        (residuals_equiv_preserved h₁ h₃ h₆) h₆ h₃ h_dec

theorem evaluatePolicies_equiv_and_well_typed
  {schema : Schema} {policies : List Policy} {rps : List ResidualPolicy}
  {req : Request} {es : Entities} {preq : PartialRequest}
  {pes : PartialEntities} {env : TypeEnv} :
  List.Forall₂ (λ p rp => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes = .ok rp) policies rps →
  schema.environment? preq.principal.ty preq.resource.ty preq.action = .some env →
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  ResidualPoliciesEquivAndWellTyped env policies rps req es
:= by
  intro h_mapM h_schema_env h_wf h_ref
  unfold ResidualPoliciesEquivAndWellTyped
  apply List.Forall₂.imp _ h_mapM
  intro p rp h
  cases h_ep : evaluatePolicy schema p preq pes <;> simp only [h_ep, Except.map_error, reduceCtorEq] at h
  simp only [Except.map_ok, Except.ok.injEq] at h
  subst h
  refine ⟨rfl, rfl, (partial_evaluate_policy_is_sound h_ep h_schema_env h_wf h_ref).symm, ?_⟩
  simp only [evaluatePolicy, h_schema_env, List.empty_eq] at h_ep
  split at h_ep <;> try cases h_ep
  cases hcheck : Except.mapError Error.invalidPolicy (checkEntities schema p.toExpr) <;>
    simp only [hcheck, Except.bind_err, reduceCtorEq] at h_ep
  simp only [Except.bind_ok, do_ok_eq_ok, Prod.exists, exists_and_right] at h_ep
  rcases h_ep with ⟨_, ⟨_, h₁₁⟩, h₁₂⟩
  simp only [Except.mapError] at h₁₁
  split at h₁₁ <;> try cases h₁₁
  rename_i ty _ _ heq₂
  subst h₁₂
  exact partial_eval_preserves_well_typed h_wf h_ref
    (conversion_preserves_typedness (typechecked_is_well_typed_after_lifting heq₂))

end Cedar.Thm
