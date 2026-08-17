import Cedar.Thm.BatchedEvaluator.Common
import Cedar.Thm.BatchedEvaluator.Evaluate
import Cedar.Thm.BatchedEvaluator.Authorize

namespace Cedar.Thm

/-!
This file defines the main theorems for batched authorization and evaluation.
-/

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm
open Cedar.Data

/--
The main correctness theorem for batched evaluation:
Batched evaluation with an entity loader produces the same result
as normal evaluation with the complete entity store.
-/
theorem batched_evaluate_eq_evaluate
  {x : TypedExpr}
  {req : Request}
  {es : Entities}
  {env : TypeEnv} :
  EntityLoader.WellBehaved es loader →
  TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvaluate env x req loader iters) req es).toOption = (evaluate x.toExpr req es).toOption := by
  simp only [batchedEvaluate]
  intro h₁ h₂ h₃
  have h₄ := (direct_request_and_entities_refine req es)

  have h₅ : Residual.WellTyped env (TypedExpr.toResidual x) := by {
    apply conversion_preserves_typedness
    exact h₂
  }
  rw [conversion_preserves_evaluation x req es]
  rw [partial_evaluate_is_sound h₅ h₃ h₄]

  have h₇: RequestAndEntitiesRefine req es req.asPartialRequest (actionEntities env.acts) := by
    constructor
    . apply as_partial_request_refines
    . exact actionEntities_refines h₃.1 h₃.2.2
  have h₆ : Residual.WellTyped env
      (TPE.evaluate env x.toResidual req.asPartialRequest (actionEntities env.acts)) :=
    partial_eval_preserves_well_typed h₃ h₇ h₅

  rw [batched_evaluate_loop_eq_evaluate es h₁ h₆ h₇ h₃]
  rw [←partial_evaluate_is_sound h₅ h₃ h₇]
  rw [←partial_evaluate_is_sound h₅ h₃ h₄]

/--
A successful batched authorization returns `isAuthorizedFromResiduals` of a list equivalent to the
policies, so any property of it transfers to the batched path without a second induction.
-/
theorem batched_authorize_ok_equiv
  {schema : Schema} {policies : List Policy} {req : Request}
  {es : Entities} {response : TPE.Response} :
  EntityLoader.WellBehaved es loader →
  schema.validateWellFormed = .ok () →
  validateEntities schema es = .ok () →
  batchedAuthorize schema policies req loader iters = .ok response →
  ∃ rps, response = isAuthorizedFromResiduals rps ∧
    ResidualPoliciesEquiv policies rps req es
:= by
  intro h_loader h_schema_wf h_entities h_batched
  simp only [batchedAuthorize] at h_batched
  cases h_mapM : policies.mapM (λ p =>
    ResidualPolicy.mk p.id p.effect <$>
      evaluatePolicy schema p req.asPartialRequest (actionEntities schema.acts)) with
  | error e => simp [h_mapM, bind_pure_comp] at h_batched
  | ok residualPolicies =>
    -- `batchedAuthorize` looks the type environment up before entering the loop, so there is an
    -- extra case for a request the schema gives no environment to.
    simp only [bind_pure_comp, h_mapM] at h_batched
    split at h_batched
    case h_1 => simp at h_batched
    case h_2 env₀ h_env₀ =>
    simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq] at h_batched
    subst h_batched
    rw [List.mapM_ok_iff_forall₂] at h_mapM
    match policies, h_mapM with
    | [], .nil =>
      -- The empty response already has a decision, so the loop returns at once.
      have h_dec : (isAuthorizedFromResiduals []).decision.isSome = true := by
        simp [isAuthorizedFromResiduals, isAuthorizedFromResiduals.satisfiedPolicies,
          isAuthorizedFromResiduals.residualPolicies]
      refine ⟨[], ?_, .nil⟩
      unfold batchedAuthorizeLoop
      simp only [h_dec, if_true]
    | p :: _, .cons h_first h_rest =>
      have ⟨r, h_ep⟩ : ∃ r,
          evaluatePolicy schema p req.asPartialRequest (actionEntities schema.acts) = .ok r := by
        cases h_ep : evaluatePolicy schema p req.asPartialRequest (actionEntities schema.acts) <;>
          simp [h_ep] at ⊢ h_first
      obtain ⟨env, h_schema_env, h_wf⟩ :=
        evaluatePolicy_ok_implies_well_formed_env h_ep h_schema_wf h_entities
      -- Flip the direction so `subst` eliminates `env₀` and keeps `env`, which the rest of the
      -- proof refers to.
      have h_env_eq : env = env₀ := by
        simp only [Request.asPartialRequest] at h_schema_env
        simp only [h_env₀, Option.some.injEq] at h_schema_env
        exact h_schema_env.symm
      subst h_env_eq
      have h_acts : env.acts = schema.acts :=
        (environment?_schema (by simpa only [Request.asPartialRequest] using h_schema_env)).2
      have h_ref : RequestAndEntitiesRefine req es req.asPartialRequest
          (actionEntities schema.acts) :=
        ⟨as_partial_request_refines, h_acts ▸ actionEntities_refines h_wf.1 h_wf.2.2⟩
      obtain ⟨rps, heq, hequiv⟩ := batched_authorize_loop_equiv es h_loader
        (evaluatePolicies_equiv_and_well_typed (.cons h_first h_rest) h_schema_env h_wf h_ref)
        h_ref h_wf
      exact ⟨rps, heq, equiv_well_typed_implies_equiv hequiv⟩

/--
The main correctness theorem for batched authorization:
If the batched authorizer reaches a definitive decision, that decision
agrees with the concrete authorizer.
-/
theorem batched_authorize_decision_eq_authorize
  {schema : Schema} {policies : List Policy} {req : Request}
  {es : Entities} {response : TPE.Response} {d : Decision} :
  EntityLoader.WellBehaved es loader →
  schema.validateWellFormed = .ok () →
  validateEntities schema es = .ok () →
  batchedAuthorize schema policies req loader iters = .ok response →
  response.decision = some d →
  (Spec.isAuthorized req es policies).decision = d
:= by
  intro h_loader h_schema_wf h_entities h_batched h_dec
  obtain ⟨rps, heq, hequiv⟩ :=
    batched_authorize_ok_equiv h_loader h_schema_wf h_entities h_batched
  rw [heq] at h_dec
  exact residuals_decision_agrees hequiv h_dec

end Cedar.Thm
