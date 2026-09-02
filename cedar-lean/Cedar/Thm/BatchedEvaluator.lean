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
  req.context.WellFormed →
  EntityLoader.WellBehaved env.ets es loader →
  TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvaluate env x req loader iters) req es).toOption = (evaluate x.toExpr req es).toOption := by
  simp only [batchedEvaluate]
  intro hctxwf h₁ h₂ h₃
  have h₄ := (direct_request_and_entities_refine env.ets req es env.reqty.context hctxwf)

  have h₅ : Residual.WellTyped env (TypedExpr.toResidual x) := by {
    apply conversion_preserves_typedness
    exact h₂
  }
  rw [conversion_preserves_evaluation x req es]
  rw [partial_evaluate_is_sound h₅ h₃ h₄]

  have h₇: RequestAndEntitiesRefine req es (req.asPartialRequest env.reqty.context)
      (actionEntities env.acts) := by
    constructor
    . apply as_partial_request_refines hctxwf
    . exact actionEntities_refines h₃.1 h₃.2.2
  have h₆ : Residual.WellTyped env (TPE.evaluate env x.toResidual
      (req.asPartialRequest env.reqty.context) (actionEntities env.acts)) :=
    partial_eval_preserves_well_typed h₃ h₇ h₅

  rw [batched_evaluate_loop_eq_evaluate es hctxwf h₁ h₆ h₇ h₃]
  rw [←partial_evaluate_is_sound h₅ h₃ h₇]
  rw [←partial_evaluate_is_sound h₅ h₃ h₄]

/--
A successful batched authorization returns `isAuthorizedFromResiduals` of a list equivalent to the
policies, so any property of it transfers to the batched path without a second induction.
-/
theorem batched_authorize_ok_equiv
  {schema : Schema} {policies : List Policy} {req : Request}
  {es : Entities} {response : TPE.Response} :
  req.context.WellFormed →
  EntityLoader.WellBehaved schema.ets es loader →
  schema.validateWellFormed = .ok () →
  validateEntities schema es = .ok () →
  batchedAuthorize schema policies req loader iters = .ok response →
  ∃ rps, response = isAuthorizedFromResiduals rps ∧
    ResidualPoliciesEquiv policies rps req es
:= by
  intro hctxwf h_loader h_schema_wf h_entities h_batched
  -- The type environment is looked up before the policies are evaluated, because the partial
  -- request needs the action's context type.
  simp only [batchedAuthorize] at h_batched
  split at h_batched
  case h_1 => simp at h_batched
  case h_2 env h_env₀ =>
  simp only [bind_pure_comp] at h_batched
  cases h_mapM : policies.mapM (λ p =>
    ResidualPolicy.mk p.id p.effect <$>
      evaluatePolicy schema p (req.asPartialRequest env.reqty.context)
        (actionEntities schema.acts)) with
  | error e => simp only [h_mapM, Except.map_error, reduceCtorEq] at h_batched
  | ok residualPolicies =>
    simp only [h_mapM, Except.map_ok, Except.ok.injEq] at h_batched
    subst h_batched
    have h_loader' : EntityLoader.WellBehaved env.ets es loader := by
      rw [environment?_ets h_env₀]; exact h_loader
    rw [List.mapM_ok_iff_forall₂] at h_mapM
    have h_schema_env : schema.environment?
        (req.asPartialRequest env.reqty.context).principal.ty
        (req.asPartialRequest env.reqty.context).resource.ty
        (req.asPartialRequest env.reqty.context).action = .some env := by
      simpa only [Request.asPartialRequest] using h_env₀
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
          evaluatePolicy schema p (req.asPartialRequest env.reqty.context)
            (actionEntities schema.acts) = .ok r := by
        cases h_ep : evaluatePolicy schema p (req.asPartialRequest env.reqty.context)
          (actionEntities schema.acts) <;> simp [h_ep] at ⊢ h_first
      have h_wf :=
        evaluatePolicy_ok_implies_well_formed_env hctxwf h_ep h_schema_env h_schema_wf h_entities
      have h_acts : env.acts = schema.acts := (environment?_schema h_env₀).2
      have h_ref : RequestAndEntitiesRefine req es (req.asPartialRequest env.reqty.context)
          (actionEntities schema.acts) :=
        ⟨as_partial_request_refines hctxwf, h_acts ▸ actionEntities_refines h_wf.1 h_wf.2.2⟩
      obtain ⟨rps, heq, hequiv⟩ := batched_authorize_loop_equiv es hctxwf h_loader'
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
  req.context.WellFormed →
  EntityLoader.WellBehaved schema.ets es loader →
  schema.validateWellFormed = .ok () →
  validateEntities schema es = .ok () →
  batchedAuthorize schema policies req loader iters = .ok response →
  response.decision = some d →
  (Spec.isAuthorized req es policies).decision = d
:= by
  -- #1015 adds the context-well-formedness hypothesis; the rest of the reasoning lives in
  -- `batched_authorize_ok_equiv`.
  intro hctxwf h_loader h_schema_wf h_entities h_batched h_dec
  obtain ⟨rps, heq, hequiv⟩ :=
    batched_authorize_ok_equiv hctxwf h_loader h_schema_wf h_entities h_batched
  rw [heq] at h_dec
  exact residuals_decision_agrees hequiv h_dec

end Cedar.Thm
