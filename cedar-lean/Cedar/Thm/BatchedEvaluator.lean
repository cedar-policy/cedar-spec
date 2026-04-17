import Cedar.Thm.BatchedEvaluator.Evaluate
import Cedar.Thm.BatchedEvaluator.Authorize

namespace Cedar.Thm

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
theorem batched_eval_eq_evaluate
  {x : TypedExpr}
  {req : Request}
  {es : Entities}
  {env : TypeEnv} :
  EntityLoader.WellBehaved es loader →
  TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvaluate x req loader iters) req es).toOption = (evaluate x.toExpr req es).toOption := by
  simp only [batchedEvaluate]
  intro h₁ h₂ h₃
  have h₄ := (direct_request_and_entities_refine req es)

  have h₅ : Residual.WellTyped env (TypedExpr.toResidual x) := by {
    apply conversion_preserves_typedness
    exact h₂
  }
  rw [conversion_preserves_evaluation x req es]
  rw [partial_evaluate_is_sound h₅ h₃ h₄]

  have h₆ : Residual.WellTyped env (TPE.evaluate x.toResidual req.asPartialRequest Map.empty) := by
    apply partial_eval_preserves_well_typed h₃ _ h₅
    . constructor
      . apply as_partial_request_refines
      . apply any_refines_empty_entities
  have h₇: RequestAndEntitiesRefine req es req.asPartialRequest Map.empty := by
    constructor
    . apply as_partial_request_refines
    . apply any_refines_empty_entities

  rw [batched_evaluate_loop_eq_evaluate es h₁ h₆ h₇ h₃]
  rw [←partial_evaluate_is_sound h₅ h₃ h₇]
  rw [←partial_evaluate_is_sound h₅ h₃ h₄]

/--
The main correctness theorem for batched authorization:
If the batched authorizer reaches a definitive decision, that decision
agrees with the concrete authorizer.
-/
theorem batched_authorize_decision_eq_authorize
  {schema : Schema} {policies : List Policy} {req : Request}
  {es : Entities} {response : TPE.Response} {d : Decision} {env : TypeEnv} :
  EntityLoader.WellBehaved es loader →
  batchedAuthorize schema policies req loader iters = .ok response →
  schema.environment? req.asPartialRequest.principal.ty req.asPartialRequest.resource.ty req.asPartialRequest.action = .some env →
  InstanceOfWellFormedEnvironment req es env →
  response.decision = some d →
  (Spec.isAuthorized req es policies).decision = d
:= by
  intro h_loader h_batched h_schema_env h_wf h_dec
  simp only [batchedAuthorize] at h_batched
  cases h_mapM : policies.mapM (λ p =>
    ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p req.asPartialRequest Map.empty) with
  | error e => simp [h_mapM, bind_pure_comp] at h_batched
  | ok residualPolicies =>
    simp only [bind_pure_comp, h_mapM, Except.map_ok, Except.ok.injEq] at h_batched
    subst h_batched
    rw [List.mapM_ok_iff_forall₂] at h_mapM
    have h_ref : RequestAndEntitiesRefine req es req.asPartialRequest Map.empty :=
      ⟨as_partial_request_refines, any_refines_empty_entities⟩
    have h_sound := evaluatePolicies_equiv_and_well_typed h_mapM h_schema_env h_wf h_ref
    exact batched_authorize_loop_decision_agrees es h_loader h_sound h_ref h_wf h_dec
