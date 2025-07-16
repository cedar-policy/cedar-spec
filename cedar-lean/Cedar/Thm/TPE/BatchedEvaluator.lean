import Cedar.TPE.Input
import Cedar.TPE.BatchedEvaluator
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Validation
import Cedar.Thm.TPE

/-!
This file defines theorems related to the batched evaluator
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm


theorem direct_request_and_entities_refine
  (req : Request)
  (es : Entities) :
  RequestAndEntitiesRefine req es (Request.asPartialRequest req) (Entities.asPartial es) := by
  sorry

theorem batched_eval_loop_eq_evaluate
  {x : TypedExpr}
  {req : Request}
  {es : Entities}
  {current_store : Entities}
  {env : TypeEnv} :
  let loader := entityLoaderFor es
  TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  (batchedEvalLoop x req loader current_store).toOption = (evaluate x.toExpr req es).toOption := by
  sorry



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
  let loader := entityLoaderFor es
  TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  (batchedEvaluate x req loader).toOption = (evaluate x.toExpr req es).toOption := by
  simp [batchedEvaluate]
  intro h₁ h₂
  have h₃ := (direct_request_and_entities_refine req es)
  let first_partial := (TPE.evaluate x (Request.asPartialRequest req) (Entities.asPartial (Data.Map.mk [])))
  have partial_sound := partial_evaluate_is_sound h₁ h₂ h₃
  rw [partial_sound]
  cases (TPE.evaluate x (Request.asPartialRequest req) (Entities.asPartial (Data.Map.mk []))).asTypedExpr with
  | error e =>
    sorry
  | ok v =>
    simp
    
    sorry

end Cedar.Thm
