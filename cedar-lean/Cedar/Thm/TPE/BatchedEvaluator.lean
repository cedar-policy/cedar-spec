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
open Cedar.Data


theorem as_partial_request_refines
  {req: Request}
  : RequestRefines req (Request.asPartialRequest req)
  := by
  dsimp [RequestRefines, Request.asPartialRequest]
  constructor
  . simp [PartialEntityUID.asEntityUID]
    apply PartialIsValid.some
    simp
  . constructor
    simp
    constructor
    all_goals {
      dsimp [PartialEntityUID.asEntityUID]
      apply PartialIsValid.some
      simp
    }

theorem any_refines_empty_entities:
  EntitiesRefine es Data.Map.empty
:= by
  simp [EntitiesRefine]
  intro a e₂ h₁
  simp [Data.Map.empty, Data.Map.find?, Map.kvs] at h₁


theorem direct_request_and_entities_refine
  (req : Request)
  (es : Entities) :
  RequestAndEntitiesRefine req es (Request.asPartialRequest req) (Entities.asPartial es) := by
  sorry




theorem batched_eval_loop_eq_evaluate
  {x : Residual}
  {req : Request}
  (es : Entities)
  {current_store : PartialEntities}
  {env : TypeEnv} :
  let loader := entityLoaderFor es
  Residual.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  (batchedEvalLoop x req loader current_store).toOption = (Residual.evaluate x req es).toOption := by
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
  let first_partial := (TPE.evaluate (TypedExpr.toResidual x) (Request.asPartialRequest req) (Entities.asPartial (Data.Map.mk [])))
  let h₅ : Residual.WellTyped env (TypedExpr.toResidual x) := by {
    apply conversion_preserves_typedness
    exact h₁
  }
  have conversion_sound := conversion_preserves_evaluation x req es
  rw [conversion_sound]
  have partial_sound := partial_evaluate_is_sound h₅ h₂ h₃
  rw [partial_sound]
  rw [batched_eval_loop_eq_evaluate]
  rw [←partial_evaluate_is_sound]
  rw [←partial_evaluate_is_sound]
  exact h₅
  exact h₂
  exact h₃
  exact h₅
  exact h₂
  unfold RequestAndEntitiesRefine
  constructor
  . apply as_partial_request_refines
  . unfold EntitiesRefine
    intro uid
    intro pd
    dsimp [Data.Map.find?, Data.Map.kvs]
    intro h_contra
    contradiction
  . exact env
  case a =>
   apply partial_eval_preserves_well_typed h₂
   . unfold RequestAndEntitiesRefine
     constructor
     . apply as_partial_request_refines
     . apply any_refines_empty_entities
   . exact h₅
  . exact h₂


end Cedar.Thm
