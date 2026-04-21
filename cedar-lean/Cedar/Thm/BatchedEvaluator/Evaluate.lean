import Cedar.TPE.Input
import Cedar.TPE.BatchedEvaluator
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Validation
import Cedar.Thm.TPE
import Cedar.Thm.BatchedEvaluator.Common

/-!
Soundness of batched expression evaluation: batched evaluation of a single
well-typed residual produces the same result as direct evaluation with the
complete entity store.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm
open Cedar.Data

theorem batched_evaluate_loop_eq_evaluate
  {x : Residual}
  {req : Request}
  (es : Entities)
  {current_store : PartialEntities}
  {env : TypeEnv} :
  EntityLoader.WellBehaved es loader →
  Residual.WellTyped env x →
  RequestAndEntitiesRefine req es req.asPartialRequest current_store →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvaluateLoop x req loader current_store iters) req es).toOption = (Residual.evaluate x req es).toOption := by
  intro h₀ h₁ h₂ h₃
  unfold batchedEvaluateLoop
  split
  case h_1 => simp only
  case h_2 iters n=>
    let toLoad := (Set.filter (fun uid => (Map.find? current_store uid).isNone) x.allLiteralUIDs)
    let newEntities := ((loader toLoad).mapOnValues MaybeEntityData.asPartial)
    let newStore := newEntities ++ current_store

    have h₆ : RequestAndEntitiesRefine req es req.asPartialRequest newStore := by
      constructor
      · exact as_partial_request_refines
      · apply entities_refine_append
        · exact h₂.right
        · exact (h₀ toLoad).2
    let newRes := TPE.evaluate x req.asPartialRequest newStore
    have h₇ : (Residual.evaluate newRes req es).toOption = (Residual.evaluate x req es).toOption := by
      rw [← partial_evaluate_is_sound h₁ h₃ h₆]

    simp only
    split
    case h_1 h₆ =>
      rw [← h₆]
      exact h₇
    case h_2 =>
      have h₈ := (partial_eval_preserves_well_typed h₃ h₆ h₁)
      rw [batched_evaluate_loop_eq_evaluate es h₀ h₈ h₆ h₃]
      exact h₇


end Cedar.Thm
