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
  req.context.WellFormed →
  EntityLoader.WellBehaved env.ets es loader →
  Residual.WellTyped env x →
  RequestAndEntitiesRefine req es (req.asPartialRequest env.reqty.context) current_store →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvaluateLoop env x req loader current_store iters) req es).toOption = (Residual.evaluate x req es).toOption := by
  intro hctxwf h₀ h₁ h₂ h₃
  unfold batchedEvaluateLoop
  split
  case h_1 => simp only
  case h_2 iters n=>
    let toLoad := (Set.filter (fun uid => (Map.find? current_store uid).isNone) x.allLiteralUIDs)
    let newEntities := SlicedEntities.asPartial env.ets (loader toLoad)
    let newStore := newEntities ++ current_store

    have h₆ : RequestAndEntitiesRefine req es (req.asPartialRequest env.reqty.context) newStore := by
      constructor
      · exact as_partial_request_refines hctxwf
      · apply entities_refine_append
        · exact h₂.right
        · exact (h₀ toLoad)
    let newRes := TPE.evaluate env x (req.asPartialRequest env.reqty.context) newStore
    have h₇ : (Residual.evaluate newRes req es).toOption = (Residual.evaluate x req es).toOption := by
      rw [← partial_evaluate_is_sound h₁ h₃ h₆]

    simp only
    split
    case h_1 hval =>
      rw [← hval]
      exact h₇
    case h_2 =>
      have h₈ := (partial_eval_preserves_well_typed h₃ h₆ h₁)
      rw [batched_evaluate_loop_eq_evaluate es hctxwf h₀ h₈ h₆ h₃]
      exact h₇


end Cedar.Thm
