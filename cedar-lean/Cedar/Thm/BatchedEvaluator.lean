import Cedar.TPE.Input
import Cedar.TPE.BatchedEvaluator
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Validation
import Cedar.Thm.TPE

/-!
This file defines theorems related to the batched evaluator.
These proofs need updating for the new RequestRefines/EntitiesRefine signatures
and the rTargetCorrect invariant.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm
open Cedar.Data

abbrev EntityLoader.WellBehaved (env : TypeEnv) (store: Entities) (loader: EntityLoader) : Prop :=
  ∀ s, s ⊆ (loader s).keys ∧
       EntitiesRefine env store ((loader s).mapOnValues MaybeEntityData.asPartial)

theorem as_partial_request_refines {req : Request} {env : TypeEnv} :
  RequestRefines env req req.asPartialRequest := by sorry

theorem any_refines_empty_entities {env : TypeEnv} :
  EntitiesRefine env es Map.empty := by sorry

theorem entities_refine_append {env : TypeEnv} (es : Entities) (m1 m2 : PartialEntities) :
  EntitiesRefine env es m1 → EntitiesRefine env es m2 → EntitiesRefine env es (m2 ++ m1) := by sorry

theorem direct_request_and_entities_refine {env : TypeEnv} (req : Request) (es : Entities) :
  RequestAndEntitiesRefine env req es req.asPartialRequest Map.empty := by sorry

theorem batched_eval_loop_eq_evaluate
  {x : TypedExpr} {req : Request} {es : Entities} {env : TypeEnv}
  {loader : EntityLoader} {store : PartialEntities} {r : Residual} {n : Nat} :
  Cedar.Thm.TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  EntityLoader.WellBehaved env es loader →
  EntitiesRefine env es store →
  Residual.WellTyped env r →
  r.evaluate req es = x.toResidual.evaluate req es →
  (batchedEvalLoop r req loader store n).evaluate req es = x.toResidual.evaluate req es := by sorry

theorem batched_eval_eq_evaluate
  {x : TypedExpr} {req : Request} {es : Entities} {env : TypeEnv}
  {loader : EntityLoader} {n : Nat} :
  Cedar.Thm.TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  EntityLoader.WellBehaved env es loader →
  (batchedEvaluate x req loader n).evaluate req es = x.toResidual.evaluate req es := by sorry

end Cedar.Thm
