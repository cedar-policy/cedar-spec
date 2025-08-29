import Cedar.TPE
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.TPE.WellTypedCases
import Cedar.Thm.Validation.WellTyped.ResidualDefinition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

/-!
This file contains theorems about partial evaluation preserving well-typedness of residuals.
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE


theorem batched_eval_loop_preserves_well_typed
  (loader) (store) (i)
  {env : TypeEnv}
  {res : Residual}
  {req : Request}
  {es : Entities}
  {pes : PartialEntities} :
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es (req.asPartialRequest) pes →
  Residual.WellTyped env res →
  Residual.WellTyped env (batchedEvalLoop res req loader store i)
:= by
  sorry

end Cedar.Thm
