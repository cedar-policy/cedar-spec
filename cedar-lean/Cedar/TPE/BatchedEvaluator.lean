import Cedar.Spec
import Cedar.Data

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec


def EntityLoader: Type := (Set EntityUID) -> List EntityData



def batched_evaluate
  (x : TypedExpr)
  (req: Request)
  (loader: EntityLoader)
  : Entities
  :=
  sorry
