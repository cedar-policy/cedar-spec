import Cedar.Data
import Cedar.Spec.Expr
import Cedar.Spec.Request
import Cedar.Spec.Entities

namespace Cedar.Spec
open Cedar.Data
open Cedar.Spec

def Prim.findEuids (p : Prim) (entities : Entities) : Option (List (EntityUID × EntityData)) :=
  match p with
  | .bool _ => return []
  | .int _ => return []
  | .string _ => return []
  | .entityUID euid => do
    let data ← entities.find? euid
    return [(euid, data)]





def Value.findEuids (value : Value) (entities : Entities) : Option (List (EntityUID × EntityData)):=
  match value with
  | .prim p => p.findEuids entities
  | .set s => do
    let euids ← s.toList.mapM₁ (λ pair => pair.val.findEuids entities)
    return euids.join
  | .record kvs => do
    let euids ← kvs.values.mapM₁ (λ pair => pair.val.findEuids entities)
    return euids.join
  | .ext _ => return []
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  case _ =>
    cases s
    rename_i members
    have step₁ : sizeOf pair.val < sizeOf members := by
      apply List.in_lists_means_smaller
      apply pair.property
    have step₂ : sizeOf members < sizeOf (Set.mk members) := by
      simp
      omega
    omega
  case _ =>
    have step : sizeOf pair.val < sizeOf kvs := by
      apply Map.sizeOf_lt_of_in_values
      apply pair.property
    omega




def loadEuids (context : Map Attr Value) (entities : Entities) : Option (List (EntityUID × EntityData)) := do
  (Value.record context).findEuids entities


def simpleSlice (req : Request) (entities : Entities) : Option Entities := do
  let p ← entities.find? req.principal
  let a ← entities.find? req.action
  let r ← entities.find? req.resource
  let fromContext ← loadEuids req.context entities
  let kvs := (req.principal, p) :: (req.action, a) :: (req.resource, r)  :: fromContext
  return Map.make kvs




end Cedar.Spec
