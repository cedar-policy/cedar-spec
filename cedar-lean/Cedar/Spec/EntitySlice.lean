import Cedar.Data
import Cedar.Spec.Expr
import Cedar.Spec.Request
import Cedar.Spec.Entities

namespace Cedar.Spec
open Cedar.Data
open Cedar.Spec

def Prim.findEuids (p : Prim) : List EntityUID :=
  match p with
  | .bool _ => []
  | .int _ => []
  | .string _ => []
  | .entityUID euid => [euid]




def Value.findEuids (value : Value) : List EntityUID :=
  match value with
  | .prim p => p.findEuids
  | .set members =>
    (members.toList.map₁ (λ pair => pair.val.findEuids ) ).join
  | .record members => (members.values.map₁  (λ pair => pair.val.findEuids)).join
  | .ext _ => []
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  case _ =>
    have step₁ : sizeOf (members.toList) < sizeOf members := by
      cases members
      rename_i members
      simp [Set.toList, Set.elts]
      omega
    have step₂ : sizeOf pair.val < sizeOf members.toList := by
      apply List.in_lists_means_smaller
      apply pair.property
    omega
  case _ =>
    have step₁ : sizeOf pair.val < sizeOf members := by
      apply Map.sizeOf_lt_of_in_values
      apply pair.property
    omega



def findEuids (context : Map Attr Value) : List EntityUID :=
  (context.values.map Value.findEuids).join

def simpleSlice (req : Request) (entities : Entities) : Option Entities := do
  let p ← entities.find? req.principal
  let a ← entities.find? req.action
  let r ← entities.find? req.resource
  return Map.make ([(req.principal, p), (req.action, a), (req.resource, r)])




end Cedar.Spec
