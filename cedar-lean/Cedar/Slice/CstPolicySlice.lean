import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstToAst
import Cedar.Slice.PolicySlice

namespace Cedar.Slice.Cst

open Cedar.Spec

def varBoundWF (vd : Cst.VariableDef) : Bool :=
  match vd.entityType, vd.ineq with
  | none,   some (.rEq, e) => (e.toEntityUID?).isSome
  | none,   some (.rIn, e) => (e.toEntityUID?).isSome
  | some _, some (.rIn, e) => (e.toEntityUID?).isSome
  | _, _ => true

def prVars? (policy : Cst.Policy) : Option (Cst.VariableDef × Cst.VariableDef) :=
  match policy with
  | .policy p => match p.vars with
    | [pr, act, res] =>
      match pr.var, act.var, res.var with
      | .idPrincipal, .idAction, .idResource =>
        if varBoundWF pr && varBoundWF res then some (pr, res) else none
      | _, _, _ => none
    | _ => none

def varBound? (vd : Cst.VariableDef) : Option EntityUID :=
  match vd.entityType, vd.ineq with
  | none,   some (.rEq, e) => e.toEntityUID?   -- principal == e
  | none,   some (.rIn, e) => e.toEntityUID?   -- principal in e
  | some _, some (.rIn, e) => e.toEntityUID?   -- principal is _ in e
  | _, _ => none

abbrev BoundAnalysis := (policy : Cst.Policy) → (prVars? policy).isSome → PolicyBound

def BoundAnalysis.slice (ba : BoundAnalysis) (request : Request) (entities : Entities)
    (policies : Cst.Policies)
    (h : ∀ policy ∈ policies.ps, (prVars? policy).isSome) : Cst.Policies :=
  { ps := policies.ps.attach.filterMap (fun ⟨policy, hmem⟩ =>
      if satisfiedBound (ba policy (h policy hmem)) request entities then some policy else none) }

def scopeAnalysis (policy : Cst.Policy) (h : (prVars? policy).isSome) : PolicyBound :=
  let (pr, res) := (prVars? policy).get h
  { principalBound := varBound? pr,
    resourceBound  := varBound? res }

end Cedar.Slice.Cst
