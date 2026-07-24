import Cedar.Spec
import Cedar.Frontend.Cst
import Cedar.Frontend.Cst.ToAst
import Cedar.Slice.PolicySlice

namespace Cedar.Slice.Cst

open Cedar.Spec
open Cedar.Frontend
open Cedar.Frontend.Cst hiding Expr ExprImpl ExprData OrExpr AndExpr AddExpr MultExpr Name Policy PolicyImpl Policies Ident Literal Primary Member MemAccess Unary Relation RelOp Cond VariableDef Ref RecInit Str


-- Returns true if a `VariableDef` is well-formed.
def varBoundWF (vd : Cst.VariableDef) : Bool :=
  match vd.entityType, vd.ineq with
  | none,   some (.rEq, e) => (e.toEntityUID?).isSome
  | none,   some (.rIn, e) => (e.toEntityUID?).isSome
  | some _, some (.rIn, e) => (e.toEntityUID?).isSome
  | _, _ => true

-- Extracts the principal and resource `VariableDef` from a CST Policy.
-- Returns none if the scopes are out of order or missing.
def prVars? (policy : Cst.Policy) : Option (Cst.VariableDef × Cst.VariableDef) :=
  match policy with
  | .policy p => match p.vars with
    | [pr, act, res] =>
      match pr.var, act.var, res.var with
      | .idPrincipal, .idAction, .idResource =>
        if varBoundWF pr && varBoundWF res then some (pr, res) else none
      | _, _, _ => none
    | _ => none

-- Get the variable bound from a `VariableDef`.
def varBound? (vd : Cst.VariableDef) : Option EntityUID :=
  match vd.entityType, vd.ineq with
  | none,   some (.rEq, e) => e.toEntityUID?   -- principal == e
  | none,   some (.rIn, e) => e.toEntityUID?   -- principal in e
  | some _, some (.rIn, e) => e.toEntityUID?   -- principal is _ in e
  | _, _ => none

-- Given a CST Policy and a proof term that the extraction of the
-- principal and resource `VariableDef` is successful, a `BoundAnalysis`
-- computes the `PolicyBound`.
abbrev BoundAnalysis := (policy : Cst.Policy) → (prVars? policy).isSome → PolicyBound

-- A bound-based slicing algorithm takes as input a bound analysis, request,
-- entities, policies, and a hypothesis that the principal and resourse
-- `VariableDef`s can be extracted from all policies,
-- and filters out the policies whose bound is not satisfied by the
-- request and entities.
def BoundAnalysis.slice (ba : BoundAnalysis) (request : Request) (entities : Entities)
    (policies : Cst.Policies)
    (h : ∀ policy ∈ policies.ps, (prVars? policy).isSome) : Cst.Policies :=
  { ps := policies.ps.attach.filterMap (fun ⟨policy, hmem⟩ =>
      if satisfiedBound (ba policy (h policy hmem)) request entities then some policy else none) }

-- Scope-based analysis extracts the bound from the policy.
def scopeAnalysis (policy : Cst.Policy) (h : (prVars? policy).isSome) : PolicyBound :=
  let (pr, res) := (prVars? policy).get h
  { principalBound := varBound? pr,
    resourceBound  := varBound? res }

end Cedar.Slice.Cst
