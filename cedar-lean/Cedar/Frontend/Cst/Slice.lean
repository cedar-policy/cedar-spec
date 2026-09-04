/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

module

import Cedar.Spec
public import Cedar.Frontend.Cst.Syntax
import Cedar.Frontend.Cst.ToAst
public import Cedar.Slice.PolicySlice

namespace Cedar.Frontend.Cst

open Cedar.Spec
open Cedar.Frontend
open Cedar.Slice

-- Returns true if a `VariableDef` is well-formed.
public def varBoundWF (vd : VariableDef) : Bool :=
  match vd.entityType, vd.ineq with
  | none,   some (.rEq, e) => (e.toEntityUID?).isSome
  | none,   some (.rIn, e) => (e.toEntityUID?).isSome
  | some _, some (.rIn, e) => (e.toEntityUID?).isSome
  | _, _ => true

-- Extracts the principal and resource `VariableDef` from a CST Policy.
-- Returns none if the scopes are out of order or missing.
public def prVars? (policy : Policy) : Option (VariableDef × VariableDef) :=
  match policy with
  | .policy p => match p.vars with
    | [pr, act, res] =>
      match pr.var, act.var, res.var with
      | .idPrincipal, .idAction, .idResource =>
        if varBoundWF pr && varBoundWF res then some (pr, res) else none
      | _, _, _ => none
    | _ => none

-- Get the variable bound from a `VariableDef`.
public def varBound? (vd : VariableDef) : Option EntityUID :=
  match vd.entityType, vd.ineq with
  | none,   some (.rEq, e) => e.toEntityUID?   -- principal == e
  | none,   some (.rIn, e) => e.toEntityUID?   -- principal in e
  | some _, some (.rIn, e) => e.toEntityUID?   -- principal is _ in e
  | _, _ => none

-- Given a CST Policy and a proof term that the extraction of the
-- principal and resource `VariableDef` is successful, a `BoundAnalysis`
-- computes the `PolicyBound`.
public abbrev BoundAnalysis := (policy : Policy) → (prVars? policy).isSome → PolicyBound

-- A bound-based slicing algorithm takes as input a bound analysis, request,
-- entities, policies, and a hypothesis that the principal and resourse
-- `VariableDef`s can be extracted from all policies,
-- and filters out the policies whose bound is not satisfied by the
-- request and entities.
public def BoundAnalysis.slice (ba : BoundAnalysis) (request : Request) (entities : Entities)
    (policies : Cst.Policies)
    (h : ∀ policy ∈ policies.ps, (prVars? policy).isSome) : Cst.Policies :=
  { ps := policies.ps.attach.filterMap (fun ⟨policy, hmem⟩ =>
      if satisfiedBound (ba policy (h policy hmem)) request entities then some policy else none) }

-- Scope-based analysis extracts the bound from the policy.
public def scopeAnalysis (policy : Cst.Policy) (h : (prVars? policy).isSome) : PolicyBound :=
  let (pr, res) := (prVars? policy).get h
  { principalBound := varBound? pr,
    resourceBound  := varBound? res }

end Cedar.Frontend.Cst
