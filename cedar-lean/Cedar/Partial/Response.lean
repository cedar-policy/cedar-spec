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

import Lean.Data.Json.FromToJson
import Cedar.Data.Set
import Cedar.Partial.Evaluator
import Cedar.Partial.Value
import Cedar.Spec.Policy

/-!
This file defines Cedar partial responses.
-/

namespace Cedar.Partial

open Cedar.Data
open Cedar.Partial (Subsmap)
open Cedar.Spec (Effect Error PolicyID)

/-- The result of partial-evaluating a policy -/
inductive Residual where
  /--
    Some `Partial.Value`, which may be constant `true` (definitely satisfied),
    constant `false` (definitely not satisfied), or a nontrivial expression
  -/
  | residual (id : PolicyID) (effect : Effect) (condition : Partial.Value)
  /-- definitely results in this error, for any substitution of the unknowns -/
  | error (id : PolicyID) (error : Error)

deriving instance Repr, DecidableEq, Inhabited for Residual

def Residual.id : Residual → PolicyID
  | .residual id _ _ => id
  | .error id _ => id

def Residual.effect : Residual → Option Effect
  | .residual _ effect _ => effect
  | .error _ _ => none

/--
  if this policy must be satisfied (for any substitution of the unknowns), and
  has the specified effect, return the PolicyID
-/
def Residual.mustBeSatisfied (eff : Effect) : Residual → Option PolicyID
  | .residual id eff' (.value true) => if eff = eff' then some id else none
  | _ => none

/--
  if this policy may be satisfied (for some substitution of the unknowns), and
  has the specified effect, return the PolicyID
-/
def Residual.mayBeSatisfied (eff : Effect) : Residual → Option PolicyID
  | .residual _ _ (.value false) => none
  | .residual id eff' _ => if eff = eff' then some id else none
  | _ => none

/-- Response to a partial authorization request -/
structure Response where
  /--
    All residuals for policies that are, or may be, satisfied.
    Does not include policies that are definitely not satisfied (residual `false`).
    Does include policies that are definitely satisfied (residual `true`).
  -/
  residuals : List Residual
  /--
    The `Partial.Entities` that was used to compute this `Partial.Response`
  -/
  entities : Partial.Entities

/--
  Get the IDs of all policies which must be satisfied (for all possible
  substitutions of the unknowns) and have the given `Effect`
-/
def Response.mustBeSatisfied (resp : Partial.Response) (eff : Effect) : Set PolicyID :=
  Set.make (resp.residuals.filterMap (Residual.mustBeSatisfied eff))

/--
  Get the IDs of all policies which are, or may be, satisfied (for some
  possible substitution of the unknowns) and have the given `Effect`
-/
def Response.mayBeSatisfied (resp : Partial.Response) (eff : Effect) : Set PolicyID :=
  Set.make (resp.residuals.filterMap (Residual.mayBeSatisfied eff))

/--
  All `permit` policies which are definitely satisfied (for all possible
  substitutions of the unknowns)
-/
def Response.knownPermits (resp : Partial.Response) : Set PolicyID :=
  resp.mustBeSatisfied .permit

/--
  All `forbid` policies which are definitely satisfied (for all possible
  substitutions of the unknowns)
-/
def Response.knownForbids (resp : Partial.Response) : Set PolicyID :=
  resp.mustBeSatisfied .forbid

/--
  All `permit` policies which are, or may be, satisfied
-/
def Response.permits (resp : Partial.Response) : Set PolicyID :=
  resp.mayBeSatisfied .permit

/--
  All `forbid` policies which are, or may be, satisfied
-/
def Response.forbids (resp : Partial.Response) : Set PolicyID :=
  resp.mayBeSatisfied .forbid

/--
  All policies which definitely produce errors (for all possible substitutions
  of the unknowns)
-/
def Response.errorPolicies (resp : Partial.Response) : Set PolicyID :=
  Set.make (resp.residuals.filterMap λ residual => match residual with
    | .error id _ => some id
    | _ => none
  )

inductive Decision where
  /-- definitely Allow, for any substitution of the unknowns -/
  | allow
  /-- definitely Deny, for any substitution of the unknowns -/
  | deny
  /-- Allow and Deny are both possible, depending on substitution of the unknowns -/
  | unknown

deriving instance Repr, DecidableEq for Decision

instance : ToString Decision where
  toString d := match d with
    | .allow => "allow"
    | .deny => "deny"
    | .unknown => "unknown"

/--
  Return a `Partial.Decision` representing the authz decision, if it is known
  (for instance, if there is a forbid known to be satisfied, or no permits that
  are even possibly satisfied), or otherwise `Partial.Decision.unknown`
-/
def Response.decision (resp : Partial.Response) : Partial.Decision :=
  if ¬ resp.knownForbids.isEmpty then
    -- there is a known forbid, we'll always get explicit deny
    .deny
  else if resp.permits.isEmpty then
    -- there are no permits that are even possibly satisfied
    .deny
  else if resp.forbids.isEmpty && ¬ resp.knownPermits.isEmpty then
    -- there are no forbids that are even possibly satisfied, and at least one
    -- permit that is definitely satisfied
    .allow
  else
    -- all other cases we cannot know the decision yet.
    -- This includes at least two distinct cases:
    --   - there's at least one forbid that may be satisfied, and at least one
    --     permit that may be (or is) satisfied
    --   - there are no forbids that are even possibly satisfied, and at least
    --     one permit that may be satisfied, but none known to be satisfied
    .unknown

/--
  All policies which could possibly be determining, given some substitution of
  the unknowns
-/
def Response.overapproximateDeterminingPolicies (resp : Partial.Response) : Set PolicyID :=
  match resp.decision with
  | .deny =>
    -- when the decision is Deny, forbids (if any) are determining.
    -- Any forbid that may be satisfied may be determining.
    resp.forbids
  | .allow =>
    -- when the decision is Allow, permits (if any) are determining.
    -- Any permit that may be satisfied may be determining.
    resp.permits
  | .unknown =>
    -- when the decision is Unknown, any permits or forbids could be
    -- determining.
    resp.permits ∪ resp.forbids

/--
  All policies that must be determining (for all possible substitutions of the
  unknowns)
-/
def Response.underapproximateDeterminingPolicies (resp : Partial.Response) : Set PolicyID :=
  match resp.decision with
  | .deny =>
    -- when the decision is Deny, forbids (if any) are determining.
    -- The only forbids we _know_ will be determining are those that must be
    -- satisfied.
    resp.knownForbids
  | .allow =>
    -- when the decision is Allow, permits (if any) are determining.
    -- The only permits we _know_ will be determining are those that must be
    -- satisfied.
    resp.knownPermits
  | .unknown =>
    -- when the decision is Unknown, nothing is guaranteed to be determining.
    Set.empty

/--
  Re-evaluate with the given substitution for unknowns, giving a new
  `Residual`, or `none` if the residual is now `false`.

  Assumes that `entities` have already been substituted.
-/
def Residual.reEvaluateWithSubst (subsmap : Subsmap) (entities : Partial.Entities) : Residual → Option Residual
  | .error id e => some (.error id e)
  | .residual id effect cond =>
    match Partial.evaluateValue (cond.subst subsmap) entities with
    | .ok (.value false) => none
    | .ok (.value v) => some (.residual id effect v)
    | .ok cond' => some (.residual id effect cond')
    | .error e => some (.error id e)

/--
  Re-evaluate with the given substitution for unknowns, giving a new
  `Partial.Response`.

  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.Response` will still contain some (nontrivial) residuals.

  Respects the invariant documented on `Partial.Response.residuals` that:
    - `.residuals` will not include policies that are definitely not satisfied
        (residual `false`).
    - `.residuals` will include policies that are definitely satisfied (residual
        `true`).
-/
def Response.reEvaluateWithSubst (subsmap : Subsmap) : Partial.Response → Partial.Response
  | { residuals, entities } =>
  let entities' := entities.subst subsmap
  {
    residuals := residuals.filterMap (Residual.reEvaluateWithSubst subsmap entities')
    entities := entities'
  }

private structure JSONResponse where
  knownPermits : List String
  knownForbids : List String
  mayBeSatisifedPermits : List String
  mayBeSatisifedForbids : List String
  decision : String
  determiningUnderApprox : List String
  determiningOverApprox : List String
  deriving Lean.ToJson

instance : Coe Response JSONResponse where
  coe r := {
    knownPermits := r.knownPermits.toList
    knownForbids := r.knownForbids.toList
    mayBeSatisifedPermits := (r.mayBeSatisfied .permit).toList
    mayBeSatisifedForbids := (r.mayBeSatisfied .forbid).toList
    decision := toString r.decision
    determiningOverApprox := r.overapproximateDeterminingPolicies.toList
    determiningUnderApprox := r.underapproximateDeterminingPolicies.toList
    : JSONResponse
  }

instance : Lean.ToJson Response where
  toJson r :=
    let json_r : JSONResponse := r
    Lean.toJson json_r

end Cedar.Partial
