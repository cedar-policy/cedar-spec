/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Data.Set
import Cedar.Spec.PartialEvaluator
import Cedar.Spec.PartialExpr
import Cedar.Spec.Policy

/-!
This file defines Cedar partial responses.
-/

namespace Cedar.Spec

open Cedar.Data

inductive Residual where
  | residual (id : PolicyID) (effect : Effect) (condition : PartialExpr)
  | error (id : PolicyID) (error : Error) -- definitely results in this error, for any substitution of the unknowns

def Residual.id (r : Residual) : PolicyID :=
  match r with
  | .residual id _ _ => id
  | .error id _ => id

def Residual.effect (r : Residual) : Option Effect :=
  match r with
  | .residual _ effect _ => effect
  | .error _ _ => none

structure PartialResponse where
  /--
    All residuals for policies that are, or may be, satisfied.
    Does not include policies that are definitely not satisfied.
    Does include policies that are definitely satisfied (they will have residual `true`).
  -/
  residuals : List Residual
  /--
    The `PartialRequest` that was used to compute this `PartialResponse`
  -/
  req : PartialRequest
  /--
    The `PartialEntities` that was used to compute this `PartialResponse`
  -/
  entities : PartialEntities

/--
  All `permit` policies which are definitely satisfied (for all possible
  substitutions of the unknowns)
-/
def PartialResponse.knownPermits (resp : PartialResponse) : Set PolicyID :=
  let permits := resp.residuals.filterMap fun residual => match residual with
    | .residual id .permit (.lit (.bool true)) => some id
    | _ => none
  Set.make permits

/--
  All `forbid` policies which are definitely satisfied (for all possible
  substitutions of the unknowns)
-/
def PartialResponse.knownForbids (resp : PartialResponse) : Set PolicyID :=
  let forbids := resp.residuals.filterMap fun residual => match residual with
    | .residual id .forbid (.lit (.bool true)) => some id
    | _ => none
  Set.make forbids

/--
  All `permit` policies which are, or may be, satisfied
-/
def PartialResponse.permits (resp : PartialResponse) : Set PolicyID :=
  let permits := resp.residuals.filterMap fun residual => match residual with
    | .residual id .permit _ => some id
    | _ => none
  Set.make permits

/--
  All `forbid` policies which are, or may be, satisfied
-/
def PartialResponse.forbids (resp : PartialResponse) : Set PolicyID :=
  let forbids := resp.residuals.filterMap fun residual => match residual with
    | .residual id .forbid _ => some id
    | _ => none
  Set.make forbids

/--
  All policies which definitely produce errors (for all possible substitutions
  of the unknowns)
-/
def PartialResponse.errors (resp : PartialResponse) : List (PolicyID × Error) :=
  resp.residuals.filterMap fun residual => match residual with
    | .error id error => some (id, error)
    | _ => none

inductive PartialDecision where
  | allow -- definitely Allow, for any substitution of the unknowns
  | deny -- definitely Deny, for any substitution of the unknowns
  | unknown -- Allow and Deny are both possible, depending on substitution of the unknowns

deriving instance Repr, DecidableEq for PartialDecision

def PartialResponse.decision (resp : PartialResponse) : PartialDecision :=
  if ¬ resp.knownForbids.isEmpty
  then .deny -- there is a known forbid, we'll always get explicit deny
  else if resp.permits.isEmpty
  then .deny -- there are no permits that are even possibly satisfied
  else if ¬ resp.forbids.isEmpty
  then .unknown -- there's at least one forbid that may be satisfied, and at least one permit that may be (or is) satisfied
  else if ¬ resp.knownPermits.isEmpty
  then .allow -- there are no forbids that are even possibly satisfied, and at least one permit that is definitely satisfied
  else .unknown -- there are no forbids that are even possibly satisfied, and at least one permit that may be satisfied

/--
  All policies which could possibly be determining, given some substitution of
  the unknowns
-/
def PartialResponse.overapproximateDeterminingPolicies (resp : PartialResponse) : Set PolicyID :=
  if ¬ resp.knownForbids.isEmpty
  then resp.forbids -- there is a known forbid so the decision will always be Deny, but any of resp.forbids could be determining
  else if resp.permits.isEmpty
  then resp.forbids -- there are no permits that are even possibly satisfied, so forbids will be determining, or if no forbids, then nothing will be determining
  else if ¬ resp.forbids.isEmpty
  then resp.permits ++ resp.forbids -- we don't know the decision in this case, so any permits or forbids could be determining
  else resp.permits -- there are no forbids that are even possibly satisfied, so permits will be determining, or if no permits, then nothing will be determining

/--
  All policies that must be determining (for all possible substitutions of the
  unknowns)
-/
def PartialResponse.underapproximateDeterminingPolicies (resp : PartialResponse) : Set PolicyID :=
  if ¬ resp.knownForbids.isEmpty
  then resp.knownForbids -- there is a known forbid, so we know at least the known forbids will be determining
  else if resp.permits.isEmpty
  then Set.empty -- there are no permits that are even possibly satisfied. The determining policies will be forbids, if any, but there aren't any known forbids so there are no policies we know will be determining
  else if ¬ resp.forbids.isEmpty
  then Set.empty -- we don't know the decision in this case, so we can't say any policy is for sure determining
  else resp.knownPermits -- there are no forbids that are even possibly satisfied, so if there are known permits, we know they will be determining

/--
  Re-evaluate with the given substitution for unknowns, giving a new PartialResponse

  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `PartialResponse` will still contain some (nontrivial) residuals.

  Returns `none` if the substitution is invalid -- e.g., if trying to substitute
  a non-EntityUID into `UidOrUnknown`.
-/
def PartialResponse.reEvaluateWithSubst (resp : PartialResponse) (subsmap : Map String RestrictedPartialValue) : Option PartialResponse := do
  let req' ← resp.req.subst subsmap
  some {
    residuals := resp.residuals.filterMap λ residual => match residual with
      | .error id e => some (.error id e)
      | .residual id effect cond => match partialEvaluate (cond.subst subsmap) req' (resp.entities.subst subsmap) with
        | .ok (.value (.prim (.bool false))) => none
        | .ok (.value v) => some (.residual id effect v.asPartialExpr)
        | .ok (.residual r) => some (.residual id effect r)
        | .error e => some (.error id e)
    req := req'
    entities := resp.entities.subst subsmap
  }

deriving instance Repr, DecidableEq, Inhabited for Residual

end Cedar.Spec
