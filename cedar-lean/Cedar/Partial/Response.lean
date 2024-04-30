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

import Cedar.Data.Set
import Cedar.Partial.Evaluator
import Cedar.Partial.Expr
import Cedar.Spec.Policy

/-!
This file defines Cedar partial responses.
-/

namespace Cedar.Partial

open Cedar.Data
open Cedar.Spec (Effect Error PolicyID)
open Cedar.Spec.Effect

inductive Residual where
  | residual (id : PolicyID) (effect : Effect) (condition : Partial.Expr)
  | error (id : PolicyID) (error : Error) -- definitely results in this error, for any substitution of the unknowns

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
  | .residual id eff' (.lit (.bool true)) => if eff = eff' then some id else none
  | _ => none

/--
  if this policy may be satisfied (for some substitution of the unknowns), and
  has the specified effect, return the PolicyID
-/
def Residual.mayBeSatisfied (eff : Effect) : Residual → Option PolicyID
  | .residual id eff' _ => if eff = eff' then some id else none
  | _ => none

structure Response where
  /--
    All residuals for policies that are, or may be, satisfied.
    Does not include policies that are definitely not satisfied (residual `false`).
    Does include policies that are definitely satisfied (residual `true`).
  -/
  residuals : List Residual
  /--
    The `Partial.Request` that was used to compute this `Partial.Response`
  -/
  req : Partial.Request
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
def Response.errors (resp : Partial.Response) : List (PolicyID × Error) :=
  resp.residuals.filterMap λ residual => match residual with
    | .error id error => some (id, error)
    | _ => none

inductive Decision where
  | allow -- definitely Allow, for any substitution of the unknowns
  | deny -- definitely Deny, for any substitution of the unknowns
  | unknown -- Allow and Deny are both possible, depending on substitution of the unknowns

deriving instance Repr, DecidableEq for Decision

def Response.decision (resp : Partial.Response) : Partial.Decision :=
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
def Response.overapproximateDeterminingPolicies (resp : Partial.Response) : Set PolicyID :=
  if ¬ resp.knownForbids.isEmpty
  then resp.forbids -- there is a known forbid so the decision will always be Deny, but any of resp.forbids could be determining
  else if resp.permits.isEmpty
  then resp.forbids -- there are no permits that are even possibly satisfied, so forbids will be determining, or if no forbids, then nothing will be determining
  else if ¬ resp.forbids.isEmpty
  then resp.permits ∪ resp.forbids -- we don't know the decision in this case, so any permits or forbids could be determining
  else resp.permits -- there are no forbids that are even possibly satisfied, so permits will be determining, or if no permits, then nothing will be determining

/--
  All policies that must be determining (for all possible substitutions of the
  unknowns)
-/
def Response.underapproximateDeterminingPolicies (resp : Partial.Response) : Set PolicyID :=
  if ¬ resp.knownForbids.isEmpty
  then resp.knownForbids -- there is a known forbid, so we know at least the known forbids will be determining
  else if resp.permits.isEmpty
  then Set.empty -- there are no permits that are even possibly satisfied. The determining policies will be forbids, if any, but there aren't any known forbids so there are no policies we know will be determining
  else if ¬ resp.forbids.isEmpty
  then Set.empty -- we don't know the decision in this case, so we can't say any policy is for sure determining
  else resp.knownPermits -- there are no forbids that are even possibly satisfied, so if there are known permits, we know they will be determining

end Cedar.Partial
