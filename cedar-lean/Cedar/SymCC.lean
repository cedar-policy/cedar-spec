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

import Cedar.SymCC.Extractor
import Cedar.SymCC.Decoder
import Cedar.SymCC.Encoder
import Cedar.SymCC.Solver
import Cedar.SymCC.Verifier
import Cedar.Validation.Validator

/-! This file contains the top-level interface to SymCC. -/

namespace Cedar.SymCC

open Cedar.Spec

/--
Given a type environment `Γ`, returns a symbolic environment `εnv` that
represents all concrete inputs (requests and entities) `env ∈ εnv` that conform
to `Γ` according to `Cedar.Validation.requestMatchesEnvironment` and
`Cedar.Validation.entitiesMatchEnvironment`.
-/
abbrev SymEnv.ofTypeEnv := SymEnv.ofEnv

/--
The Cedar symbolic compiler assumes that it receives well-typed policies.  This
function enforces this requirement by calling Cedar's typechecker. Specifically,
given a policy `p` and type environment `Γ`, this function calls the Cedar
typechecker to obtain a policy `p'` that is semantically equivalent to `p` and
well-typed with respect to `Γ`.

All functions defined in this file that accept policies as input _must_ be
called on the _output_ of this function (or `wellTypedPolicies`) to ensure that
symbolic compilation succeeds. Applying the symbolic compiler directly to a
policy `p` may result in type errors---that is, the compiler rejecting the
policy because it does not satisfy the `WellTyped` constraints that are assumed
by the compiler, and enforced by the typechecker through policy transformation.
-/
def wellTypedPolicy (p : Policy) (Γ : Cedar.Validation.TypeEnv) : Except Validation.ValidationError Policy := do
  let tx ← Cedar.Validation.typecheckPolicy p Γ
  .ok {
    id             := p.id,
    effect         := p.effect,
    principalScope := .principalScope .any,
    actionScope    := .actionScope .any,
    resourceScope  := .resourceScope .any,
    condition      := [⟨.when, tx.toExpr⟩]
  }

/--
The Cedar symbolic compiler assumes that it receives well-typed policies.  This
function enforces this requirement by calling Cedar's typechecker. Specifically,
given policies `ps` and a type environment `Γ`, this function calls the Cedar
typechecker on each `p ∈ ps` to obtain a policy `p'` that is semantically
equivalent to `p` and well-typed with respect to `Γ`.

All functions defined in this file that accept policies as input _must_ be
called on the _output_ of this function (or `wellTypedPolicy`) to ensure that
symbolic compilation succeeds. Applying the symbolic compiler directly to
policies `ps` may result in type errors---that is, the compiler rejecting the
policies because they don't satisfy the `WellTyped` constraints that are assumed
by the compiler, and enforced by the typechecker through policy transformation.
-/
def wellTypedPolicies (ps : Policies) (Γ : Cedar.Validation.TypeEnv) : Except Validation.ValidationError Policies :=
  ps.mapM (wellTypedPolicy · Γ)

----- Slow verification checks that extract models -----

/--
Given some `asserts` and their corresponding symbolic environment `εnv`,
calls the SMT solver (if necessary) on an SMTLib encoding of `asserts` and
returns `none` if the result is unsatisfiable. Otherwise returns `some I`
containing a counterexample interpretation `I`. The `asserts` are expected to
be well-formed with respect to `εnv` according to `Cedar.SymCC.Term.WellFormed`.
This call resets the solver.
-/
def checkSatAsserts (asserts : Asserts) (εnv : SymEnv) : SolverM (Option Interpretation) := do
  if asserts.any (· == false) then
    Solver.reset
    pure .none
  else if asserts.all (· == true) then
    Solver.reset
    pure (.some (Decoder.defaultInterpretation εnv.entities))
  else
    let enc ← Encoder.encode asserts εnv (produceModels := true)
    match (← Solver.checkSat) with
    | .unsat   => pure .none
    | .sat     =>
      let model ← Solver.getModel
      match Decoder.decode model enc with
      | .ok I      => -- validate the model
        for t in asserts do
          if t.interpret I != true then
            throw (IO.userError s!"Model violates assertion {reprStr t}: {model}")
        pure (.some I)
      | .error msg => throw (IO.userError s!"Model decoding failed: {msg}\n {model}")
    | .unknown => throw (IO.userError s!"Solver returned unknown.")

/--
Given policies `ps` (in their post-typecheck forms), some `asserts`, and the
corresponding symbolic environment `εnv`, calls the SMT solver (if necessary) on
an SMTLib encoding of `asserts` and returns `none` if the result is
unsatisfiable. Otherwise returns `some env` containing a counterexample
environment such that evaluating `ps` in `env` violates the property verified by
`asserts`.

The `asserts` are expected to be well-formed with respect to `εnv` according to
`Cedar.SymCC.Term.WellFormed`. They must encode a property of policies `pc`.
Specifically, for each term `t ∈ asserts`, there must be a set of expressions
`xs` such that each `x ∈ xs` is a subexpression of `p ∈ ps`, and the meaning of
`t` is a function of the meaning of `xs`. This ensures that findings generated
by `solve` are sound and complete.
-/
def satAsserts? (ps : Policies) (asserts : Asserts) (εnv : SymEnv) : SolverM (Option Env) := do
  match ← checkSatAsserts asserts εnv with
  | .none   => pure none
  | .some I =>
    match εnv.extract? (ps.map Policy.toExpr) I with
    | .some env => pure (some env)
    | .none     => throw (IO.userError s!"Extraction failed.")

/--
Given policies `ps`, a verification condition generator `vc`, and a symbolic
environment `εnv`, calls the SMT solver (if necessary) on an SMTLib encoding of
`vc εnv` and returns `none` if the result is unsatisfiable. Otherwise
returns `some env` containing a counterexample environment such that
evaluating `ps` in `env` violates the property verified by `vc`.

The function `vc` is expected to produce a list of terms type .bool that are
well-formed with respect to `εnv` according to `Cedar.SymCC.Term.WellFormed`.
These terms must encode a property of policies `pc`.  Specifically, for each
term `t ∈ vc εnv`, there must be a set of expressions `xs` such that each
`x ∈ xs` is a subexpression of `p ∈ ps`, and the meaning of `t` is a function of
the meaning of `xs`.  This ensures that findings generated by `solve` are sound
and complete.

This call resets the solver.
-/
def sat? (ps : Policies) (vc : SymEnv → Result Asserts) (εnv : SymEnv) : SolverM (Option Env) :=
  match vc εnv with
  | .ok asserts => satAsserts? ps asserts εnv
  | .error err => throw (IO.userError s!"SymCC failed: {reprStr err}.")

/--
Returns `none` iff `p` does not error on any well-formed input in `εnv`.
Otherwise returns an input `some env` on which `p` errors.
-/
def neverErrors? (p : Policy) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? [p] (verifyNeverErrors p) εnv

/--
Returns `none` iff `p` matches all well-formed inputs in `εnv`. That is,
if `p` is a `permit` policy, it allows all inputs in `εnv`, or if `p` is a
`forbid` policy, it denies all inputs in `εnv`.
Otherwise returns an input `some env` that is not-matched by `p`.

Compare with `alwaysAllows?`, which takes a policyset (which could consist of a
single policy, or more) and determines whether it _allows_ all well-formed
inputs in an `εnv`. This function differs from `alwaysAllows` on a singleton
policyset in how it treats `forbid` policies -- while `alwaysAllows` trivially
doesn't hold for any policyset containing only `forbid` policies,
`alwaysMatches` does hold if the `forbid` policy explicitly denies all inputs in
the `εnv`.
-/
def alwaysMatches? (p : Policy) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? [p] (verifyAlwaysMatches p) εnv

/--
Returns `none` iff `p` matches no well-formed inputs in `εnv`.
Otherwise returns an input `some env` that is matched by `p`.

Compare with `alwaysDenies?`, which takes a policyset (which could consist of a
single policy, or more) and determines whether it _denies_ all well-formed
inputs in an `εnv`. This function differs from `alwaysDenies` on a singleton
policyset in how it treats `forbid` policies -- while `alwaysDenies` trivially
holds for any policyset containing only `forbid` policies, `neverMatches` only
holds if the `forbid` policy explicitly denies no inputs in the `εnv`.
-/
def neverMatches? (p : Policy) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? [p] (verifyNeverMatches p) εnv

/--
Returns `none` iff `p₁` and `p₂` match exactly the same set of well-formed
inputs in `εnv`.  Otherwise returns an input `some env` on which `p₁` and `p₂`
have different matching behavior (one matches and the other does not).

Compare with `equivalent?`, which takes two policysets (which could consist of a
single policy, or more) and determines whether the _authorization behavior_ of
those policysets is equivalent for well-formed inputs in `εnv`. This function
differs from `equivalent?` on singleton policysets in how it treats `forbid`
policies -- while `equivalent?` trivially holds for any pair of `forbid` policies
(as they both always-deny), `matchesEquivalent?` only holds if the two policies
match exactly the same set of inputs. Also, a nontrivial `permit` and nontrivial
`forbid` policy can be `matchesEquivalent?`, but can never be `equivalent?`.
-/
def matchesEquivalent? (p₁ p₂ : Policy) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? [p₁, p₂] (verifyMatchesEquivalent p₁ p₂) εnv

/--
Returns `none` iff `p₁` matching implies that `p₂` matches, for every
well-formed input in `εnv`. That is, for every request where `p₁` matches, `p₂`
also matches. Otherwise returns an input `some env` that is matched by `p₁` but
not-matched by `p₂`.

Compare with `implies?`, which takes two policysets (which could consist of a
single policy, or more) and determines whether the _authorization decision_ of
the first implies that of the second. This function differs from `implies?` on
singleton policysets in how it treats `forbid` policies -- while for `implies?`,
any `forbid` policy trivially implies any `permit` policy (as always-deny always
implies any policy), for `matchesImplies?`, a `forbid` policy may or may not
imply a `permit` policy, and a `permit` policy may or may not imply a `forbid`
policy.
-/
def matchesImplies? (p₁ p₂ : Policy) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? [p₁, p₂] (verifyMatchesImplies p₁ p₂) εnv

/--
Returns `none` iff there is no well-formed input in `εnv` that is matched by
both `p₁` and `p₂`. Otherwise returns an input `some env` that is matched by
both `p₁` and `p₂`. This checks that the sets of inputs matched by `p₁` and `p₂`
are disjoint.

Compare with `disjoint?`, which takes two policysets (which could consist of a
single policy, or more) and determines whether the _authorization behavior_ of
those policysets are disjoint. This function differs from `disjoint?` on
singleton policysets in how it treats `forbid` policies -- while for
`disjoint?`, any `forbid` policy is trivially disjoint from any other policy (as
it allows nothing), `matchesDisjoint?` considers whether the `forbid` policy may
_match_ (rather than _allow_) any input that is matched by the other policy.
-/
def matchesDisjoint? (p₁ p₂ : Policy) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? [p₁, p₂] (verifyMatchesDisjoint p₁ p₂) εnv

/--
Returns `none` iff the authorization decision of `ps₁` implies that of `ps₂` for
every well-formed input in `εnv`. That is, every input allowed by `ps₁` is
allowed by `ps₂`; `ps₂` is either more permissive than, or equivalent to, `ps₁`.
Otherwise returns an input `some env` that is allowed by `ps₁` but denied by `ps₂`.
-/
def implies? (ps₁ ps₂ : Policies) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? (ps₁ ++ ps₂) (verifyImplies ps₁ ps₂) εnv

/--
Returns `none` iff `ps` allows all well-formed inputs in `εnv`. Otherwise
returns an input `some env` that is denied by `ps`.
-/
def alwaysAllows? (ps : Policies) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? ps (verifyAlwaysAllows ps) εnv

/--
Returns `none` iff `ps` denies all well-formed inputs in `εnv`. Otherwise
returns an input `some env` that is allowed by `ps`.
-/
def alwaysDenies? (ps : Policies) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? ps (verifyAlwaysDenies ps) εnv

/--
Returns `none` iff `ps₁` and `ps₂` produce the same authorization decision on
all well-formed inputs in `εnv`. Otherwise returns an input `some env` on which
`ps₁` and `ps₂` produce different authorization decisions.
-/
def equivalent? (ps₁ ps₂ : Policies) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? (ps₁ ++ ps₂) (verifyEquivalent ps₁ ps₂) εnv

/--
Returns `none` iff there is no well-formed input in `εnv` that is allowed by
both `ps₁` and `ps₂`.  Otherwise returns an input `some env` that is allowed by
both `ps₁` and `ps₂`. This checks that the authorization semantics of `ps₁` and
`ps₂` are disjoint.
-/
def disjoint? (ps₁ ps₂ : Policies) (εnv : SymEnv) : SolverM (Option Env) :=
  sat? (ps₁ ++ ps₂) (verifyDisjoint ps₁ ps₂) εnv

----- Faster verification checks that don't extract models -----

/--
Given some `asserts` and their corresponding symbolic environment `εnv`,
calls the SMT solver (if necessary) on an SMTLib encoding of `asserts` and
returns `true` iff the result is unsatisfiable. The `asserts` are expected to
be well-formed with respect to `εnv` according to `Cedar.SymCC.Term.WellFormed`.
This call resets the solver.
-/
def checkUnsatAsserts (asserts : Asserts) (εnv : SymEnv) : SolverM Bool := do
  if asserts.any (· == false) then
    Solver.reset
    pure true
  else if asserts.all (· == true) then
    Solver.reset
    pure false
  else
    let _ ← Encoder.encode asserts εnv (produceModels := false)
    match (← Solver.checkSat) with
    | .unsat   => pure true
    | .sat     => pure false
    | .unknown => throw (IO.userError s!"Solver returned unknown.")

/--
Given a verification condition generator `vc` and a symbolic environment `εnv`,
calls the SMT solver (if necessary) on an SMTLib encoding of `vc εnv` and
returns `true` iff the result is unsatisfiable. The function `vc` is expected to
produce a list of terms type .bool that are well-formed with respect to `εnv`
according to `Cedar.SymCC.Term.WellFormed`. This call resets the solver.
-/
def checkUnsat (vc : SymEnv → Result Asserts) (εnv : SymEnv) : SolverM Bool := do
  match vc εnv with
  | .ok asserts => checkUnsatAsserts asserts εnv
  | .error err => throw (IO.userError s!"SymCC failed: {reprStr err}.")

/--
Returns true iff `p` does not error on any well-formed input in `εnv`.
-/
def checkNeverErrors (p : Policy) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyNeverErrors p) εnv

/--
Returns true iff `p` matches all well-formed inputs in `εnv`. That is,
if `p` is a `permit` policy, it allows all inputs in `εnv`, or if `p` is a
`forbid` policy, it denies all inputs in `εnv`.

Compare with `checkAlwaysAllows`, which takes a policyset (which could consist of a
single policy, or more) and determines whether it _allows_ all well-formed
inputs in an `εnv`. This function differs from `checkAlwaysAllows` on a
singleton policyset in how it treats `forbid` policies -- while
`checkAlwaysAllows` trivially doesn't hold for any policyset containing only
`forbid` policies, `checkAlwaysMatches` does hold if the `forbid` policy
explicitly denies all inputs in the `εnv`.
-/
def checkAlwaysMatches (p : Policy) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyAlwaysMatches p) εnv

/--
Returns true iff `p` matches no well-formed inputs in `εnv`.

Compare with `checkAlwaysDenies`, which takes a policyset (which could consist
of a single policy, or more) and determines whether it _denies_ all well-formed
inputs in an `εnv`. This function differs from `checkAlwaysDenies` on a
singleton policyset in how it treats `forbid` policies -- while
`checkAlwaysDenies` trivially holds for any policyset containing only `forbid`
policies, `checkNeverMatches` only holds if the `forbid` policy explicitly
denies no inputs in the `εnv`.
-/
def checkNeverMatches (p : Policy) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyNeverMatches p) εnv

/--
Returns true iff `p₁` and `p₂` match exactly the same set of well-formed
inputs in `εnv`.

Compare with `checkEquivalent`, which takes two policysets (which could consist of a
single policy, or more) and determines whether the _authorization behavior_ of
those policysets is equivalent for well-formed inputs in `εnv`. This function
differs from `checkEquivalent` on a singleton policyset in how it treats `forbid`
policies -- while `checkEquivalent` trivially holds for any pair of `forbid` policies
(as they both always-deny), `checkMatchesEquivalent` only holds if the two policies
match exactly the same set of inputs. Also, a nontrivial `permit` and nontrivial
`forbid` policy can be `checkMatchesEquivalent`, but can never be `checkEquivalent`.
-/
def checkMatchesEquivalent (p₁ p₂ : Policy) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyMatchesEquivalent p₁ p₂) εnv

/--
Returns true iff `p₁` matching implies that `p₂` matches, for every
well-formed input in `εnv`. That is, for every request where `p₁` matches, `p₂`
also matches.

Compare with `checkImplies`, which takes two policysets (which could consist of
a single policy, or more) and determines whether the _authorization decision_ of
the first implies that of the second. This function differs from `checkImplies`
on singleton policysets in how it treats `forbid` policies -- while for
`checkImplies`, any `forbid` policy trivially implies any `permit` policy (as
always-deny always implies any policy), for `checkMatchesImplies`, a `forbid`
policy may or may not imply a `permit` policy, and a `permit` policy may or may
not imply a `forbid` policy.
-/
def checkMatchesImplies (p₁ p₂ : Policy) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyMatchesImplies p₁ p₂) εnv

/--
Returns true iff there is no well-formed input in `εnv` that is matched by
both `p₁` and `p₂`. This checks that the sets of inputs matched by `p₁` and `p₂`
are disjoint.

Compare with `checkDisjoint`, which takes two policysets (which could consist of
a single policy, or more) and determines whether the _authorization behavior_ of
those policysets are disjoint. This function differs from `checkDisjoint` on
singleton policysets in how it treats `forbid` policies -- while for
`checkDisjoint`, any `forbid` policy is trivially disjoint from any other policy
(as it allows nothing), `checkMatchesDisjoint` considers whether the `forbid`
policy may _match_ (rather than _allow_) any input that is matched by the other
policy.
-/
def checkMatchesDisjoint (p₁ p₂ : Policy) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyMatchesDisjoint p₁ p₂) εnv

/--
Returns true iff the authorization decision of `ps₁` implies that of `ps₂` for
every well-formed input in `εnv`. That is, every input allowed by `ps₁` is
allowed by `ps₂`; `ps₂` is either more permissive than, or equivalent to, `ps₁`.
-/
def checkImplies (ps₁ ps₂ : Policies) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyImplies ps₁ ps₂) εnv

/--
Returns true iff `ps` allows all well-formed inputs in `εnv`.
-/
def checkAlwaysAllows (ps : Policies) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyAlwaysAllows ps) εnv

/--
Returns true iff `ps` denies all well-formed inputs in `εnv`.
-/
def checkAlwaysDenies (ps : Policies) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyAlwaysDenies ps) εnv

/--
Returns true iff `ps₁` and `ps₂` produce the same authorization decision on all
well-formed inputs in `εnv`.
-/
def checkEquivalent (ps₁ ps₂ : Policies) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyEquivalent ps₁ ps₂) εnv

/--
Returns true iff there is no well-formed input in `εnv` that is allowed by both
`ps₁` and `ps₂`.  This checks that the authorization semantics of `ps₁` and
`ps₂` are disjoint. If this query is satisfiable, then there is at least one
well-formed input that is allowed by both `ps₁` and `ps₂`.
-/
def checkDisjoint (ps₁ ps₂ : Policies) (εnv : SymEnv) : SolverM Bool :=
  checkUnsat (verifyDisjoint ps₁ ps₂) εnv

end Cedar.SymCC
