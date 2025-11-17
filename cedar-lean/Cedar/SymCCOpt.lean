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

import Cedar.SymCC
import Cedar.SymCCOpt.CompiledPolicies
import Cedar.SymCCOpt.Verifier
import Cedar.Validation.Validator

/-! This file contains the top-level interface to optimized SymCC. -/

namespace Cedar.SymCC

open Cedar.Spec

----- Slow verification checks that extract models -----

/--
Returns `none` iff `p` does not error on any well-formed input in the `εnv` it
was compiled for.
Otherwise returns an input `some env` on which `p` errors.
-/
def neverErrorsOpt? (p : CompiledPolicy) : SolverM (Option Env) :=
  satAsserts? [p.policy] (verifyNeverErrorsOpt p) p.εnv

/--
Returns `none` iff the authorization decision of `ps₁` implies that of `ps₂` for
every well-formed input in the `εnv` that the policysets were compiled for.
(Caller guarantees that `ps₁` and `ps₂` were compiled for the same `εnv`.)
That is, every input allowed by `ps₁` is allowed by `ps₂`; `ps₂` is either more
permissive than, or equivalent to, `ps₁`.
Otherwise returns an input `some env` that is allowed by `ps₁` but denied by `ps₂`.
-/
def impliesOpt? (ps₁ ps₂ : CompiledPolicies) : SolverM (Option Env) :=
  satAsserts? (ps₁.policies ++ ps₂.policies) (verifyImpliesOpt ps₁ ps₂) ps₁.εnv

/--
Returns `none` iff `ps` allows all well-formed inputs in the `εnv` it was
compiled for.
Otherwise returns an input `some env` that is denied by `ps`.
-/
def alwaysAllowsOpt? (ps : CompiledPolicies) : SolverM (Option Env) :=
  satAsserts? ps.policies (verifyAlwaysAllowsOpt ps) ps.εnv

/--
Returns `none` iff `ps` denies all well-formed inputs in the `εnv` it was
compiled for.
Otherwise returns an input `some env` that is allowed by `ps`.
-/
def alwaysDeniesOpt? (ps : CompiledPolicies) : SolverM (Option Env) :=
  satAsserts? ps.policies (verifyAlwaysDeniesOpt ps) ps.εnv

/--
Returns `none` iff `ps₁` and `ps₂` produce the same authorization decision on
all well-formed inputs in the `εnv` that the policysets were compiled for.
(Caller guarantees that `ps₁` and `ps₂` were compiled for the same `εnv`.)
Otherwise returns an input `some env` on which `ps₁` and `ps₂` produce different
authorization decisions.
-/
def equivalentOpt? (ps₁ ps₂ : CompiledPolicies) : SolverM (Option Env) :=
  satAsserts? (ps₁.policies ++ ps₂.policies) (verifyEquivalentOpt ps₁ ps₂) ps₁.εnv

/--
Returns `none` iff there is no well-formed input in `εnv` that the policysets were
compiled for, that is allowed by both `ps₁` and `ps₂`.
(Caller guarantees that `ps₁` and `ps₂` were compiled for the same `εnv`.)
Otherwise returns an input `some env` that is allowed by both `ps₁` and `ps₂`.
This checks that the authorization semantics of `ps₁` and `ps₂` are disjoint.
-/
def disjointOpt? (ps₁ ps₂ : CompiledPolicies) : SolverM (Option Env) :=
  satAsserts? (ps₁.policies ++ ps₂.policies) (verifyDisjointOpt ps₁ ps₂) ps₁.εnv

----- Faster verification checks that don't extract models -----

/--
Returns true iff `p` does not error on any well-formed input in the `εnv` it was
compiled for.
-/
def checkNeverErrorsOpt (p : CompiledPolicy) : SolverM Bool :=
  checkUnsatAsserts (verifyNeverErrorsOpt p) p.εnv

/--
Returns true iff the authorization decision of `ps₁` implies that of `ps₂` for
every well-formed input in `εnv` that the policysets were compiled for.
(Caller guarantees that `ps₁` and `ps₂` were compiled for the same `εnv`.)
That is, every input allowed by `ps₁` is allowed by `ps₂`; `ps₂` is either more
permissive than, or equivalent to, `ps₁`.
-/
def checkImpliesOpt (ps₁ ps₂ : CompiledPolicies) : SolverM Bool :=
  checkUnsatAsserts (verifyImpliesOpt ps₁ ps₂) ps₁.εnv

/--
Returns true iff `ps` allows all well-formed inputs in the `εnv` it was compiled
for.
-/
def checkAlwaysAllowsOpt (ps : CompiledPolicies) : SolverM Bool :=
  checkUnsatAsserts (verifyAlwaysAllowsOpt ps) ps.εnv

/--
Returns true iff `ps` denies all well-formed inputs in the `εnv` it was compiled
for.
-/
def checkAlwaysDeniesOpt (ps : CompiledPolicies) : SolverM Bool :=
  checkUnsatAsserts (verifyAlwaysDeniesOpt ps) ps.εnv

/--
Returns true iff `ps₁` and `ps₂` produce the same authorization decision on all
well-formed inputs in the `εnv` that the policysets were compiled for.
-/
def checkEquivalentOpt (ps₁ ps₂ : CompiledPolicies) : SolverM Bool :=
  checkUnsatAsserts (verifyEquivalentOpt ps₁ ps₂) ps₁.εnv

/--
Returns true iff there is no well-formed input in `εnv` that is allowed by both
`ps₁` and `ps₂`.
(Caller guarantees that `ps₁` and `ps₂` were compiled for the same `εnv`.)
This checks that the authorization semantics of `ps₁` and `ps₂` are disjoint. If
this query is satisfiable, then there is at least one well-formed input that is
allowed by both `ps₁` and `ps₂`.
-/
def checkDisjointOpt (ps₁ ps₂ : CompiledPolicies) : SolverM Bool :=
  checkUnsatAsserts (verifyDisjointOpt ps₁ ps₂) ps₁.εnv

end Cedar.SymCC
