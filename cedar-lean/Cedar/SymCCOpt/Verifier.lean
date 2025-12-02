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

import Cedar.SymCC.Verifier
import Cedar.SymCCOpt.CompiledPolicies
import Cedar.SymCCOpt.Enforcer

/-!
This file contains versions of the functions in `SymCC/Verifier.lean` that
operate on compiled policies (from `SymCCOpt/CompiledPolicies.lean`).
Unlike the unoptimized functions in `SymCC/Verifier.lean`, the functions in this
file do not need to call the symbolic compiler.
-/

namespace Cedar.SymCC

open Cedar.Spec Factory

/--
Returns asserts that are unsatisfiable iff the evaluation of `p`, represented
as a `Term` of type .option .bool, satisfies `φ` on all inputs drawn from the
`εnv` that `p` was compiled for.

See also `verifyNeverErrorsOpt`.
-/
def verifyEvaluateOpt (φ : Term → Term) (p : CompiledPolicy) : Asserts :=
  (enforceCompiledPolicy p).elts ++ [not (φ p.term)]

/--
Returns asserts that are unsatisfiable iff the authorization decisions produced
by `ps₁` and `ps₂`, represented as `Term`s of type .bool, satisfy `φ` on all
inputs drawn from the `εnv` that the policysets were compiled for.
(Caller guarantees that `ps₁` and `ps₂` were compiled for the same `εnv`.)

See also `verifyAlwaysAllowsOpt`, `verifyAlwaysDeniesOpt`, `verifyImpliesOpt`,
`verifyEquivalentOpt`, and `verifyDisjointOpt`.
-/
def verifyIsAuthorizedOpt (φ : Term → Term → Term) (ps₁ ps₂ : CompiledPolicies) : Asserts :=
  assert! ps₁.εnv = ps₂.εnv
  (enforcePairCompiledPolicies ps₁ ps₂).elts ++ [not (φ ps₁.term ps₂.term)]

/--
Returns asserts that are unsatisfiable iff `p` does not error on any input in
the `εnv` it was compiled for. If the asserts are satisfiable, then there is
some input in `εnv` on which `p` errors.
-/
def verifyNeverErrorsOpt (p : CompiledPolicy) : Asserts :=
  verifyEvaluateOpt isSome p

/--
Returns asserts that are unsatisfiable iff `p` matches all inputs in the `εnv`
it was compiled for.  If the asserts are satisfiable, then there is some input
in `εnv` which `p` doesn't match.
-/
def verifyAlwaysMatchesOpt (p : CompiledPolicy) : Asserts :=
  verifyEvaluateOpt (eq · (⊙true)) p

/--
Returns asserts that are unsatisfiable iff `p` matches no inputs in `εnv`.
If the asserts are satisfiable, then there is some input in `εnv` which `p`
does match.
-/
def verifyNeverMatchesOpt (p : CompiledPolicy) : Asserts :=
  verifyEvaluateOpt (λ t => not (eq t (⊙true))) p

/--
Returns asserts that are unsatisfiable iff the authorization decision of `ps₁`
implies that of `ps₂` for every input in the `εnv` that the policysets were
compiled for.
(Caller guarantees that `ps₁` and `ps₂` were compiled for the same `εnv`.)
In other words, every input allowed by `ps₁` is allowed by `ps₂`.
-/
def verifyImpliesOpt (ps₁ ps₂ : CompiledPolicies) : Asserts :=
  verifyIsAuthorizedOpt implies ps₁ ps₂

/--
Returns asserts that are unsatisfiable iff `ps` allows all inputs in the `εnv`
it was compiled for.
-/
def verifyAlwaysAllowsOpt (ps : CompiledPolicies) : Asserts :=
  verifyImpliesOpt (CompiledPolicies.allowAll ps.εnv) ps

/--
Returns asserts that are unsatisfiable iff `ps` denies all inputs in the `εnv`
it was compiled for.
-/
def verifyAlwaysDeniesOpt (ps : CompiledPolicies) : Asserts :=
  verifyImpliesOpt ps (CompiledPolicies.denyAll ps.εnv)

/--
Returns asserts that are unsatisfiable iff `ps₁` and `ps₂` produce the same
authorization decision on all inputs in the `εnv` that the policysets were
compiled for.
(Caller guarantees that `ps₁` and `ps₂` were compiled for the same `εnv`.)
-/
def verifyEquivalentOpt (ps₁ ps₂ : CompiledPolicies) : Asserts :=
  verifyIsAuthorizedOpt eq ps₁ ps₂

/--
Returns asserts that are unsatisfiable iff there is no input in the `εnv` that
is allowed by both `ps₁` and `ps₂`.
(Caller guarantees that `ps₁` and `ps₂` were compiled for the same `εnv`.)
This checks that the authorization semantics of `ps₁` and `ps₂` are disjoint.
If this query is satisfiable, then there is at least one input in this `εnv` that
is allowed by both `ps₁` and `ps₂`.
-/
def verifyDisjointOpt (ps₁ ps₂ : CompiledPolicies) : Asserts :=
  verifyIsAuthorizedOpt disjoint ps₁ ps₂
where
  disjoint (t₁ t₂ : Term) := not (and t₁ t₂)

end Cedar.SymCC
