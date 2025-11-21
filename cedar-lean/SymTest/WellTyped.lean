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
import SymTest.Util

/-!

This file contains unit tests that show the symbolic compiler (`compile`) does
not error on policies that are well-typed according to the `WellTyped`
constraints established by Cedar's typechecker; see
`Cedar.Thm.Validation.WellTyped.Definition` and `Cedar.Thm.WellTyped` for
details.  We also include tests that show that the symbolic compiler can error
on policies that do not satisfy `WellTyped` constraints .

Eventually, we will want to _prove_ that the symbolic compiler never errors on
`WellTyped` policies.

In practice, this means that we have to ensure that an analysis calls the
symbolic compiler _only_ on policies that are well-typed, as established by
`SymCC.wellTypedPolicy`.

To see why the compiler may fail on policies that pass validation (but are not
made to be well-typed through validator transformations), consider the following
policy where the type of `context` is `{foo: Long, bar?: Bool}`:

```
// Policy A
permit(principal, action, resource)
when {
  if ((- context.foo < 0) && (context has baz))  // condition
  then 1
  else context has bar
};
```

Policy A passes validation. In particular, the validator types the entire
condition as `ff` because `context has baz` is known to be false from the type
of `context`. Given this, the validator concludes that the `then`-branch, which
is ill-typed, can never be executed so it can be safely ignored.  The `else`
branch is well-typed (as a boolean), so validation as a whole passes.

However, the symbolic compiler _rejects_ this policy with a type error because
it sees that the `then`-branch does not have a boolean type.  The compiler must
examine the `then` branch since it concludes, correctly, that the condition does
_not_ always evaluate to `false`. The condition evaluates to _either_ an
airthmetic overflow error _or_ false, and the compiler's encoding reflects this
fact, in order to be sound and complete with respect to full Cedar semantics.
(The validator is free to ignore all errors that aren't type errors, but the
compiler is not.)

This brings up a natural question: can't we just make the symbolic compiler
smarter? After all, while the condition is not always false, it is indeed the
case that we _can_ safely ignore the `then` branch here because it can _never_
be executed:  either execution fails when checking the condition due to an
arithmetic overflow error, or execution succeeds with `false`, falling through
to the `else` branch. So, it seems like it should be possible to develop a set
of _local_ rewrites of Terms that are "either error or a boolean constant" to
infer when a branch cannot be executed.

Unfortunately, this is not possible because of two lines of code in the
validator:
 * https://github.com/cedar-policy/cedar-spec/blob/356b86d13971224ff0553af6c33f19e1a3f7bd2a/cedar-lean/Cedar/Validation/Typechecker.lean#L190
 * https://github.com/cedar-policy/cedar-spec/blob/356b86d13971224ff0553af6c33f19e1a3f7bd2a/cedar-lean/Cedar/Validation/Typechecker.lean#L244

These two lines use capability information to infer that the type of a `has` or
`hasTag` expression is the constant `tt`. Note that these are the only two lines
in the validator that do this---everywhere else, deciding if the type of an
expression is `tt` or `ff` is done from bottom-up (local) information, without
referencing capabilities, which are pushing context-sensitive information
top-down.

Here is an example policy, with the same `context` type as before, where the
validator uses this code to conclude that the policy is well-typed:

```
// Policy B
permit(principal, action, resource)
when {
  if context has bar
  then if context has bar then context.bar else 1
  else true
};
```

If it weren't for these two lines of code, it would indeed be possible for the
symbolic compiler to use local rewrites to eliminate dead branches as often as
the validator.  And we cannot eliminate these two lines of code because it would
compile validator precision (i.e., reject more policies), which is a breaking
change.

For the symbolic compiler to reproduce these inferences, we would need to start
propagating contextual information---specifically, the path condition---from the
top down, just like the validator. It is possible to do this and to prove it
correct (see https://dl.acm.org/doi/10.1145/3498709), but it would require
invasive changes to both the compiler and all the accompanying proofs.  We can
do this if we find that calling the typechecker prior to symbolic compilation
introduces too much of a burden in practice (e.g., by making debugging difficult
due to the deepening of the analysis pipeline).
-/

namespace SymTest.WellTyped

open Cedar Data Spec SymCC Validation
open UnitTest

private def ctxtTy : RecordType :=
  Map.make [
    ("foo", .required .int),
    ("bar", .optional (.bool .anyBool)),
  ]

private def Γ := BasicTypes.env Map.empty Map.empty ctxtTy
private def εnv  := SymEnv.ofEnv Γ

/-
// Policy A
permit(principal, action, resource)
when {
  if ((- context.foo < 0) && (context has baz))  // condition
  then 1
  else context has bar
};
-/
private def policyA : Policy := {
  id             := "Policy A",
  effect         := .permit,
  principalScope := .principalScope .any,
  actionScope    := .actionScope .any,
  resourceScope  := .resourceScope .any,
  condition      := [⟨.when,
    .ite
      (.and
        (.binaryApp .less
          (.unaryApp .neg (.getAttr (.var .context) "foo"))
          (.lit (.int 0)))
        (.hasAttr (.var .context) "baz"))
      (.lit (.int 1))
      (.hasAttr (.var .context) "bar")⟩]
}

/-
// Policy B
permit(principal, action, resource)
when {
  if context has bar
  then if context has bar then context.bar else 1
  else true
};
-/
private def policyB : Policy := {
  id             := "Policy B",
  effect         := .permit,
  principalScope := .principalScope .any,
  actionScope    := .actionScope .any,
  resourceScope  := .resourceScope .any,
  condition      := [⟨.when,
    .ite
      (.hasAttr (.var .context) "bar")
      (.ite
        (.hasAttr (.var .context) "bar")
        (.getAttr (.var .context) "bar")
        (.lit (.int 1)))
      (.lit (.bool true))⟩]
}

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
def testFailsOnIllTyped (p : Policy) : List (TestCase SolverM) :=
  [
    test s!"on the unoptimized path, verifyNeverErrors of {p.id} fails due to type errors"
      -- on the unoptimized path, verifyNeverErrors fails with .typeError
      -- (if the caller used `wellTypedPolicy p Γ` rather than `p` directly, as they
      -- should, then either `wellTypedPolicy` itself would fail-fast, or both
      -- `wellTypedPolicy` and `verifyNeverErrors` would succeed; see theorem
      -- `verifyNeverErrors_is_ok_and_sound` in WellTypedVerification.lean.)
      ⟨λ _ => checkEq (verifyNeverErrors p εnv) (.error .typeError)⟩,
    test s!"on the optimized path, policy compilation and verifyNeverErrorsOpt of {p.id} succeed"
      -- on the optimized path, policy compilation and `verifyNeverErrorsOpt` both succeed
      -- (despite the extensive comments at the top of this file) because it compiles the
      -- _transformed_ policies produced by the typechecker -- equivalent to if the
      -- caller in the unoptimized case had passed their policies through `wellTypedPolicy`
      -- (as they properly should) rather than feeding them to `verifyNeverErrors` directly.
      ⟨λ _ =>
        let compileResult := CompiledPolicy.compile p Γ
        -- no need to actually check that `verifyNeverErrorsOpt` succeeds,
        -- because it is infallible (doesn't return a Result/Except type). Tests
        -- in other modules check the end-to-end behavior of the optimized path.
        checkMatches (compileResult matches .ok _) compileResult⟩,
  ]

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
def testSucceedsOnWellTyped (p : Policy) (expected : Bool) : List (TestCase SolverM) :=
  let desc := s!"checkNeverErrors of (wellTypedPolicy {p.id} Γ) succeeds with outcome '{expected}'"
  [
    test (desc ++ " (unoptimized)")
      ⟨λ _ => do
        let wp ← wellTypedPolicy p Γ |> IO.ofExcept
        checkEq (← checkNeverErrors wp εnv) expected
      ⟩,
    test (desc ++ " (optimized)")
      ⟨λ _ => do
        let cp ← CompiledPolicy.compile p Γ |> IO.ofExcept
        checkEq (← checkNeverErrorsOpt cp) expected
      ⟩,
  ]

def testsForIllTyped :=
  suite "WellTyped.compileFailsOnIllTypedPolicies" $ List.flatten
  [
    testFailsOnIllTyped policyA,
    testFailsOnIllTyped policyB,
  ]

def testsForWellTyped :=
  suite "WellTyped.compileSucceedsOnWellTypedPolicies" $ List.flatten
  [
    testSucceedsOnWellTyped policyA false,
    testSucceedsOnWellTyped policyB true,
  ]

def tests := [
  testsForIllTyped,
  testsForWellTyped
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)


end SymTest.WellTyped
