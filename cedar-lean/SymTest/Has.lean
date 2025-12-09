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

import SymTest.Util

/-! This file unit tests symbolic compilation of the `has` operator. -/

namespace SymTest.Has

open Cedar Data Spec SymCC Validation
open UnitTest

private def hasContext : RecordType :=
  Map.make [
    ("a", .optional (.bool .anyBool)),
    ("x", .required (.bool .anyBool)),
  ]

private def hasTypeEnv := BasicTypes.env Map.empty Map.empty hasContext

private def getₐ : Expr := .getAttr (.var .context) "a"
private def getₓ : Expr := .getAttr (.var .context) "x"

private def hasₐ : Expr := .hasAttr (.var .context) "a"
private def hasₓ : Expr := .hasAttr (.var .context) "x"

def testsForBasicHasOps :=
  suite "Has.basic" $ List.flatten
  [
    testVerifyEquivalent "True: context has x"
      hasₓ
      (.lit (.bool true))
      hasTypeEnv .unsat,

    [testFailsCompilePolicy "Error: context.a" getₐ hasTypeEnv],
    [testFailsCompilePolicies "Error: context.a" getₐ hasTypeEnv],

    testVerifyNoError "Okay: context has a && context.a"
      (.and hasₐ getₐ)
      hasTypeEnv .unsat,

    -- this policy never errors at runtime, but our current validator is not
    -- powerful enough to validate this policy.
    -- however, if you were to feed this policy directly to the symbolic
    -- compiler (that is, if compilation did not require typechecking first --
    -- see also the notes in SymTest/WellTyped.lean), the symbolic compiler
    -- would correctly handle this policy and `testVerifyNoError` would confirm
    -- it never errors
    [testFailsCompilePolicy "Error: !(!(context has a)) && context.a"
      (.and (.unaryApp .not (.unaryApp .not hasₐ)) getₐ)
      hasTypeEnv],

    -- this policy never errors at runtime, but our current validator is not
    -- powerful enough to validate this policy.
    -- however, if you were to feed this policy directly to the symbolic
    -- compiler (that is, if compilation did not require typechecking first --
    -- see also the notes in SymTest/WellTyped.lean), the symbolic compiler
    -- would correctly handle this policy and `testVerifyNoError` would confirm
    -- it never errors
    [testFailsCompilePolicy "Error: !(context has a) || context.a"
      (.or (.unaryApp .not hasₐ) getₐ)
      hasTypeEnv],

    -- this policy never errors at runtime, but our current validator is not
    -- powerful enough to validate this policy.
    -- however, if you were to feed this policy directly to the symbolic
    -- compiler (that is, if compilation did not require typechecking first --
    -- see also the notes in SymTest/WellTyped.lean), the symbolic compiler
    -- would correctly handle this policy and `testVerifyEquivalent` would give
    -- the Equivalent result
    [testFailsCompilePolicy "Error: (context.x == context has a) && (context.x && context.a)"
      (.and (.binaryApp .eq getₓ hasₐ) (.and getₓ getₐ))
      -- would be equivalent to: (.and getₐ (.and hasₐ getₐ))
      hasTypeEnv],
  ]

def tests := [
  testsForBasicHasOps
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.Has
