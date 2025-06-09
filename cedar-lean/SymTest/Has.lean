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
private def hasSymEnv  := SymEnv.ofEnv hasTypeEnv

private def getₐ : Expr := .getAttr (.var .context) "a"
private def getₓ : Expr := .getAttr (.var .context) "x"

private def hasₐ : Expr := .hasAttr (.var .context) "a"
private def hasₓ : Expr := .hasAttr (.var .context) "x"

def testsForBasicHasOps :=
  suite "Has.basic"
  [
    testVerifyEquivalent "True: context has x"
      hasₓ
      (.lit (.bool true))
      hasSymEnv .unsat,

    testVerifyNoError "Error: context.a"
      getₐ
      hasSymEnv .sat,

    testVerifyNoError "Okay: context has a && context.a"
      (.and hasₐ getₐ)
      hasSymEnv .unsat,

    testVerifyNoError "Okay: !(!(context has a)) && context.a"
      (.and (.unaryApp .not (.unaryApp .not hasₐ)) getₐ)
      hasSymEnv .unsat,

    testVerifyNoError "Okay: !(context has a) || context.a"
      (.or (.unaryApp .not hasₐ) getₐ)
      hasSymEnv .unsat,

    testVerifyEquivalent "Equivalent: (context.x == context has a) && (context.x && context.a) <==> context.x && context has a && context.a"
      (.and (.binaryApp .eq getₓ hasₐ) (.and getₓ getₐ))
      (.and getₓ (.and hasₐ getₐ))
      hasSymEnv .unsat,
  ]

def tests := [
  testsForBasicHasOps
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.Has
