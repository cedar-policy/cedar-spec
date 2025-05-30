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

/-! This file unit tests symbolic evaluation of the `hasTag` and `getTag` operators. -/

namespace SymTest.Tags

open Cedar Data Spec SymCC Validation
open UnitTest

private def ctx : RecordType :=
  Map.make [
    ("key", .required .string)
  ]

private def noTagsEnv := SymEnv.ofEnv (BasicTypes.env Map.empty Map.empty ctx)
private def tagsEnv := SymEnv.ofEnv (BasicTypes.env Map.empty Map.empty ctx (.some (.bool .anyBool)))

private def hasₐ : Expr := .binaryApp .hasTag (.var .principal) (.lit (.string "a"))
private def hasₖ : Expr := .binaryApp .hasTag (.var .principal) (.getAttr (.var .context) "key")

private def getₐ : Expr := .binaryApp .getTag (.var .principal) (.lit (.string "a"))
private def getₖ : Expr := .binaryApp .getTag (.var .principal) (.getAttr (.var .context) "key")

def testsForTagOps :=
  suite "Tags.basic"
  [
    testReduce "False: principal.hasTag(\"a\")"
      hasₐ
      noTagsEnv
      (.ok (.some false)),

    testVerifyNoError "No error: principal.hasTag(\"a\")"
      hasₐ
      tagsEnv .unsat,

    testVerifyNoError "No error: principal.hasTag(context.key)"
      hasₖ
      tagsEnv .unsat,

    testVerifyNoError "Error: principal.getTag(\"a\")"
      getₐ
      tagsEnv .sat,

    testVerifyNoError "Error: principal.getTag(context.key)"
      getₖ
      tagsEnv .sat,

    testVerifyNoError "Okay: principal.hasTag(\"a\") && principal.getTag(\"a\")"
      (.and hasₐ getₐ)
      tagsEnv .unsat,

    testVerifyNoError "Okay: !(!(principal.hasTag(\"a\"))) && principal.getTag(\"a\")"
      (.and (.unaryApp .not (.unaryApp .not hasₐ)) getₐ)
      tagsEnv .unsat,

    testVerifyNoError "Okay: !(principal.hasTag(\"a\")) || principal.getTag(\"a\")"
      (.or (.unaryApp .not hasₐ) getₐ)
      tagsEnv .unsat,

    testVerifyEquivalent "Equivalent: (context.key == \"a\") && (principal.hasTag(context.key) && principal.getTag(\"a\")) <==> (context.key == \"a\") && principal.hasTag(\"a\") && principal.getTag(\"a\")"
      (.and (.binaryApp .eq  (.getAttr (.var .context) "key") (.lit (.string "a"))) (.and hasₖ getₐ))
      (.and (.binaryApp .eq  (.getAttr (.var .context) "key") (.lit (.string "a"))) (.and hasₐ getₐ))
      tagsEnv .unsat,
  ]

def tests := [
  testsForTagOps
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.Tags
