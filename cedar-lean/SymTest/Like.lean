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

/-! This file unit tests symbolic evaluation of the `like` operator on strings. -/

namespace SymTest.Like

open Cedar Data Spec SymCC Validation
open UnitTest

private def likeContext : RecordType :=
  Map.make [
    ("x", .required .string),
    ("y", .required .string),
    ("z", .required .string)
  ]

private def likeTypeEnv := BasicTypes.env Map.empty Map.empty likeContext
private def likeSymEnv  := SymEnv.ofEnv likeTypeEnv

private def x : Expr := .getAttr (.var .context) "x"
private def y : Expr := .getAttr (.var .context) "y"
private def z : Expr := .getAttr (.var .context) "z"

private def justChars : String → Pattern
  | .mk [] => []
  | .mk (c :: cs) => (.justChar c) :: (justChars (.mk cs))

def testsForBasicLikeOps :=
  suite "Like.basic"
  [
    testVerifyEquivalent "False: x != \"\" && x like \"\""
      (.and
        (.unaryApp .not (.binaryApp .eq x (.lit (.string ""))))
        (.unaryApp (.like []) x))
      (.lit (.bool false))
      likeSymEnv .unsat,

    testVerifyEquivalent "False: x != \"a\" && x like \"a\""
      (.and
        (.unaryApp .not (.binaryApp .eq x (.lit (.string "a"))))
        (.unaryApp (.like (justChars "a")) x))
      (.lit (.bool false))
      likeSymEnv .unsat,

    testVerifyEquivalent "True: x != \"a*Cd\" || x like \"a\\*Cd\""
      (.or
        (.unaryApp .not (.binaryApp .eq x (.lit (.string "a*Cd"))))
        (.unaryApp (.like (justChars "a*Cd")) x))
      (.lit (.bool true))
      likeSymEnv .unsat,

    testVerifyEquivalent "True: x like \"*\""
      (.unaryApp (.like [.star]) x)
      (.lit (.bool true))
      likeSymEnv .unsat,

    testVerifyEquivalent "True: !(x like \"ab***12\") || x like \"ab*2\""
      (.or
        (.unaryApp .not
          (.unaryApp
            (.like [.justChar 'a', .justChar 'b', .star, .star, .star, .justChar '1', .justChar '2'])
            x))
        (.unaryApp
          (.like [.justChar 'a', .justChar 'b', .star, .justChar '2'])
          x))
      (.lit (.bool true))
      likeSymEnv .unsat,
  ]

def tests := [
  testsForBasicLikeOps
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.Like
