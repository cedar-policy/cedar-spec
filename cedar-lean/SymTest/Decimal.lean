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

/-! This file unit tests symbolic evaluation of Decimal operators. -/

namespace SymTest.Decimal

open Cedar Data Spec SymCC Validation
open UnitTest

private def decimalContext : RecordType :=
  Map.make [
    ("x", .required (.ext .decimal)),
    ("y", .required (.ext .decimal)),
    ("z", .required (.ext .decimal)),
    ("s", .required .string)
  ]

private def decimalTypeEnv := BasicTypes.env Map.empty Map.empty decimalContext
private def decimalSymEnv  := SymEnv.ofEnv decimalTypeEnv

private def x : Expr := .getAttr (.var .context) "x"
private def y : Expr := .getAttr (.var .context) "y"
private def z : Expr := .getAttr (.var .context) "z"
private def s : Expr := .getAttr (.var .context) "s"

def decLit (str : String) : Expr :=
  .call .decimal [.lit (.string str)]

private def testValid (str : String) (rep : Int) : TestCase SolverM :=
  testReduce str
    (decLit str)
    decimalSymEnv
    (.ok (.some (.prim (.ext (.decimal (Ext.Decimal.decimal? rep).get!)))))

private def testInvalid (str : String) (msg : String) : TestCase SolverM :=
  testReduce s!"{str} [{msg}]"
    (decLit str)
    decimalSymEnv
    (.error .typeError)

def testsForDecimalConstructor :=
  suite "Decimal.decimal"
  [
    testValid "0.0" 0,
    testValid "0.0000" 0,
    testValid "12.34" 123400,
    testValid "1.2345" 12345,
    testValid "-1.0" (-10000),
    testValid "-4.2" (-42000),
    testValid "-9.876" (-98760),
    testValid "-922337203685477.5808" (-9223372036854775808),
    testValid "922337203685477.5807" 9223372036854775807,
    testInvalid "1.x" "invalid characters",
    testInvalid "1.-2" "invalid use of -",
    testInvalid "12" "no decimal point",
    testInvalid ".12" "no integer part",
    testInvalid "-.12" "no integer part",
    testInvalid "12." "no fractional part",
    testInvalid "1.23456" "too many fractional digits",
    testInvalid "922337203685477.5808" "overflow",
    testInvalid "-922337203685477.5809" "overflow",
    testReduce s!"Error: applying decimal constructor to a non-literal"
      (.call .decimal [s])
      decimalSymEnv
      (.error .typeError)
  ]

def testsForDecimalComparisonOperations :=
  suite "Decimal.comparisons"
  [
    testVerifyEquivalent "True: x lessThanOrEqual 922337203685477.5807"
      (.call .lessThanOrEqual [x, decLit "922337203685477.5807"])
      (.lit (.bool true))
      decimalSymEnv .unsat,

    testVerifyEquivalent "True: 922337203685477.5807 greaterThanOrEqual x"
      (.call .greaterThanOrEqual [decLit "922337203685477.5807", x])
      (.lit (.bool true))
      decimalSymEnv .unsat,

    testVerifyEquivalent "True: x greaterThanOrEqual -922337203685477.5808"
      (.call .greaterThanOrEqual [x, decLit "-922337203685477.5808"])
      (.lit (.bool true))
      decimalSymEnv .unsat,

    testVerifyEquivalent "True: -922337203685477.5808 lessThanOrEqual x"
      (.call .lessThanOrEqual [decLit "-922337203685477.5808", x])
      (.lit (.bool true))
      decimalSymEnv .unsat,

    testVerifyImplies "Implies: x != 922337203685477.5807 ==> x lessThan 922337203685477.5807"
      (.unaryApp .not (.binaryApp .eq x (decLit "922337203685477.5807")))
      (.call .lessThan [x, decLit "922337203685477.5807"])
      decimalSymEnv .unsat,

    testVerifyImplies "Implies: x != -922337203685477.5808 ==> x greaterThan -922337203685477.5808"
      (.unaryApp .not (.binaryApp .eq x (decLit "-922337203685477.5808")))
      (.call .greaterThan [x, decLit "-922337203685477.5808"])
      decimalSymEnv .unsat,

    testVerifyImplies "Implies: x lessThan y ==> y greaterThan x"
      (.call .lessThan [x, y])
      (.call .greaterThan [y, x])
      decimalSymEnv .unsat,

    testVerifyImplies "Implies: x lessThanOrEqual y ==> y greaterThanOrEqual x"
      (.call .lessThanOrEqual [x, y])
      (.call .greaterThanOrEqual [y, x])
      decimalSymEnv .unsat,

    testVerifyImplies "Implies: x lessThanOrEqual y && y lessThanOrEqual x ==> x = y"
      (.and
        (.call .lessThanOrEqual [x, y])
        (.call .lessThanOrEqual [y, x]))
      (.binaryApp .eq x y)
      decimalSymEnv .unsat,

    testVerifyImplies "Implies: x lessThan y && x lessThan z ==> z greaterThan x"
      (.and
        (.call .lessThan [x, y])
        (.call .lessThan [y, z]))
      (.call .greaterThan [z, x])
      decimalSymEnv .unsat,
  ]

def tests := [
  testsForDecimalConstructor,
  testsForDecimalComparisonOperations
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.Decimal
