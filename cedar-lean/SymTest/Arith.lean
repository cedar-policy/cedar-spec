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

/-! This file unit tests symbolic compilation of arithmetic operators. -/

namespace SymTest.Arith

open Cedar Data Spec SymCC Validation
open UnitTest

private def arithContext : RecordType :=
  Map.make [
    ("x", .required .int),
    ("y", .required .int),
    ("z", .required .int)
  ]

private def arithTypeEnv := BasicTypes.env Map.empty Map.empty arithContext
private def arithSymEnv  := SymEnv.ofEnv arithTypeEnv

private def x : Expr := .getAttr (.var .context) "x"
private def y : Expr := .getAttr (.var .context) "y"
private def z : Expr := .getAttr (.var .context) "z"

def testsForBasicArithEqualities :=
  suite "Arith.basic"
  [
    testVerifyEquivalent "Equivalent: x + 0 = x"
      (.binaryApp .eq
        (.binaryApp .add x (.lit (.int 0)))
        x)
      (.lit (.bool true))
      arithSymEnv .unsat,

    testVerifyEquivalent "Equivalent: x - 0 = x"
      (.binaryApp .eq
        (.binaryApp .sub x (.lit (.int 0)))
        x)
      (.lit (.bool true))
      arithSymEnv .unsat,

    testVerifyEquivalent "Equivalent: x - x = 0"
      (.binaryApp .eq
        (.binaryApp .sub x x)
        (.lit (.int 0)))
      (.lit (.bool true))
      arithSymEnv .unsat,

    testVerifyEquivalent "Equivalent: x * 1 = x"
      (.binaryApp .eq
        (.binaryApp .mul (.lit (.int 1)) x)
        x)
      (.lit (.bool true))
      arithSymEnv .unsat,

    testVerifyEquivalent "Equivalent: (x <= y and y <= x) = (x = y)"
      (.binaryApp .eq
        (.and
          (.binaryApp .lessEq x y)
          (.binaryApp .lessEq y x))
        (.binaryApp .eq x y))
      (.lit (.bool true))
      arithSymEnv .unsat,

    testVerifyEquivalent "Equivalent: (x < y) = not (y <= x)"
      (.binaryApp .eq
        (.binaryApp .less x y)
        (.unaryApp .not (.binaryApp .lessEq y x)))
      (.lit (.bool true))
      arithSymEnv .unsat,
  ]

private def inRange (x : Expr) (lo hi : Int64) : Expr :=
  .and
    (.binaryApp .lessEq (.lit (.int lo)) x)
    (.binaryApp .lessEq x (.lit (.int hi)))

def testsForOverflowSemantics :=
  suite "Arith.overflow"
  [
    testVerifyNoError "Overflow: x + y = y + x"
      (.binaryApp .eq (.binaryApp .add x y) (.binaryApp .add y x))
      arithSymEnv .sat,

    testVerifyNoError "Overflow: x = - (- x)"
      (.binaryApp .eq x (.unaryApp .neg (.unaryApp .neg x)))
      arithSymEnv .sat,

    testVerifyNoError "Overflow: x - y = - y + x"
      (.binaryApp .eq (.binaryApp .sub x y) (.binaryApp .add (.unaryApp .neg y) x))
      arithSymEnv .sat,

    testVerifyNoError "Overflow: x + x = x * 2"
      (.binaryApp .eq (.binaryApp .add x x) (.binaryApp .mul (.lit (.int 2)) x))
      arithSymEnv .sat,

    testVerifyNoError "No overflow: x = 0 && x + y = y + x"
      (.and
        (.binaryApp .eq x (.lit (.int 0)))
        (.binaryApp .eq (.binaryApp .add x y) (.binaryApp .add y x)))
      arithSymEnv .unsat,

    testVerifyImplies "Implies: (-100 <= x && x <= 100) && (-100 <= y && y <= 100) ==> x + y = y + x"
      (.and (inRange x (-100) 100) (inRange y (-100) 100))
      (.binaryApp .eq (.binaryApp .add x y) (.binaryApp .add y x))
      arithSymEnv .unsat,

    testVerifyImplies "Implies: INT64_MIN < x ==> x = - (- x)"
      (.binaryApp .less (.lit (.int (Int64.ofIntChecked Int64.MIN (by decide)))) x)
      (.binaryApp .eq x (.unaryApp .neg (.unaryApp .neg x)))
      arithSymEnv .unsat,

    testVerifyImplies "Implies: (-100 <= x && x <= 100) && (-100 <= y && y <= 100) ==> x - y = - y + x"
      (.and (inRange x (-100) 100) (inRange y (-100) 100))
      (.binaryApp .eq (.binaryApp .sub x y) (.binaryApp .add (.unaryApp .neg y) x))
      arithSymEnv .unsat,

    testVerifyImplies "Implies: (-100 <= x && x <= 100) && (-100 <= y && y <= 100) ==>  x + x = x * 2"
      (.and (inRange x (-100) 100) (inRange y (-100) 100))
      (.binaryApp .eq (.binaryApp .add x x) (.binaryApp .mul (.lit (.int 2)) x))
      arithSymEnv .unsat,

    testVerifyEquivalent "False: x == - 3 && y == 5 && z == 4 * (y - x) + 9223372036854775807 && z != 9223372036854775839"
      (.and
        (.binaryApp .eq x (.unaryApp .neg (.lit (.int 3))))
        (.and
          (.binaryApp .eq y (.lit (.int 5)))
          (.and
            (.binaryApp .eq z
              (.binaryApp .add
                (.binaryApp .mul (.lit (.int 4)) (.binaryApp .sub y x))
                (.lit (.int 9223372036854775807))))
            (.unaryApp .not
              (.binaryApp .eq z (.lit (.int 9223372036854775839)))))))
      (.lit (.bool false))
      arithSymEnv .unsat,

    testVerifyImplies "Nothing other than 0 should satisfy x = -x"
      (.and
        (.unaryApp .not (.binaryApp .eq x (.lit (.int 0))))
        (.binaryApp .eq x (.unaryApp .neg x))
      )
      (.lit (.bool false))
      arithSymEnv .unsat,
  ]

def tests := [
  testsForBasicArithEqualities,
  testsForOverflowSemantics
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.Arith
