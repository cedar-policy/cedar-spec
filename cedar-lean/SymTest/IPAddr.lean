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

/-! This file unit tests symbolic compilation of IPAddr operators. -/

namespace SymTest.IPAddr

open Cedar Data Spec SymCC Validation
open UnitTest

private def ipContext : RecordType :=
  Map.make [
    ("x", .required (.ext .ipAddr)),
    ("y", .required (.ext .ipAddr)),
    ("z", .required (.ext .ipAddr)),
    ("s", .required .string)
  ]

private def ipTypeEnv := BasicTypes.env Map.empty Map.empty ipContext
private def ipSymEnv  := SymEnv.ofEnv ipTypeEnv

private def x : Expr := .getAttr (.var .context) "x"
private def y : Expr := .getAttr (.var .context) "y"
private def z : Expr := .getAttr (.var .context) "z"
private def s : Expr := .getAttr (.var .context) "s"

def ipLit (str : String) : Expr :=
  .call .ip [.lit (.string str)]

private def testValid (str : String) : TestCase SolverM :=
  testCompile str
    (ipLit str)
    ipSymEnv
    (.ok (.some (IPAddr.ipTerm (Ext.IPAddr.ip str).get!)))

private def testInvalid (str : String) (msg : String) : TestCase SolverM :=
  testCompile s!"{str} [{msg}]"
    (ipLit str)
    ipSymEnv
    (.error .typeError)

def testsForIpConstructor :=
  suite "IPAddr.ip"
  [
    testValid "127.0.0.1",
    testValid "127.3.4.1/2",
    testValid "::",
    testValid "::/5",
    testValid "a::",
    testValid "::f",
    testValid "F:AE::F:5:F:F:0",
    testValid "a::f/120",
    testInvalid "127.0.a.1" "no hex in IPv4",
    testInvalid "127.3.4.1/33" "prefix out of range",
    testInvalid "::::" "too many double colons",
    testInvalid "::f::" "too many double colons",
    testInvalid "F:AE::F:5:F:F:0:0" "too many groups",
    testInvalid "F:A:F:5:F:F:0:0:1" "too many groups",
    testInvalid "F:A" "too few groups",
    testInvalid "::ffff1" "group out of range",
    testInvalid "F:AE::F:5:F:F:0/129" "prefix out of range",
    testInvalid "::ffff:127.0.0.1" "no IPv4 embedded in IPv6",
    testInvalid "::/00" "no leading zeros",
    testInvalid "::/01" "no leading zeros",
    testInvalid "::/001" "no leading zeros",
    testInvalid "127.0.0.1/01" "no leading zeros",
    testInvalid "F:AE::F:5:F:F:0/01" "no leading zeros",
    testCompile s!"Error: applying ip constructor to a non-literal"
      (.call .ip [s])
      ipSymEnv
      (.error .typeError)
  ]

private def testIs (msg : String) (isFun : ExtFun) (x : Expr) (expected : Bool) : TestCase SolverM :=
  testCompile s!"Expected {expected}: {reprStr isFun} {msg}]"
    (.call isFun [x])
    ipSymEnv
    (.ok (.some expected))

private def testIsLoopback (msg : String) (x : Expr) (expected : Bool) : TestCase SolverM :=
  testIs msg .isLoopback x expected

private def testIsMulticast (msg : String) (x : Expr) (expected : Bool) : TestCase SolverM :=
  testIs msg .isMulticast x expected

private def testInRange (str₁ str₂ : String) (expected : Bool) : TestCase SolverM :=
  testCompile s!"Expected {expected}: inRange {str₁} {str₂}]"
    (.call .isInRange [(ipLit str₁), (ipLit str₂)])
    ipSymEnv
    (.ok (.some expected))

def testsForIsLoopback :=
  suite "IPAddr.isLoopback"
  [
    testIsLoopback "127.0.0.1" (ipLit "127.0.0.1") true,
    testIsLoopback "::B" (ipLit "::B") false,
    testIsLoopback "::1" (ipLit "::1") true,
    testIsLoopback "::ffff:ff00:0001" (ipLit "::ffff:ff00:0001") false,

    testVerifyImplies "Implies: x == ip(127.0.0.1) || x == ip(::1) ==> x.isLoopback"
      (.or
        (.binaryApp .eq x (ipLit "127.0.0.1"))
        (.binaryApp .eq x (ipLit "::1")) )
      (.call .isLoopback [x])
      ipSymEnv .unsat,

    testVerifyImplies "Implies: x == ip(::B) || x == ip(::ffff:ff00:0001) ==> !x.isLoopback"
      (.or
        (.binaryApp .eq x (ipLit "::B"))
        (.binaryApp .eq x (ipLit "::ffff:ff00:0001")) )
      (.unaryApp .not (.call .isLoopback [x]))
      ipSymEnv .unsat
  ]

def testsForIsMulticast :=
  suite "IPAddr.isMulticast"
  [
    testIsMulticast "224.0.0.0" (ipLit "224.0.0.0") true,
    testIsMulticast "225.1.0.0" (ipLit "225.1.0.0") true,
    testIsMulticast "FF00::" (ipLit "FF00::") true,
    testIsMulticast "223.0.0.0" (ipLit "223.0.0.0") false,
    testIsMulticast "1.0.0.1" (ipLit "1.0.0.1") false,
    testIsMulticast "EF00::" (ipLit "EF00::") false,

    testVerifyImplies "Implies: x == ip(224.0.0.0) || x == ip(FF00::) ==> x.isMulticast"
      (.or
        (.binaryApp .eq x (ipLit "224.0.0.0"))
        (.binaryApp .eq x (ipLit "FF00::")) )
      (.call .isMulticast [x])
      ipSymEnv .unsat,

    testVerifyImplies "Implies: x == ip(223.0.0.0) || x == ip(EF00::) ==> !x.isMulticast"
      (.or
        (.binaryApp .eq x (ipLit "223.0.0.0"))
        (.binaryApp .eq x (ipLit "EF00::")) )
      (.unaryApp .not (.call .isMulticast [x]))
      ipSymEnv .unsat
  ]

def testsForIsInRange :=
  suite "IPAddr.isInRange"
  [
    testInRange "238.238.238.238" "238.238.238.41/12" true,
    testInRange "238.238.238.238" "238.238.238.238" true,
    testInRange "F:AE::F:5:F:F:0" "F:AE::F:5:F:F:0" true,
    testInRange "F:AE::F:5:F:F:1" "F:AE::F:5:F:F:0/127" true,
    testInRange "F:AE::F:5:F:F:2" "F:AE::F:5:F:F:0/127" false,
    testInRange "0.0.0.0" "::" false,
    testInRange "::" "0.0.0.0" false,
    testInRange "10.0.0.0" "10.0.0.0/24" true,
    testInRange "10.0.0.0" "10.0.0.0/32" true,
    testInRange "10.0.0.0" "10.0.0.1/24" true,
    testInRange "10.0.0.0" "10.0.0.1/32" false,
    testInRange "10.0.0.1" "10.0.0.0/24" true,
    testInRange "10.0.0.1" "10.0.0.1/24" true,
    testInRange "10.0.0.0/24" "10.0.0.0/32" false,
    testInRange "10.0.0.0/32" "10.0.0.0/24" true,
    testInRange "10.0.0.1/24" "10.0.0.0/24" true,
    testInRange "10.0.0.1/24" "10.0.0.1/24" true,
    testInRange "10.0.0.0/24" "10.0.0.1/24" true,
    testInRange "10.0.0.0/24" "10.0.0.0/29" false,
    testInRange "10.0.0.0/29" "10.0.0.0/24" true,
    testInRange "10.0.0.0/24" "10.0.0.1/29" false,
    testInRange "10.0.0.0/29" "10.0.0.1/24" true,
    testInRange "10.0.0.1/24" "10.0.0.0/29" false,
    testInRange "10.0.0.1/29" "10.0.0.0/24" true,
    testInRange "10.0.0.0/32" "10.0.0.0/32" true,
    testInRange "10.0.0.0/32" "10.0.0.0" true,
    testInRange "0.0.0.0/31" "0.0.0.1/31" true,
    testInRange "0.0.0.1/31" "0.0.0.0/31" true,

    testVerifyImplies "Implies: x.isInRange(y) && y.isInRange(z) ==> x.isInRange(z)"
      (.and
        (.call .isInRange [x, y])
        (.call .isInRange [y, z]))
      (.call .isInRange [x, z])
      ipSymEnv .unsat,

    testVerifyImplies "Not implies: x.isInRange(y) && y.isInRange(x) ==> x == y"
      (.and
        (.call .isInRange [x, y])
        (.call .isInRange [y, x]))
      (.binaryApp .eq x y)
      ipSymEnv .sat, -- consider x = 0.0.0.0/31, y = 0.0.0.1/31

    testVerifyImplies "Implies: x == y ==> x.isInRange(y) && y.isInRange(x)"
      (.binaryApp .eq x y)
      (.and
        (.call .isInRange [x, y])
        (.call .isInRange [y, x]))
      ipSymEnv .unsat,
  ]

def tests := [
  testsForIpConstructor,
  testsForIsLoopback,
  testsForIsMulticast,
  testsForIsInRange
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.IPAddr
