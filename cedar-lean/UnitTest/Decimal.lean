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

import Cedar.Spec.Ext.Decimal
import UnitTest.Run

/-! This file defines unit tests for Decimal functions. -/

namespace UnitTest.Decimal

open Cedar.Spec.Ext.Decimal

theorem test1 : unParse ((parse "3.14").get!) = "3.1400" := by decide
theorem test2 : unParse ((parse "11.0003").get!) = "11.0003" := by decide
theorem test3 : unParse ((parse "11.003").get!) = "11.0030" := by decide
theorem test4 : unParse ((parse "11.3000").get!) = "11.3000" := by decide
theorem test5 : unParse ((parse "123.0").get!) = "123.0000" := by decide
theorem test6 : unParse ((parse "-123.0").get!) = "-123.0000" := by decide
theorem test7 : unParse ((parse "-3.14").get!) = "-3.1400" := by decide
theorem test8 : unParse ((parse "-11.0003").get!) = "-11.0003" := by decide

private def testValid (str : String) (rep : Int) : TestCase IO :=
  test str ⟨λ _ => checkEq (parse str) (decimal? rep)⟩

def testsForValidStrings :=
  suite "Decimal.parse for valid strings"
  [
    testValid "0.0" 0,
    testValid "0.0000" 0,
    testValid "12.34" 123400,
    testValid "1.2345" 12345,
    testValid "-1.0" (-10000),
    testValid "-4.2" (-42000),
    testValid "-9.876" (-98760),
    testValid "-922337203685477.5808" (-9223372036854775808),
    testValid "922337203685477.5807" 9223372036854775807
  ]

private def testInvalid (str : String) (msg : String) : TestCase IO :=
  test s!"{str} [{msg}]" ⟨λ _ => checkEq (parse str) .none⟩

def testsForInvalidStrings :=
  suite "Decimal.parse for invalid strings"
  [
    testInvalid "1.x" "invalid characters",
    testInvalid "1.-2" "invalid use of -",
    testInvalid "12" "no decimal point",
    testInvalid ".12" "no integer part",
    testInvalid "-.12" "no integer part",
    testInvalid "12." "no fractional part",
    testInvalid "1.23456" "too many fractional digits",
    testInvalid "922337203685477.5808" "overflow",
    testInvalid "-922337203685477.5809" "overflow"
  ]

def tests := [testsForValidStrings, testsForInvalidStrings]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.Decimal
