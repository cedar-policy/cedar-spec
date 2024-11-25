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

import Cedar.Spec.Ext.Datetime
import UnitTest.Run

/-! This file defines unit tests for Datetime functions. -/

namespace UnitTest.Datetime

open Cedar.Spec.Ext.Datetime

theorem test1 : toString ((Duration.parse "1ms").get!) = "1" := by native_decide
theorem test2 : toString ((Duration.parse "1s").get!) = "1000" := by native_decide
theorem test3 : toString ((Duration.parse "1m").get!) = "60000" := by native_decide
theorem test4 : toString ((Duration.parse "1h").get!) = "360000" := by native_decide
theorem test5 : toString ((Duration.parse "1d").get!) = "86400000" := by native_decide
theorem test6 : toString ((Duration.parse "1d2h3m4s5ms").get!) = "87304005" := by native_decide
theorem test7 : toString ((Duration.parse "2d12h").get!) = "177120000" := by native_decide
theorem test8 : toString ((Duration.parse "3m30s").get!) = "210000" := by native_decide
theorem test9 : toString ((Duration.parse "1h30m45s").get!) = "2205000" := by native_decide
theorem test10 : toString ((Duration.parse "2d5h20m").get!) = "175800000" := by native_decide
theorem test11 : toString ((Duration.parse "-1d12h").get!) = "-90720000" := by native_decide
theorem test12 : toString ((Duration.parse "-3h45m").get!) = "-3780000" := by native_decide
theorem test13 : toString ((Duration.parse "1d1ms").get!) = "86400001" := by native_decide
theorem test14 : toString ((Duration.parse "59m59s999ms").get!) = "3599999" := by native_decide
theorem test15 : toString ((Duration.parse "23h59m59s999ms").get!) = "11879999" := by native_decide
theorem test16 : toString ((Duration.parse "0d0h0m0s0ms").get!) = "0" := by native_decide

private def testValid (str : String) (rep : Int) : TestCase IO :=
  test str ⟨λ _ => checkEq (Duration.parse str) (duration? rep)⟩

def testsForValidDurationStrings :=
  suite "Duration.parse for valid strings"
  [
    testValid "0ms" 0,
    testValid "0d0s" 0,
    testValid "1ms" 1,
    testValid "1s" 1000,
    testValid "1m" 60000,
    testValid "1h" 360000,
    testValid "1d" 86400000,
    testValid "12s340ms" 12340,
    testValid "1s234ms" 1234,
    testValid "-1s" (-1000),
    testValid "-4s200ms" (-4200),
    testValid "-9s876ms" (-9876),
    testValid "106751d23h47m16s854ms" 9223297516854,
    testValid "-106751d23h47m16s854ms" (-9223297516854),
    testValid "1d2h3m4s5ms" 87304005,
    testValid "2d12h" 177120000,
    testValid "3m30s" 210000,
    testValid "1h30m45s" 2205000,
    testValid "2d5h20m" 175800000,
    testValid "-1d12h" (-90720000),
    testValid "-3h45m" (-3780000),
    testValid "1d1ms" 86400001,
    testValid "59m59s999ms" 3599999,
    testValid "23h59m59s999ms" 11879999
  ]

private def testInvalid (str : String) (msg : String) : TestCase IO :=
  test s!"{str} [{msg}]" ⟨λ _ => checkEq (Duration.parse str) .none⟩

def testsForInvalidDurationStrings :=
  suite "Duration.parse for invalid strings"
  [
    testInvalid "" "empty string",
    testInvalid "d" "unit but no amount",
    testInvalid "1d-1s" "invalid use of -",
    testInvalid "1d2h3m4s5ms6" "trailing amount",
    testInvalid "1x2m3s" "invalid unit",
    testInvalid "1.23s" "amounts must be integral",
    testInvalid "1s1d" "invalid order",
    testInvalid "1s1s" "repeated units",
    testInvalid "1d2h3m4s5ms " "trailing space",
    testInvalid " 1d2h3m4s5ms" "leading space",
    testInvalid "1d9223372036854775807ms" "overflow",
    testInvalid "1d92233720368547758071ms" "overflow ms",
    testInvalid "9223372036854776s1ms" "overflow s"
  ]

def tests := [testsForValidDurationStrings, testsForInvalidDurationStrings]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.Datetime
