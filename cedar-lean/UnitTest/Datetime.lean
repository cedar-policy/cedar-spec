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


theorem testDatetime1 : toString ((parse "2022-10-10").get!) = "1665360000000" := by native_decide
theorem testDatetime2 : toString ((parse "1969-12-31").get!) = "-86400000" := by native_decide

private def testValidDatetime (str : String) (rep : Int) : TestCase IO :=
  test str ⟨λ _ => checkEq (parse str) (datetime? rep)⟩

def testsForValidDatetimeStrings :=
  suite "Datetime.parse for valid strings"
  [
    testValidDatetime "1970-01-01" 0,
    testValidDatetime "1969-12-31T23:59:59Z" (-1000 : Int),
    -- testValidDatetime "1969-12-31T23:59:59.999Z" (-1 : Int), -- TODO: Bug in dates before 1970
    testValidDatetime "2024-10-15" 1728950400000,
    testValidDatetime "2024-10-15T11:38:02Z" 1728992282000,
    testValidDatetime "2024-10-15T11:38:02.101Z" 1728992282101,
    testValidDatetime "2024-10-15T11:38:02.101-1134" 1729033922101,
    testValidDatetime "2024-10-15T11:38:02.101+1134" 1728950642101,
    testValidDatetime "2024-10-15T11:38:02+1134" 1728950642000,
    testValidDatetime "2024-10-15T11:38:02-1134" 1729033922000,
    testValidDatetime "2016-12-31T23:59:60Z" 1483228800000, -- the last leap second // TODO: LEAN-RUST DIFF
    testValidDatetime "2017-01-01" 1483228800000, -- same date without leap second // TODO: LEAN-RUST DIFF
  ]

private def testInvalidDatetime (str : String) (msg : String) : TestCase IO :=
  test s!"{str} [{msg}]" ⟨λ _ => checkEq (parse str) .none⟩

def testsForInvalidDatetimeStrings :=
  suite "Datetime.parse for invalid strings"
  [
    testInvalidDatetime "" "empty string",
    testInvalidDatetime "a" "string is letter",
    testInvalidDatetime "-" "string is character",
    testInvalidDatetime "-1" "string is integer",
    testInvalidDatetime "11-12-13" "two digits for year",
    testInvalidDatetime "1111-1x-20" "invalid month",
    testInvalidDatetime "2024-10-15Z" "Zulu code invalid for date",
    testInvalidDatetime "2024-10-15T11:38:02ZZ" "double Zulu code",
    testInvalidDatetime "2024-01-01T" "separator not needed",
    testInvalidDatetime "2024-01-01Ta" "invalid time: character",
    testInvalidDatetime "2024-01-01T01:" "invalid time: only hours",
    testInvalidDatetime "2024-01-01T01:02" "invalid time: no seconds",
    testInvalidDatetime "2024-01-01T01:02:0b" "invalid time: character",
    testInvalidDatetime "2024-01-01T01::02:03" "invalid time: double colon",
    testInvalidDatetime "2024-01-01T01::02::03" "invalid time: double colons",
    testInvalidDatetime "2024-01-01T31:02:03Z" "invalid time: hour offset",
    testInvalidDatetime "2024-01-01T01:60:03Z" "invalid time: minute offset",
    -- testInvalidDatetime "2016-12-31T23:59:60Z" "invalid time: leap second", -- TODO: LEAN-RUST DIFF
    testInvalidDatetime "2016-12-31T23:59:61Z" "invalid time: second offset",
    testInvalidDatetime "2024-01-01T00:00:00" "timezone not specified",
    testInvalidDatetime "2024-01-01T00:00:00T" "separator is not timezone",
    testInvalidDatetime "2024-01-01T00:00:00ZZ" "double Zulu code",
    testInvalidDatetime "2024-01-01T00:00:00x001Z" "typo in milliseconds separator",
    testInvalidDatetime "2024-01-01T00:00:00.001ZZ" "double Zulu code w/ millis",
    testInvalidDatetime "2024-01-01T00:00:00➕0000" "sign `+` is an emoji",
    testInvalidDatetime "2024-01-01T00:00:00➖0000" "sign `-` is an emoji",
    testInvalidDatetime "2024-01-01T00:00:00.0001Z" "fraction of seconds is 4 digits",
    testInvalidDatetime "2024-01-01T00:00:00.001➖0000" "sign `+` is an emoji",
    testInvalidDatetime "2024-01-01T00:00:00.001➕0000" "sign `-` is an emoji",
    testInvalidDatetime "2024-01-01T00:00:00.001+00000" "timezone offset is 5 digits",
    testInvalidDatetime "2024-01-01T00:00:00.001-00000" "timezone offset is 5 digits",
    -- testInvalidDatetime "2016-12-31T00:00:00+1160" "timezone offset is ???", -- TODO: LEAN-RUST DIFF
    -- testInvalidDatetime "2016-12-31T00:00:00+1199" "timezone offset is ???", -- TODO: LEAN-RUST DIFF
  ]

theorem testDuration1 : toString ((Duration.parse "1ms").get!) = "1" := by native_decide
theorem testDuration2 : toString ((Duration.parse "1s").get!) = "1000" := by native_decide
theorem testDuration3 : toString ((Duration.parse "1m").get!) = "60000" := by native_decide
theorem testDuration4 : toString ((Duration.parse "1h").get!) = "360000" := by native_decide
theorem testDuration5 : toString ((Duration.parse "1d").get!) = "86400000" := by native_decide
theorem testDuration6 : toString ((Duration.parse "1d2h3m4s5ms").get!) = "87304005" := by native_decide
theorem testDuration7 : toString ((Duration.parse "2d12h").get!) = "177120000" := by native_decide
theorem testDuration8 : toString ((Duration.parse "3m30s").get!) = "210000" := by native_decide
theorem testDuration9 : toString ((Duration.parse "1h30m45s").get!) = "2205000" := by native_decide
theorem testDuration10 : toString ((Duration.parse "2d5h20m").get!) = "175800000" := by native_decide
theorem testDuration11 : toString ((Duration.parse "-1d12h").get!) = "-90720000" := by native_decide
theorem testDuration12 : toString ((Duration.parse "-3h45m").get!) = "-3780000" := by native_decide
theorem testDuration13 : toString ((Duration.parse "1d1ms").get!) = "86400001" := by native_decide
theorem testDuration14 : toString ((Duration.parse "59m59s999ms").get!) = "3599999" := by native_decide
theorem testDuration15 : toString ((Duration.parse "23h59m59s999ms").get!) = "11879999" := by native_decide
theorem testDuration16 : toString ((Duration.parse "0d0h0m0s0ms").get!) = "0" := by native_decide

private def testValidDuration (str : String) (rep : Int) : TestCase IO :=
  test str ⟨λ _ => checkEq (Duration.parse str) (duration? rep)⟩

def testsForValidDurationStrings :=
  suite "Duration.parse for valid strings"
  [
    testValidDuration "0ms" 0,
    testValidDuration "0d0s" 0,
    testValidDuration "1ms" 1,
    testValidDuration "1s" 1000,
    testValidDuration "1m" 60000,
    testValidDuration "1h" 360000,
    testValidDuration "1d" 86400000,
    testValidDuration "12s340ms" 12340,
    testValidDuration "1s234ms" 1234,
    testValidDuration "-1s" (-1000),
    testValidDuration "-4s200ms" (-4200),
    testValidDuration "-9s876ms" (-9876),
    testValidDuration "106751d23h47m16s854ms" 9223297516854,
    testValidDuration "-106751d23h47m16s854ms" (-9223297516854),
    testValidDuration "1d2h3m4s5ms" 87304005,
    testValidDuration "2d12h" 177120000,
    testValidDuration "3m30s" 210000,
    testValidDuration "1h30m45s" 2205000,
    testValidDuration "2d5h20m" 175800000,
    testValidDuration "-1d12h" (-90720000),
    testValidDuration "-3h45m" (-3780000),
    testValidDuration "1d1ms" 86400001,
    testValidDuration "59m59s999ms" 3599999,
    testValidDuration "23h59m59s999ms" 11879999
  ]

private def testInvalidDuration (str : String) (msg : String) : TestCase IO :=
  test s!"{str} [{msg}]" ⟨λ _ => checkEq (Duration.parse str) .none⟩

def testsForInvalidDurationStrings :=
  suite "Duration.parse for invalid strings"
  [
    testInvalidDuration "" "empty string",
    testInvalidDuration "d" "unit but no amount",
    testInvalidDuration "1d-1s" "invalid use of -",
    testInvalidDuration "1d2h3m4s5ms6" "trailing amount",
    testInvalidDuration "1x2m3s" "invalid unit",
    testInvalidDuration "1.23s" "amounts must be integral",
    testInvalidDuration "1s1d" "invalid order",
    testInvalidDuration "1s1s" "repeated units",
    testInvalidDuration "1d2h3m4s5ms " "trailing space",
    testInvalidDuration " 1d2h3m4s5ms" "leading space",
    testInvalidDuration "1d9223372036854775807ms" "overflow",
    testInvalidDuration "1d92233720368547758071ms" "overflow ms",
    testInvalidDuration "9223372036854776s1ms" "overflow s"
  ]

def tests := [testsForValidDatetimeStrings, testsForInvalidDatetimeStrings,
              testsForValidDurationStrings, testsForInvalidDurationStrings]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.Datetime
