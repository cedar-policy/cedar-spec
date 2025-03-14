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

private def testValidDatetime (str : String) (rep : Int) : TestCase IO :=
  test str ⟨λ _ => checkEq (parse str) (datetime? rep)⟩

def testsForValidDatetimeStrings :=
  suite "Datetime.parse for valid strings"
  [
    testValidDatetime "2022-10-10" 1665360000000,
    testValidDatetime "1969-12-31" (-86400000 : Int),
    testValidDatetime "1969-12-31T23:59:59Z" (-1000 : Int),
    testValidDatetime "1969-12-31T23:59:59.001Z" (-999 : Int),
    testValidDatetime "1969-12-31T23:59:59.999Z" (-1 : Int),
    testValidDatetime "2024-10-15" 1728950400000,
    testValidDatetime "2024-10-15T11:38:02Z" 1728992282000,
    testValidDatetime "2024-10-15T11:38:02.101Z" 1728992282101,
    testValidDatetime "2024-10-15T11:38:02.101-1134" 1729033922101,
    testValidDatetime "2024-10-15T11:38:02.101+1134" 1728950642101,
    testValidDatetime "2024-10-15T11:38:02+1134" 1728950642000,
    testValidDatetime "2024-10-15T11:38:02-1134" 1729033922000,
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
    testInvalidDatetime " 2022-10-10" "leading space",
    testInvalidDatetime "2022-10-10 " "trailing space",
    testInvalidDatetime "2022-10- 10" "interior space",
    testInvalidDatetime "11-12-13" "two digits for year",
    testInvalidDatetime "011-12-13" "three digits for year",
    testInvalidDatetime "00011-12-13" "five digits for year",
    testInvalidDatetime "0001-2-13" "one digit for month",
    testInvalidDatetime "0001-012-13" "three digits for month",
    testInvalidDatetime "0001-02-3" "one digit for day",
    testInvalidDatetime "0001-02-003" "three digits for day",
    testInvalidDatetime "0001-01-01T1:01:01Z" "one digit for hour",
    testInvalidDatetime "0001-01-01T001:01:01Z" "three digits for hour",
    testInvalidDatetime "0001-01-01T01:1:01Z" "one digit for minutes",
    testInvalidDatetime "0001-01-01T01:001:01Z" "three digits for minutes",
    testInvalidDatetime "0001-01-01T01:01:1Z" "one digit for seconds",
    testInvalidDatetime "0001-01-01T01:01:001Z" "three digits for seconds",
    testInvalidDatetime "0001-01-01T01:01:01.01Z" "two digits for ms",
    testInvalidDatetime "0001-01-01T01:01:01.0001Z" "four digits for ms",
    testInvalidDatetime "0001-01-01T01:01:01.001+01" "two digits for offset",
    testInvalidDatetime "0001-01-01T01:01:01.001+001" "three digits for offset",
    testInvalidDatetime "0001-01-01T01:01:01.001+00001" "six digits for offset",
    testInvalidDatetime "0001-01-01T01:01:01.001+00:01" "offset with colon",
    testInvalidDatetime "0001-01-01T01:01:01.001+00:00:01" "six offset with colon",
    testInvalidDatetime "-0001-01-01" "negative year",
    testInvalidDatetime "1111-1x-20" "invalid month",
    testInvalidDatetime "1111-Jul-20" "abbreviated month",
    testInvalidDatetime "1111-July-20" "full month",
    testInvalidDatetime "1111-J-20" "single letter month",
    testInvalidDatetime "2024-10-15Z" "Zulu code invalid for date",
    testInvalidDatetime "2024-10-15T11:38:02ZZ" "double Zulu code",
    testInvalidDatetime "2024-01-01T" "separator not needed",
    testInvalidDatetime "2024-01-01Ta" "unexpected character 'a'",
    testInvalidDatetime "2024-01-01T01:" "only hours",
    testInvalidDatetime "2024-01-01T01:02" "no seconds",
    testInvalidDatetime "2024-01-01T01:02:0b" "unexpected character 'b'",
    testInvalidDatetime "2024-01-01T01::02:03" "double colon",
    testInvalidDatetime "2024-01-01T01::02::03" "double colons",
    testInvalidDatetime "2024-01-01T31:02:03Z" "invalid hour range",
    testInvalidDatetime "2024-01-01T01:60:03Z" "invalid minute range",
    testInvalidDatetime "2016-12-31T23:59:60Z" "leap second",
    testInvalidDatetime "2016-12-31T23:59:61Z" "invalid second range",
    testInvalidDatetime "2024-01-01T00:00:00" "timezone not specified",
    testInvalidDatetime "2024-01-01T00:00:00T" "separator is not timezone",
    testInvalidDatetime "2024-01-01T00:00:00ZZ" "double Zulu code",
    testInvalidDatetime "2024-01-01T00:00:00x001Z" "typo in milliseconds separator",
    testInvalidDatetime "2024-01-01T00:00:00.001ZZ" "double Zulu code w/ millis",
    testInvalidDatetime "2016-12-31T23:59:60.000Z" "leap second (millis/UTC)",
    testInvalidDatetime "2016-12-31T23:59:60.000+0200" "leap second (millis/offset)",
    testInvalidDatetime "2024-01-01T00:00:00➕0000" "sign `+` is an emoji",
    testInvalidDatetime "2024-01-01T00:00:00➖0000" "sign `-` is an emoji",
    testInvalidDatetime "2024-01-01T00:00:00.0001Z" "fraction of seconds is 4 digits",
    testInvalidDatetime "2024-01-01T00:00:00.001➖0000" "sign `+` is an emoji",
    testInvalidDatetime "2024-01-01T00:00:00.001➕0000" "sign `-` is an emoji",
    testInvalidDatetime "2024-01-01T00:00:00.001+00000" "offset is 5 digits",
    testInvalidDatetime "2024-01-01T00:00:00.001-00000" "offset is 5 digits",
    testInvalidDatetime "2016-01-01T00:00:00+2400" "invalid offset hour range",
    testInvalidDatetime "2016-01-01T00:00:00+0060" "invalid offset minute range",
    testInvalidDatetime "2016-01-01T00:00:00+9999" "invalid offset hour and minute range",
  ]

-- Note: The instances below are only used for tests.
-- We might redefine them if they are need for something else.
instance : OfNat Duration n where
  ofNat := ⟨Int64.ofNat n⟩

instance : ToString Duration where
  toString d := toString d.val

instance : Neg Duration where
  neg d := ⟨-d.val⟩

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
    testValidDuration "1h" 3600000,
    testValidDuration "1d" 86400000,
    testValidDuration "12s340ms" 12340,
    testValidDuration "1s234ms" 1234,
    testValidDuration "-1ms" (-1),
    testValidDuration "-1s" (-1000),
    testValidDuration "-4s200ms" (-4200),
    testValidDuration "-9s876ms" (-9876),
    testValidDuration "106751d23h47m16s854ms" 9223372036854,
    testValidDuration "-106751d23h47m16s854ms" (-9223372036854),
    testValidDuration "-9223372036854775808ms" (-9223372036854775808), -- min Int64 value
    testValidDuration "9223372036854775807ms" (9223372036854775807),   -- max Int64 value
    testValidDuration "1d2h3m4s5ms" 93784005,
    testValidDuration "2d12h" 216000000,
    testValidDuration "3m30s" 210000,
    testValidDuration "1h30m45s" 5445000,
    testValidDuration "2d5h20m" 192000000,
    testValidDuration "-1d12h" (-129600000),
    testValidDuration "-3h45m" (-13500000),
    testValidDuration "1d1ms" 86400001,
    testValidDuration "59m59s999ms" 3599999,
    testValidDuration "23h59m59s999ms" 86399999,
    testValidDuration "0d0h0m0s0ms" 0
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
    testInvalidDuration "9223372036854776s1ms" "overflow s",
    testInvalidDuration "-12142442932071h" "overflow hours"
  ]

private def testOffset (date₁ date₂ : String) (dur : Duration) : TestCase IO :=
  test s!"{date₁} + {dur} -> {date₂}" ⟨λ _ => checkEq (offset (parse date₁).get! dur) (parse date₂)⟩

def testsForOffset :=
  suite "offset tests"
  [
    testOffset "2024-10-15" "2024-10-15" 0,
    testOffset "2024-10-15" "2024-10-15T00:00:00.001Z" 1,
    testOffset "2024-10-15" "2024-10-15T00:00:01Z" 1000,
    testOffset "2024-10-15" "2024-10-14T23:59:59Z" (-1000 : Duration),
    testOffset "2024-10-15" "2024-10-15T00:00:00-0001" 60000,
  ]

private def testDurationSince (date₁ date₂ : String) (dur : Duration) : TestCase IO :=
  test s!"durationSince {date₁} {date₂} = {dur}" ⟨λ _ => checkEq (durationSince (parse date₁).get! (parse date₂).get!) dur⟩

def testsForDurationSince :=
  suite "durationSince tests"
  [
    testDurationSince "2024-10-15" "2024-10-15" 0,
    testDurationSince "2024-10-15T00:00:00.001Z" "2024-10-15" 1,
    testDurationSince "2024-10-15T00:00:01Z" "2024-10-15" 1000,
    testDurationSince "2024-10-14T23:59:59Z" "2024-10-15" (-1000 : Duration),
    testDurationSince "2024-10-15T00:00:00-0001" "2024-10-15" 60000,
  ]

private def testToDate (date₁ date₂ : String) : TestCase IO :=
  test s!"toDate {date₁} = {date₂}" ⟨λ _ => checkEq (toDate (parse date₁).get!) (parse date₂).get!⟩

def testsForToDate :=
  suite "toDate tests"
  [
    testToDate "2024-10-15" "2024-10-15",
    testToDate "2024-10-15T00:00:01Z" "2024-10-15",
    testToDate "2024-10-15T23:59:59Z" "2024-10-15",
    testToDate "2024-10-15T23:59:00-0001" "2024-10-16",
    testToDate "1969-12-31" "1969-12-31",
    testToDate "1969-12-31T23:59:59Z" "1969-12-31",
  ]

private def testToTime (date₁ : String) (dur : Duration) : TestCase IO :=
  test s!"toTime {date₁} = {dur}" ⟨λ _ => checkEq (toTime (parse date₁).get!) dur⟩

def testsForToTime :=
  suite "toTime tests"
  [
    testToTime "2024-10-15" 0,
    testToTime "2024-10-15T00:00:00.001Z" 1,
    testToTime "2024-10-15T00:00:01Z" 1000,
    testToTime "2024-10-15T23:59:59Z" 86399000,
    testToTime "2024-10-15T23:59:00-0001" 0,
    testToTime "1969-12-31" 0,
    testToTime "1969-12-31T23:59:59Z" 86399000,
    testToTime "1969-12-31T12:00:00Z" 43200000
  ]

private def testToMilliseconds (str : String) (dur : Int64) : TestCase IO :=
  test s!"toMilliseconds {str} = {dur}" ⟨λ _ => checkEq (Duration.toMilliseconds (Duration.parse str).get!) dur⟩

def testsForToMilliseconds :=
  suite "toMilliseconds tests"
  [
    testToMilliseconds "0ms" 0,
    testToMilliseconds "1ms" 1,
    testToMilliseconds "1000ms" 1000,
    testToMilliseconds "-0ms" 0,
    testToMilliseconds "-1ms" (-1 : Int64),
    testToMilliseconds "1s" 1000,
    testToMilliseconds "1m" 60000,
    testToMilliseconds "1h" 3600000,
    testToMilliseconds "1d" 86400000,
    testToMilliseconds "-9223372036854775808ms" (-9223372036854775808 : Int64),
    testToMilliseconds "9223372036854775807ms" 9223372036854775807,
  ]

private def testToSeconds (str : String) (dur : Int64) : TestCase IO :=
  test s!"toSeconds {str} = {dur}" ⟨λ _ => checkEq (Duration.toSeconds (Duration.parse str).get!) dur⟩

def testsForToSeconds :=
  suite "toSeconds tests"
  [
    testToSeconds "0ms" 0,
    testToSeconds "999ms" 0,
    testToSeconds "1000ms" 1,
    testToSeconds "1001ms" 1,
    testToSeconds "-0ms" 0,
    testToSeconds "-999ms" (0 : Int64),
    testToSeconds "-1000ms" (-1 : Int64),
    testToSeconds "1s" 1,
    testToSeconds "1m" 60,
    testToSeconds "1h" 3600,
    testToSeconds "1d" 86400,
  ]

private def testToMinutes (str : String) (dur : Int64) : TestCase IO :=
  test s!"toMinutes {str} = {dur}" ⟨λ _ => checkEq (Duration.toMinutes (Duration.parse str).get!) dur⟩

def testsForToMinutes :=
  suite "toMinutes tests"
  [
    testToMinutes "0ms" 0,
    testToMinutes "59999ms" 0,
    testToMinutes "60000ms" 1,
    testToMinutes "59s" 0,
    testToMinutes "60s" 1,
    testToMinutes "61s" 1,
    testToMinutes "-59999ms" 0,
    testToMinutes "-60000ms" (-1 : Int64),
    testToMinutes "1m" 1,
    testToMinutes "1h" 60,
    testToMinutes "1d" 1440,
  ]

private def testToHours (str : String) (dur : Int64) : TestCase IO :=
  test s!"toHours {str} = {dur}" ⟨λ _ => checkEq (Duration.toHours (Duration.parse str).get!) dur⟩

def testsForToHours :=
  suite "toHours tests"
  [
    testToHours "0ms" 0,
    testToHours "3599999ms" 0,
    testToHours "3600000ms" 1,
    testToHours "59m" 0,
    testToHours "60m" 1,
    testToHours "61m" 1,
    testToHours "-3599999ms" 0,
    testToHours "-3600000ms" (-1 : Int64),
    testToHours "1h" 1,
    testToHours "1d" 24,
  ]

private def testToDays (str : String) (dur : Int64) : TestCase IO :=
  test s!"toDays {str} = {dur}" ⟨λ _ => checkEq (Duration.toDays (Duration.parse str).get!) dur⟩

def testsForToDays :=
  suite "toDays tests"
  [
    testToDays "0ms" 0,
    testToDays "86399999ms" 0,
    testToDays "86400000ms" 1,
    testToDays "23h" 0,
    testToDays "24h" 1,
    testToDays "25h" 1,
    testToDays "-86399999ms" 0,
    testToDays "-86400000ms" (-1 : Int64),
    testToDays "1d" 1,
  ]

def tests := [testsForValidDatetimeStrings, testsForInvalidDatetimeStrings,
              testsForValidDurationStrings, testsForInvalidDurationStrings,
              testsForOffset, testsForDurationSince, testsForToDate, testsForToTime,
              testsForToMilliseconds, testsForToSeconds, testsForToMinutes, testsForToHours, testsForToDays]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.Datetime
