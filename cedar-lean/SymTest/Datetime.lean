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

namespace SymTest.Datetime

open Cedar Data Spec SymCC Validation
open UnitTest

namespace Duration

private def durationContext : RecordType :=
  Map.make [
    ("x", .required (.ext .duration)),
    ("y", .required (.ext .duration)),
    ("z", .required (.ext .duration)),
    ("s", .required .string)
  ]

private def durationTypeEnv := BasicTypes.env Map.empty Map.empty durationContext
private def durationSymEnv  := SymEnv.ofEnv durationTypeEnv

private def x : Expr := .getAttr (.var .context) "x"
private def y : Expr := .getAttr (.var .context) "y"
private def z : Expr := .getAttr (.var .context) "z"
private def s : Expr := .getAttr (.var .context) "s"

def durLit (str : String) : Expr :=
  .call .duration [.lit (.string str)]

private def testValidConstructor (str : String) (rep : Int) : TestCase SolverM :=
  testReduce str
    (durLit str)
    durationSymEnv
    (.ok (.some (.prim (.ext (.duration (Ext.Datetime.duration? rep).get!)))))

private def testInvalidConstructor (str : String) (msg : String) : TestCase SolverM :=
  testReduce s!"{str} [{msg}]"
    (durLit str)
    durationSymEnv
    (.error .typeError)

private def testValidConversion (test_name : String) (expr : Expr) (res : Int64) : TestCase SolverM :=
  testVerifyEquivalent test_name
    (.binaryApp .eq expr (.lit (.int res)))
    (.lit (.bool true))
    durationSymEnv .unsat

def testsForDurationConstructor :=
  suite "Duration.duration"
  [
    testValidConstructor "0ms" 0,
    testValidConstructor "0d0s" 0,
    testValidConstructor "1ms" 1,
    testValidConstructor "1s" 1000,
    testValidConstructor "1m" 60000,
    testValidConstructor "1h" 3600000,
    testValidConstructor "1d" 86400000,
    testValidConstructor "12s340ms" 12340,
    testValidConstructor "1s234ms" 1234,
    testValidConstructor "-1ms" (-1),
    testValidConstructor "-1s" (-1000),
    testValidConstructor "-4s200ms" (-4200),
    testValidConstructor "-9s876ms" (-9876),
    testValidConstructor "106751d23h47m16s854ms" 9223372036854,
    testValidConstructor "-106751d23h47m16s854ms" (-9223372036854),
    testValidConstructor "-9223372036854775808ms" (-9223372036854775808), -- min Int64 value
    testValidConstructor "9223372036854775807ms" (9223372036854775807),   -- max Int64 value
    testValidConstructor "1d2h3m4s5ms" 93784005,
    testValidConstructor "2d12h" 216000000,
    testValidConstructor "3m30s" 210000,
    testValidConstructor "1h30m45s" 5445000,
    testValidConstructor "2d5h20m" 192000000,
    testValidConstructor "-1d12h" (-129600000),
    testValidConstructor "-3h45m" (-13500000),
    testValidConstructor "1d1ms" 86400001,
    testValidConstructor "59m59s999ms" 3599999,
    testValidConstructor "23h59m59s999ms" 86399999,
    testValidConstructor "0d0h0m0s0ms" 0,
    testInvalidConstructor "" "empty string",
    testInvalidConstructor "d" "unit but no amount",
    testInvalidConstructor "1d-1s" "invalid use of -",
    testInvalidConstructor "1d2h3m4s5ms6" "trailing amount",
    testInvalidConstructor "1x2m3s" "invalid unit",
    testInvalidConstructor "1.23s" "amounts must be integral",
    testInvalidConstructor "1s1d" "invalid order",
    testInvalidConstructor "1s1s" "repeated units",
    testInvalidConstructor "1d2h3m4s5ms " "trailing space",
    testInvalidConstructor " 1d2h3m4s5ms" "leading space",
    testInvalidConstructor "1d9223372036854775807ms" "overflow",
    testInvalidConstructor "1d92233720368547758071ms" "overflow ms",
    testInvalidConstructor "9223372036854776s1ms" "overflow s"
  ]

def testsForDurationComparisonOperations :=
  suite "Duration.comparisons"
  [
    testVerifyEquivalent "True: x <= 9223372036854775807ms"
      (.binaryApp .lessEq x (durLit "9223372036854775807ms"))
      (.lit (.bool true))
      durationSymEnv .unsat,

    testVerifyEquivalent "True: !(9223372036854775807ms < x)"
      (.unaryApp .not (.binaryApp .less (durLit "9223372036854775807ms") x))
      (.lit (.bool true))
      durationSymEnv .unsat,

    testVerifyEquivalent "True: -9223372036854775808ms <= x"
      (.binaryApp .lessEq (durLit "-9223372036854775808ms") x)
      (.lit (.bool true))
      durationSymEnv .unsat,

    testVerifyEquivalent "True: !(x < -9223372036854775808ms)"
      (.unaryApp .not (.binaryApp .less x (durLit "-9223372036854775808ms")))
      (.lit (.bool true))
      durationSymEnv .unsat,

    testVerifyEquivalent "True: x <= x"
      (.binaryApp .lessEq x x)
      (.lit (.bool true))
      durationSymEnv .unsat,

    testVerifyEquivalent "True: x <= y ∨ y <= x"
      (.or (.binaryApp .lessEq x y) (.binaryApp .lessEq y x))
      (.lit (.bool true))
      durationSymEnv .unsat,

    testVerifyEquivalent "False: x < x"
      (.binaryApp .less x x)
      (.lit (.bool false))
      durationSymEnv .unsat,

    testVerifyEquivalent "False: x < y ∧ y < x"
      (.and (.binaryApp .less x y) (.binaryApp .less y x))
      (.lit (.bool false))
      durationSymEnv .unsat,

    testVerifyEquivalent "Implies: !(x = y) ===> x < y ∨ y < x"
      (.unaryApp .not (.binaryApp .eq x y))
      (.or (.binaryApp .less x y) (.binaryApp .less y x))
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x != 9223372036854775807ms ===> x < 9223372036854775807ms"
      (.unaryApp .not (.binaryApp .eq x (durLit "9223372036854775807ms")))
      (.binaryApp .less x (durLit "9223372036854775807ms"))
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x != -9223372036854775808ms ===> -9223372036854775808ms < x"
      (.unaryApp .not (.binaryApp .eq x (durLit "-9223372036854775808ms")))
      (.binaryApp .less (durLit "-9223372036854775808ms") x)
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x < y ===> !(y <= x)"
      (.binaryApp .less x y)
      (.unaryApp .not (.binaryApp .lessEq y x))
      durationSymEnv .unsat,

    testVerifyImplies "Implies: !(y <= x) ===> x < y"
      (.unaryApp .not (.binaryApp .lessEq y x))
      (.binaryApp .less x y)
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x <= y ===> !(y < x)"
      (.binaryApp .lessEq x y)
      (.unaryApp .not (.binaryApp .less y x))
      durationSymEnv .unsat,

    testVerifyImplies "Implies: !(y < x) ===> x <= y"
      (.unaryApp .not (.binaryApp .less y x))
      (.binaryApp .lessEq x y)
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x < y ===> x <= y"
      (.binaryApp .less x y)
      (.binaryApp .lessEq x y)
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x = y ===> x <= y"
      (.binaryApp .eq x y)
      (.binaryApp .lessEq x y)
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x <= y ===> x = y ∨ x < y"
      (.binaryApp .lessEq x y)
      (.or (.binaryApp .eq x y) (.binaryApp .less x y))
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x <= y ∧ !(x = y) ===> x < y"
      (.and (.binaryApp .lessEq x y) (.unaryApp .not (.binaryApp .eq x y)))
      (.binaryApp .less x y)
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x < y ===> !(x = y)"
      (.binaryApp .less x y)
      (.unaryApp .not (.binaryApp .eq x y))
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x <= y ∧ y <= x ===> y = x"
      (.and (.binaryApp .lessEq x y) (.binaryApp .lessEq y x))
      (.binaryApp .eq x y)
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x <= y ∧ y <= z ===> x <= z"
      (.and (.binaryApp .lessEq x y) (.binaryApp .lessEq y z))
      (.binaryApp .lessEq x z)
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x < y ∧ y < z ===> x < z"
      (.and (.binaryApp .less x y) (.binaryApp .less y z))
      (.binaryApp .lessEq x z)
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x < y ∧ y <= z ===> x < z"
      (.and (.binaryApp .less x y) (.binaryApp .lessEq y z))
      (.binaryApp .lessEq x z)
      durationSymEnv .unsat,

    testVerifyImplies "Implies: x <= y ∧ y < z ===> x < z"
      (.and (.binaryApp .lessEq x y) (.binaryApp .less y z))
      (.binaryApp .lessEq x z)
      durationSymEnv .unsat,
  ]

def testsForDurationConversions :=
  suite "Duration.conversions"
  [
    testValidConversion "Testcase: Duration(0ms).toMilliseconds == 0"
      (.call .toMilliseconds [(durLit "0ms")])
      0,
    testValidConversion "Testcase: Duration(999ms).toSeconds == 0"
      (.call .toSeconds [(durLit "999ms")])
      0,
    testValidConversion "Testcase: Duration(59s999ms).toMinutes == 0"
      (.call .toMinutes [(durLit "59s999ms")])
      0,
    testValidConversion "Testcase: Duration(59m59s999ms).toHours == 0"
      (.call .toHours [(durLit "59m59s999ms")])
      0,
    testValidConversion "Testcase: Duration(23h59m59s999ms).toDays == 0"
      (.call .toDays [(durLit "23h59m59s999ms")])
      0,

    testValidConversion "Testcase: Duration(-999ms).toSeconds == 0"
      (.call .toSeconds [(durLit "-999ms")])
      0,
    testValidConversion "Testcase: Duration(-59s999ms).toMinutes == 0"
      (.call .toMinutes [(durLit "-59s999ms")])
      0,
    testValidConversion "Testcase: Duration(-59m59s999ms).toHours == 0"
      (.call .toHours [(durLit "-59m59s999ms")])
      0,
    testValidConversion "Testcase: Duration(-23h59m59s999ms).toDays == 0"
      (.call .toDays [(durLit "-23h59m59s999ms")])
      0,

    testValidConversion "Testcase: Duration(1ms).toMilliseconds == 1"
      (.call .toMilliseconds [(durLit "1ms")])
      1,
    testValidConversion "Testcase: Duration(1000ms).toSeconds == 1"
      (.call .toSeconds [(durLit "1000ms")])
      1,
    testValidConversion "Testcase: Duration(60s).toMinutes == 1"
      (.call .toMinutes [(durLit "60s")])
      1,
    testValidConversion "Testcase: Duration(60m).toHours == 1"
      (.call .toHours [(durLit "60m")])
      1,
    testValidConversion "Testcase: Duration(24h).toDays == 1"
      (.call .toDays [(durLit "24h")])
      1,

    testValidConversion "Testcase: Duration(-1ms).toMilliseconds == -1"
      (.call .toMilliseconds [(durLit "-1ms")])
      (-1),
    testValidConversion "Testcase: Duration(-1000ms).toSeconds == -1"
      (.call .toSeconds [(durLit "-1000ms")])
      (-1),
    testValidConversion "Testcase: Duration(-60s).toMinutes == -1"
      (.call .toMinutes [(durLit "-60s")])
      (-1),
    testValidConversion "Testcase: Duration(-60m).toHours == -1"
      (.call .toHours [(durLit "-60m")])
      (-1),
    testValidConversion "Testcase: Duration(-24h).toDays == -1"
      (.call .toDays [(durLit "-24h")])
      (-1),

    testValidConversion "Testcase: Duration(12d2h19m50s321ms).toDays == 12"
      (.call .toDays [(durLit "12d2h19m50s321ms")])
      12,
    testValidConversion "Testcase: Duration(12d2h19m50s321ms).toHours == 290"
      (.call .toHours [(durLit "12d2h19m50s321ms")])
      290,
    testValidConversion "Testcase: Duration(12d2h19m50s321ms).toMinutes == 17419"
      (.call .toMinutes [(durLit "12d2h19m50s321ms")])
      17419,
    testValidConversion "Testcase: Duration(12d2h19m50s321ms).toSeconds == 1045190"
      (.call .toSeconds [(durLit "12d2h19m50s321ms")])
      1045190,
    testValidConversion "Testcase: Duration(12d2h19m50s321ms).toMilliseconds == 1045190321"
      (.call .toMilliseconds [(durLit "12d2h19m50s321ms")])
      1045190321,

    testValidConversion "Testcase: Duration(-12d2h19m50s321ms).toDays == -12"
      (.call .toDays [(durLit "-12d2h19m50s321ms")])
      (-12),
    testValidConversion "Testcase: Duration(-12d2h19m50s321ms).toHours == -290"
      (.call .toHours [(durLit "-12d2h19m50s321ms")])
      (-290),
    testValidConversion "Testcase: Duration(-12d2h19m50s321ms).toMinutes == -17419"
      (.call .toMinutes [(durLit "-12d2h19m50s321ms")])
      (-17419),
    testValidConversion "Testcase: Duration(-12d2h19m50s321ms).toSeconds == -1045190"
      (.call .toSeconds [(durLit "-12d2h19m50s321ms")])
      (-1045190),
    testValidConversion "Testcase: Duration(-12d2h19m50s321ms).toMilliseconds == -1045190321"
      (.call .toMilliseconds [(durLit "-12d2h19m50s321ms")])
      (-1045190321),

    -- Check that this formula is true for all possible values of x
    -- testVerifyImplies "Implies: 0ms <= x ===> x.toMilliseconds - 1000 * x.toSeconds < 1000"
    --   (.binaryApp .lessEq (durLit "0ms") x)
    --   (.binaryApp .less (.binaryApp .sub (.call .toMilliseconds [x])
    --                                      (.binaryApp .mul (.lit (.int 1000)) (.call .toSeconds [x])))
    --                     (.lit (.int 1000)))
    --   durationSymEnv .unsat,

    -- Test that some model of x satisfies the formula. Note that this is not always true
    -- (e.g., this formula is only true when x is a multiple of 1000ms)
    -- We test this way because checking formulas (similar to the above) is slow
    testVerifyEquivalent "SAT: x.toMilliseconds = 1000 * x.toSeconds"
      (.binaryApp .eq (.call .toMilliseconds [x]) (.binaryApp .mul (.lit (.int 1000)) (.call .toSeconds [x])))
      (.lit (.bool true))
      durationSymEnv .sat,

    testVerifyEquivalent "SAT: x.toSeconds = 60 * x.toMinutes"
      (.binaryApp .eq (.call .toSeconds [x]) (.binaryApp .mul (.lit (.int 60)) (.call .toMinutes [x])))
      (.lit (.bool true))
      durationSymEnv .sat,

    testVerifyEquivalent "SAT: x.toMinutes = 60 * x.toHours"
      (.binaryApp .eq (.call .toMinutes [x]) (.binaryApp .mul (.lit (.int 60)) (.call .toHours [x])))
      (.lit (.bool true))
      durationSymEnv .sat,

    testVerifyEquivalent "SAT: x.toHours = 24 * x.toDays"
      (.binaryApp .eq (.call .toHours [x]) (.binaryApp .mul (.lit (.int 24)) (.call .toDays [x])))
      (.lit (.bool true))
      durationSymEnv .sat
  ]

end Duration

private def datetimeContext : RecordType :=
  Map.make [
    ("dt1", .required (.ext .datetime)),
    ("dt2", .required (.ext .datetime)),
    ("dt3", .required (.ext .datetime)),
    ("dur1", .required (.ext .duration)),
    ("dur2", .required (.ext .duration)),
    ("s", .required .string)
  ]

private def datetimeTypeEnv := BasicTypes.env Map.empty Map.empty datetimeContext
private def datetimeSymEnv  := SymEnv.ofEnv datetimeTypeEnv

private def dt1 : Expr := .getAttr (.var .context) "dt1"
private def dt2 : Expr := .getAttr (.var .context) "dt2"
private def dt3 : Expr := .getAttr (.var .context) "dt3"
 def dur1 : Expr := .getAttr (.var .context) "dur1"
private def dur2 : Expr := .getAttr (.var .context) "dur2"
private def s : Expr := .getAttr (.var .context) "s"

def dtLit (str : String) : Expr :=
  .call .datetime [.lit (.string str)]

private def testValidConstructor (str : String) (rep : Int) : TestCase SolverM :=
  testReduce str
    (dtLit str)
    datetimeSymEnv
    (.ok (.some (.prim (.ext (.datetime (Ext.Datetime.datetime? rep).get!)))))

private def testInvalidConstructor (str : String) (msg : String) : TestCase SolverM :=
  testReduce s!"{str} [{msg}]"
    (dtLit str)
    datetimeSymEnv
    (.error .typeError)

def testsForDatetimeConstructor :=
  suite "Datetime.datetime"
  [
    testValidConstructor "2022-10-10" 1665360000000,
    testValidConstructor "1969-12-31" (-86400000 : Int),
    testValidConstructor "1969-12-31T23:59:59Z" (-1000 : Int),
    testValidConstructor "1969-12-31T23:59:59.001Z" (-999 : Int),
    testValidConstructor "1969-12-31T23:59:59.999Z" (-1 : Int),
    testValidConstructor "2024-10-15" 1728950400000,
    testValidConstructor "2024-10-15T11:38:02Z" 1728992282000,
    testValidConstructor "2024-10-15T11:38:02.101Z" 1728992282101,
    testValidConstructor "2024-10-15T11:38:02.101-1134" 1729033922101,
    testValidConstructor "2024-10-15T11:38:02.101+1134" 1728950642101,
    testValidConstructor "2024-10-15T11:38:02+1134" 1728950642000,
    testValidConstructor "2024-10-15T11:38:02-1134" 1729033922000,
    testInvalidConstructor "" "empty string",
    testInvalidConstructor "a" "string is letter",
    testInvalidConstructor "-" "string is character",
    testInvalidConstructor "-1" "string is integer",
    testInvalidConstructor " 2022-10-10" "leading space",
    testInvalidConstructor "2022-10-10 " "trailing space",
    testInvalidConstructor "2022-10- 10" "interior space",
    testInvalidConstructor "11-12-13" "two digits for year",
    testInvalidConstructor "011-12-13" "three digits for year",
    testInvalidConstructor "00011-12-13" "five digits for year",
    testInvalidConstructor "0001-2-13" "one digit for month",
    testInvalidConstructor "0001-012-13" "three digits for month",
    testInvalidConstructor "0001-02-3" "one digit for day",
    testInvalidConstructor "0001-02-003" "three digits for day",
    testInvalidConstructor "0001-01-01T1:01:01Z" "one digit for hour",
    testInvalidConstructor "0001-01-01T001:01:01Z" "three digits for hour",
    testInvalidConstructor "0001-01-01T01:1:01Z" "one digit for minutes",
    testInvalidConstructor "0001-01-01T01:001:01Z" "three digits for minutes",
    testInvalidConstructor "0001-01-01T01:01:1Z" "one digit for seconds",
    testInvalidConstructor "0001-01-01T01:01:001Z" "three digits for seconds",
    testInvalidConstructor "0001-01-01T01:01:01.01Z" "two digits for ms",
    testInvalidConstructor "0001-01-01T01:01:01.0001Z" "four digits for ms",
    testInvalidConstructor "0001-01-01T01:01:01.001+01" "two digits for offset",
    testInvalidConstructor "0001-01-01T01:01:01.001+001" "three digits for offset",
    testInvalidConstructor "0001-01-01T01:01:01.001+00001" "six digits for offset",
    testInvalidConstructor "0001-01-01T01:01:01.001+00:01" "offset with colon",
    testInvalidConstructor "0001-01-01T01:01:01.001+00:00:01" "six offset with colon",
    testInvalidConstructor "-0001-01-01" "negative year",
    testInvalidConstructor "1111-1x-20" "invalid month",
    testInvalidConstructor "1111-Jul-20" "abbreviated month",
    testInvalidConstructor "1111-July-20" "full month",
    testInvalidConstructor "1111-J-20" "single letter month",
    testInvalidConstructor "2024-10-15Z" "Zulu code invalid for date",
    testInvalidConstructor "2024-10-15T11:38:02ZZ" "double Zulu code",
    testInvalidConstructor "2024-01-01T" "separator not needed",
    testInvalidConstructor "2024-01-01Ta" "unexpected character 'a'",
    testInvalidConstructor "2024-01-01T01:" "only hours",
    testInvalidConstructor "2024-01-01T01:02" "no seconds",
    testInvalidConstructor "2024-01-01T01:02:0b" "unexpected character 'b'",
    testInvalidConstructor "2024-01-01T01::02:03" "double colon",
    testInvalidConstructor "2024-01-01T01::02::03" "double colons",
    testInvalidConstructor "2024-01-01T31:02:03Z" "invalid hour range",
    testInvalidConstructor "2024-01-01T01:60:03Z" "invalid minute range",
    testInvalidConstructor "2016-12-31T23:59:60Z" "leap second",
    testInvalidConstructor "2016-12-31T23:59:61Z" "invalid second range",
    testInvalidConstructor "2024-01-01T00:00:00" "timezone not specified",
    testInvalidConstructor "2024-01-01T00:00:00T" "separator is not timezone",
    testInvalidConstructor "2024-01-01T00:00:00ZZ" "double Zulu code",
    testInvalidConstructor "2024-01-01T00:00:00x001Z" "typo in milliseconds separator",
    testInvalidConstructor "2024-01-01T00:00:00.001ZZ" "double Zulu code w/ millis",
    testInvalidConstructor "2016-12-31T23:59:60.000Z" "leap second (millis/UTC)",
    testInvalidConstructor "2016-12-31T23:59:60.000+0200" "leap second (millis/offset)",
    testInvalidConstructor "2024-01-01T00:00:00➕0000" "sign `+` is an emoji",
    testInvalidConstructor "2024-01-01T00:00:00➖0000" "sign `-` is an emoji",
    testInvalidConstructor "2024-01-01T00:00:00.0001Z" "fraction of seconds is 4 digits",
    testInvalidConstructor "2024-01-01T00:00:00.001➖0000" "sign `+` is an emoji",
    testInvalidConstructor "2024-01-01T00:00:00.001➕0000" "sign `-` is an emoji",
    testInvalidConstructor "2024-01-01T00:00:00.001+00000" "offset is 5 digits",
    testInvalidConstructor "2024-01-01T00:00:00.001-00000" "offset is 5 digits",
    testInvalidConstructor "2016-01-01T00:00:00+2400" "invalid offset hour range",
    testInvalidConstructor "2016-01-01T00:00:00+0060" "invalid offset minute range",
    testInvalidConstructor "2016-01-01T00:00:00+9999" "invalid offset hour and minute range",
  ]

private def MIN_DT : Expr := (.call .offset [dtLit "1970-01-01", Duration.durLit "-9223372036854775808ms"])
private def MAX_DT : Expr := (.call .offset [dtLit "1970-01-01", Duration.durLit "9223372036854775807ms"])

def testsForDatetimeComparators :=
  suite "Datetime.comparators"
  [
    testVerifyEquivalent "True: dt1 <= MAX_DT"
      (.binaryApp .lessEq dt1 MAX_DT)
      (.lit (.bool true))
      datetimeSymEnv .unsat,

    testVerifyEquivalent "True: !(MAX_DT < dt1)"
      (.unaryApp .not (.binaryApp .less MAX_DT dt1))
      (.lit (.bool true))
      datetimeSymEnv .unsat,

    testVerifyEquivalent "True: offset MIN_DT <= dt1"
      (.binaryApp .lessEq MIN_DT dt1)
      (.lit (.bool true))
      datetimeSymEnv .unsat,

    testVerifyEquivalent "True: !(dt1 < offset MIN_DT)"
      (.unaryApp .not (.binaryApp .less dt1 MIN_DT))
      (.lit (.bool true))
      datetimeSymEnv .unsat,

    testVerifyEquivalent "True: dt1 <= dt1"
      (.binaryApp .lessEq dt1 dt1)
      (.lit (.bool true))
      datetimeSymEnv .unsat,

    testVerifyEquivalent "True: dt1 <= dt2 ∨ dt2 <= dt1"
      (.or (.binaryApp .lessEq dt1 dt2) (.binaryApp .lessEq dt2 dt1))
      (.lit (.bool true))
      datetimeSymEnv .unsat,

    testVerifyEquivalent "False: dt1 < dt1"
      (.binaryApp .less dt1 dt1)
      (.lit (.bool false))
      datetimeSymEnv .unsat,

    testVerifyEquivalent "False: dt1 < dt2 ∧ dt2 < dt1"
      (.and (.binaryApp .less dt1 dt2) (.binaryApp .less dt2 dt1))
      (.lit (.bool false))
      datetimeSymEnv .unsat,

    testVerifyEquivalent "Implies: !(dt1 = dt2) ===> dt1 < dt2 ∨ dt2 < dt1"
      (.unaryApp .not (.binaryApp .eq dt1 dt2))
      (.or (.binaryApp .less dt1 dt2) (.binaryApp .less dt2 dt1))
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 != MAX_DT ===> dt1 < MAX_DT"
      (.unaryApp .not (.binaryApp .eq dt1 MAX_DT))
      (.binaryApp .less dt1 MAX_DT)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 != MIN_DT ===> MIN_DT < dt1"
      (.unaryApp .not (.binaryApp .eq dt1 MIN_DT))
      (.binaryApp .less MIN_DT dt1)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 < dt2 ===> !(dt2 <= dt1)"
      (.binaryApp .less dt1 dt2)
      (.unaryApp .not (.binaryApp .lessEq dt2 dt1))
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: !(dt2 <= dt1) ===> dt1 < dt2"
      (.unaryApp .not (.binaryApp .lessEq dt2 dt1))
      (.binaryApp .less dt1 dt2)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 <= dt2 ===> !(dt2 < dt1)"
      (.binaryApp .lessEq dt1 dt2)
      (.unaryApp .not (.binaryApp .less dt2 dt1))
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: !(dt2 < dt1) ===> dt1 <= dt2"
      (.unaryApp .not (.binaryApp .less dt2 dt1))
      (.binaryApp .lessEq dt1 dt2)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 < dt2 ===> dt1 <= dt2"
      (.binaryApp .less dt1 dt2)
      (.binaryApp .lessEq dt1 dt2)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 = dt2 ===> dt1 <= dt2"
      (.binaryApp .eq dt1 dt2)
      (.binaryApp .lessEq dt1 dt2)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 <= dt2 ===> dt1 = dt2 ∨ dt1 < dt2"
      (.binaryApp .lessEq dt1 dt2)
      (.or (.binaryApp .eq dt1 dt2) (.binaryApp .less dt1 dt2))
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 <= dt2 ∧ !(dt1 = dt2) ===> dt1 < dt2"
      (.and (.binaryApp .lessEq dt1 dt2) (.unaryApp .not (.binaryApp .eq dt1 dt2)))
      (.binaryApp .less dt1 dt2)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 < dt2 ===> !(dt1 = dt2)"
      (.binaryApp .less dt1 dt2)
      (.unaryApp .not (.binaryApp .eq dt1 dt2))
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 <= dt2 ∧ dt2 <= dt1 ===> dt1 = dt2"
      (.and (.binaryApp .lessEq dt1 dt2) (.binaryApp .lessEq dt2 dt1))
      (.binaryApp .eq dt1 dt2)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 <= dt2 ∧ dt2 <= dt3 ===> dt1 <= dt3"
      (.and (.binaryApp .lessEq dt1 dt2) (.binaryApp .lessEq dt2 dt3))
      (.binaryApp .lessEq dt1 dt2)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 < dt2 ∧ dt2 < dt3 ===> dt1 < dt3"
      (.and (.binaryApp .less dt1 dt2) (.binaryApp .less dt2 dt3))
      (.binaryApp .lessEq dt1 dt3)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 < dt2 ∧ dt2 <= dt3 ===> dt1 < dt3"
      (.and (.binaryApp .less dt1 dt2) (.binaryApp .lessEq dt2 dt3))
      (.binaryApp .lessEq dt1 dt3)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 <= dt2 ∧ dt2 < dt3 ===> dt1 < dt3"
      (.and (.binaryApp .lessEq dt1 dt2) (.binaryApp .less dt2 dt3))
      (.binaryApp .lessEq dt1 dt3)
      datetimeSymEnv .unsat,
  ]

private def testOffset (dt₁ dur dt₂ : String) : TestCase SolverM :=
  testVerifyEquivalent s!"{dt₁} + {dur} -> {dt₂}"
    (.binaryApp .eq (.call .offset [dtLit dt₁, Duration.durLit dur]) (dtLit dt₂))
    (.lit (.bool true))
    datetimeSymEnv .unsat

def testsForOffset :=
  suite "Datetime.offset"
  [
    testOffset "2024-10-15" "0ms" "2024-10-15",
    testOffset "2024-10-15" "1ms" "2024-10-15T00:00:00.001Z",
    testOffset "2024-10-15" "1s" "2024-10-15T00:00:01Z",
    testOffset "2024-10-15" "-1s" "2024-10-14T23:59:59Z",
    testOffset "2024-10-15" "-14d" "2024-10-01",
    testOffset "2025-04-03" "-9224d1ms" "1999-12-31T23:59:59.999Z",
    testOffset "2021-04-03T12:01:00Z" "365d" "2022-04-03T12:01:00Z"
  ]

private def testDurationSince (dt₁ dt₂ dur : String) : TestCase SolverM :=
  testVerifyEquivalent s!"{dt₁} - {dt₂} -> {dur}"
    (.binaryApp .eq (.call .durationSince [dtLit dt₁, dtLit dt₂]) (Duration.durLit dur))
    (.lit (.bool true))
    datetimeSymEnv .unsat

def testsForDurationSince :=
  suite "Datetime.durationSince"
  [
    testDurationSince "2024-10-15" "2024-10-15"  "0ms",
    testDurationSince "2024-10-15" "2024-10-15T00:00:00.001Z" "-1ms",
    testDurationSince "2024-10-15" "2024-10-15T00:00:01Z" "-1s",
    testDurationSince "2024-10-15" "2024-10-14T23:59:59Z" "1s",
    testDurationSince "2024-10-15" "2024-10-01" "14d",
    testDurationSince "2025-04-03" "1999-12-31T23:59:59.999Z" "9224d1ms",
    testDurationSince "2021-04-03T12:01:00Z" "2022-04-03T12:01:00Z" "-365d",

    testVerifyImplies "Implies: MIN_DT <= offset dt1 dur <= MAX_DT ===> durationSince (offset dt1 dur) dt1 == dur1"
      (.and (.binaryApp .lessEq MIN_DT (.call .offset [dt1, dur1])) (.binaryApp .lessEq (.call .offset [dt1, dur1]) MAX_DT))
      (.binaryApp .eq
        (.call .durationSince [.call .offset [dt1, dur1], dt1])
        dur1
      )
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: -9223372036854775808ms <= durationSince dt2 dt1 <= 9223372036854775807ms ===> offset dt1 (durationSince dt2 dt1) == dt2"
      (.and
        (.binaryApp .lessEq (Duration.durLit "-9223372036854775808ms") (.call .durationSince [dt2, dt1]))
        (.binaryApp .lessEq (.call .durationSince [dt2, dt1]) (Duration.durLit "9223372036854775807ms"))
      )
      (.binaryApp .eq
        (.call .offset [dt1, (.call .durationSince [dt2, dt1])])
        dt2
      )
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: durationSince dt1 dt2 == 0ms ===> dt1 == dt2"
      (.binaryApp .eq (.call .durationSince [dt1, dt2]) (Duration.durLit "0ms"))
      (.binaryApp .eq dt1 dt2)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: durationSince dt1 dt2 < 0ms ===> dt1 < dt2"
      (.binaryApp .less (.call .durationSince [dt1, dt2]) (Duration.durLit "0ms"))
      (.binaryApp .less dt1 dt2)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: 0ms < durationSince dt1 dt2 ===> dt2 < dt1"
      (.binaryApp .less (Duration.durLit "0ms") (.call .durationSince [dt1, dt2]))
      (.binaryApp .less dt2 dt1)
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: offset dt1 dur1 == dt1 ===> dur1 == 0ms"
      (.binaryApp .eq (.call .offset [dt1, dur1]) dt1)
      (.binaryApp .eq dur1 (Duration.durLit "0ms"))
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: offset dt1 dur1 < dt1 ===> dur1 < 0ms"
      (.binaryApp .eq (.call .offset [dt1, dur1]) dt1)
      (.binaryApp .eq dur1 (Duration.durLit "0ms"))
      datetimeSymEnv .unsat,

    testVerifyImplies "Implies: dt1 < offset dt1 dur1 ===>  0ms < dur1"
      (.binaryApp .eq dt1 (.call .offset [dt1, dur1]))
      (.binaryApp .eq (Duration.durLit "0ms") dur1)
      datetimeSymEnv .unsat,
  ]

private def testToDate (dt₁ dt₂ : String) : TestCase SolverM :=
  testVerifyEquivalent s!"toDate {dt₁} -> {dt₂}"
    (.binaryApp .eq (.call .toDate [dtLit dt₁]) (dtLit dt₂))
    (.lit (.bool true))
    datetimeSymEnv .unsat

def TestsForToDate :=
  suite "Datetime.toDate"
  [
    testToDate "2024-10-15" "2024-10-15",
    testToDate "2024-10-15T00:00:01Z" "2024-10-15",
    testToDate "2024-10-15T23:59:59Z" "2024-10-15",
    testToDate "2024-10-15T23:59:00-0001" "2024-10-16",
    testToDate "1969-12-31" "1969-12-31",
    testToDate "1969-12-31T23:59:59Z" "1969-12-31",
  ]

private def testToTime (dt dur : String) : TestCase SolverM :=
  testVerifyEquivalent s!"toTime {dt} -> {dur}"
    (.binaryApp .eq (.call .toTime [dtLit dt]) (Duration.durLit dur))
    (.lit (.bool true))
    datetimeSymEnv .unsat

def TestsForToTime :=
  suite "Datetime.toTime"
  [
    testToTime "2024-10-15" "0ms",
    testToTime "2024-10-15T00:00:00.001Z" "1ms",
    testToTime "2024-10-15T00:00:01Z" "1s",
    testToTime "2024-10-15T23:59:59Z" "23h59m59s",
    testToTime "2024-10-15T23:59:00-0001" "0ms",
    testToTime "1969-12-31" "0ms",
    testToTime "1969-12-31T23:59:59Z" "23h59m59s",
    testToTime "1969-12-31T12:00:00Z" "12h",
  ]

def tests := [
  Duration.testsForDurationConstructor,
  Duration.testsForDurationComparisonOperations,
  Duration.testsForDurationConversions,
  testsForDatetimeConstructor,
  testsForDatetimeComparators,
  testsForOffset,
  testsForDurationSince,
  TestsForToDate,
  TestsForToTime
]

end SymTest.Datetime
