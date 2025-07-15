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

import Cedar.SymCC.Decoder
import SymTest.Util

/-!
This file contains unit tests for Cedar.SymCC.Decoder.
-/

namespace SymTest.Decoder

open Cedar Spec Validation Data UnitTest SymCC Decoder
open Std.Internal.Parsec String Batteries

private def testParseOk {α} [BEq α] [Repr α] (parser : Parser α) (str : String) (expected : α) : TestCase IO :=
  test str ⟨λ _ => checkBEq (parser.run str) (Except.ok expected)⟩

private def testParseError {α} [BEq α] [Repr α] (parser : Parser α) (str : String) : TestCase IO :=
  test str ⟨λ _ => checkBEq (parser.run str).isOk false⟩

def testsParseValidSMTStrings :=
  suite "Decoder.parse* for valid strings"
  [
    testParseOk «(» "(" (),
    testParseOk «(» "(  " (),
    testParseOk «)» ")" (),
    testParseOk «)» ")  " (),
    testParseOk parseSymbol "+-/*=%?!.$_˜&ˆ<>@" "+-/*=%?!.$_˜&ˆ<>@",
    testParseOk parseSymbol "define-fun" "define-fun",
    testParseOk parseSymbol "define-fun  " "define-fun",
    testParseOk parseSymbol "|define !@#$%^&*() fun|" "|define !@#$%^&*() fun|",
    testParseOk parseSymbol "|quoted with space|  " "|quoted with space|",
    testParseOk parseNat "0" 0,
    testParseOk parseNat "123   " 123,
    testParseOk parseString "\"\""  "",
    testParseOk parseString "\"a b c  ¬ \"\"s \""  "a b c  ¬ \"s ",
    testParseOk parseBinary "#b0" [false],
    testParseOk parseBinary "#b1011" [true, false, true, true],
    testParseOk SExpr.parse "true" (.symbol "true"),
    testParseOk SExpr.parse "123" (.numeral 123),
    testParseOk SExpr.parse "\"hello \"\"world\"\"\"" (.string "hello \"world\""),
    testParseOk SExpr.parse "#b1011" (.bitvec 11#4),
    testParseOk SExpr.parse "(hello \"world\" (123 #b10))" (.sexpr [.symbol "hello", .string "world",
      .sexpr [.numeral 123, .bitvec 2#2]])
  ]

def testsParseInvalidSMTStrings :=
  suite "Decoder.parse* for invalid strings"
  [
    testParseError «(» ")",
    testParseError «(» " (  ", -- leading spaces not ok
    testParseError «)» "(",
    testParseError «)» "  )  ",
    testParseError parseSymbol "\"define-fun",
    testParseError parseSymbol "3define-fun",
    testParseError parseSymbol "|define-fun",
    testParseError parseSymbol "|define\\fun|",
    testParseError parseNat "",
    testParseError parseNat " 123   ", -- leading spaces not ok
    testParseError parseNat "-3",
    testParseError parseString "",
    testParseError parseString "\"",
    testParseError parseString "\"\"\"",
    testParseError parseBinary "#b",
    testParseError parseBinary "#bc",
    testParseError SExpr.parse "(",
    testParseError SExpr.parse ")",
    testParseError SExpr.parse "(1",
    testParseError SExpr.parse "(foo bar",
  ]

private def colorType : EntityType := ⟨"Color", []⟩
private def userType : EntityType := ⟨"User", []⟩
private def groupType : EntityType := ⟨"Group", []⟩

private def types : IdMap TermType := IdMap.ofList [
  ("E0", .entity colorType),
  ("E1", .entity userType),
  ("E2", .entity groupType),
  ("R3", .record Map.empty),
  ("R4", .record (Map.make [
    ("a", .option .bool),
    ("b", .bitvec 64),
    ("c", .entity colorType),  ]), ),
  ("R5", .record (Map.make [
      ("e", .bool)])),
  ("R6", .record (Map.make [
    ("d", .record (Map.make [
      ("e", .bool)]))])),
  ("R7", .record (Map.make [
    ("r", .entity colorType)
  ])),
]

private def enums : IdMap EntityUID := IdMap.ofList [
  ("E0_m0", ⟨colorType, "blue"⟩),
  ("E0_m1", ⟨colorType, "green"⟩),
  ("E0_m2", ⟨colorType, "red"⟩),
]

private def vars : IdMap TermVar := IdMap.ofList [
  ("t1", ⟨"f", .entity colorType⟩),
  ("t2", ⟨"g", .entity userType⟩),
  ("t3", ⟨"h", .entity groupType⟩),
  ("t4", ⟨"i", .record Map.empty⟩),
  ("t5", ⟨"j", .record (Map.make [("e", .bool)])⟩),
]

private def uufs : IdMap UUF := IdMap.ofList [
  ("f1", ⟨"k", .entity userType, (.set (.entity groupType))⟩),
  ("f2", ⟨"l", .entity userType, (.record (Map.make [("r", .entity colorType)])) ⟩),
]

private def ids : IdMaps := ⟨types, vars, uufs, enums⟩

private def getValue! [Inhabited α] (m : IdMap α) (key : String) : α :=
  if let some v := m.find? key then v else default

private def types.get! (key : String) := getValue! types key
private def enums.get! (key : String) := getValue! enums key
private def vars.get! (key : String) := getValue! vars key
private def uufs.get! (key : String) := getValue! uufs key

private def parse! (str : String) : SExpr :=
  match SExpr.parse.run str with
  | .ok x    => x
  | .error _ => .sexpr []

private def testDecodeOk {α} [BEq α] [Repr α] (f : SExpr → Decoder.Result α) (str : String) (expected : α) : TestCase IO :=
  test str ⟨λ _ => checkBEq (f (parse! str)) (Except.ok expected)⟩

private def testDecodeError {α} [BEq α] [Repr α] (f : SExpr → Decoder.Result α) (str : String) : TestCase IO :=
  test str ⟨λ _ => checkBEq (f (parse! str)).isOk false⟩

private def testDecodeTypeOk := (testDecodeOk (SExpr.decodeType types))

private def testDecodeTypeError := (testDecodeError (SExpr.decodeType types))

def testsDecodeValidTypeStrings :=
  suite "Decoder.SExpr.decodeType for valid type strings"
  [
    testDecodeTypeOk "Bool" .bool,
    testDecodeTypeOk "String" .string,
    testDecodeTypeOk "Decimal" (.ext .decimal),
    testDecodeTypeOk "IPAddr" (.ext .ipAddr),
    testDecodeTypeOk "Duration" (.ext .duration),
    testDecodeTypeOk "Datetime" (.ext .datetime),
    testDecodeTypeOk "E1" (types.get! "E1"),
    testDecodeTypeOk "E2" (types.get! "E2"),
    testDecodeTypeOk "R3" (types.get! "R3"),
    testDecodeTypeOk "R4" (types.get! "R4"),
    testDecodeTypeOk "(_ BitVec 64)" (.bitvec 64),
    testDecodeTypeOk "(_ BitVec 32)" (.bitvec 32),
    testDecodeTypeOk "(_ BitVec 128)" (.bitvec 128),
    testDecodeTypeOk "(_ BitVec 5)" (.bitvec 5),
    testDecodeTypeOk "(_ BitVec 7 ) " (.bitvec 7),
    testDecodeTypeOk "(Option Bool )" (.option .bool),
    testDecodeTypeOk "(Option (_ BitVec 64) ) " (.option (.bitvec 64)),
    testDecodeTypeOk "(Option R4 )" (.option (types.get! "R4")),
    testDecodeTypeOk "(Set Bool)" (.set .bool),
    testDecodeTypeOk "(Set (_ BitVec 64)) " (.set (.bitvec 64)),
    testDecodeTypeOk "(Set R4)" (.set (types.get! "R4")),
    testDecodeTypeOk "(Set (Option (_ BitVec 64)))" (.set (.option (.bitvec 64))),
    testDecodeTypeOk "(Set (Option (Set E1)))" (.set (.option (.set (types.get! "E1")))),
  ]

def testsDecodeInvalidTypeStrings :=
  suite "Decoder.SExpr.decodeType for invalid type strings"
  [
    testDecodeTypeError "bool",
    testDecodeTypeError "",
    testDecodeTypeError "()",
    testDecodeTypeError "(Set foo)",
    testDecodeTypeError "(set Bool)",
  ]

private def testDecodeLitOk := (testDecodeOk (SExpr.decodeLit ids))

private def testDecodeLitError := (testDecodeError (SExpr.decodeLit ids))

def testsDecodeValidLitStrings :=
  suite "Decoder.SExpr.decodeLit for valid literal expression strings"
  [
    testDecodeLitOk "true" (.bool true),
    testDecodeLitOk "false" (.bool false),
    testDecodeLitOk "#b0001" (.bitvec 1#4),
    testDecodeLitOk "\"hello world\"" (.string "hello world"),
    testDecodeLitOk "E0_m0" (.entity (enums.get! "E0_m0")),
    testDecodeLitOk "E0_m1" (.entity (enums.get! "E0_m1")),
    testDecodeLitOk "E0_m2" (.entity (enums.get! "E0_m2")),
    testDecodeLitOk "((as some (Option E0)) E0_m0)" (.some (.entity (enums.get! "E0_m0"))),
    testDecodeLitOk "(as none (Option Bool))" (.none .bool),
    testDecodeLitOk "(as set.empty (Set (_ BitVec 64)))" (.set Set.empty (.bitvec 64)),
    testDecodeLitOk "(set.singleton (set.singleton #b0001))" (.set (Set.singleton (.set (Set.singleton 1#4) (.bitvec 4))) (.set (.bitvec 4))),
    testDecodeLitOk "(set.union (set.singleton #b00) (set.union (set.singleton #b01) (set.singleton #b10)))" (.set (Set.mk [0#2, 1#2, 2#2]) (.bitvec 2)),
    testDecodeLitOk "(Decimal #b0000000000000000000000000000000000000000000000000000000000001010)" (.ext (.decimal (Int64.ofBitVec 10#64))),
    testDecodeLitOk "(Duration #b0000000000000000000000000000000000000000000000000000000000001011)" (.ext (.duration ⟨Int64.ofBitVec 11#64⟩)),
    testDecodeLitOk "(Datetime #b0000000000000000000000000000000000000000000000000000000000001111)" (.ext (.datetime ⟨Int64.ofBitVec 15#64⟩)),
    testDecodeLitOk "(V4 #b00000000000000000000000000000000 (as none (Option (_ BitVec 5))))" (.ext (.ipaddr (.V4 ⟨0#32, .none⟩))),
    testDecodeLitOk "(V4 #b00000000000000000000000000000000 ((as some (Option (_ BitVec 5))) #b00001))" (.ext (.ipaddr (.V4 ⟨0#32, 1#5⟩))),
    testDecodeLitOk "(V6 #b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 (as none (Option (_ BitVec 7))))" (.ext (.ipaddr (.V6 ⟨0#128, .none⟩))),
    testDecodeLitOk "(V6 #b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 ((as some (Option (_ BitVec 7))) #b0000001))" (.ext (.ipaddr (.V6 ⟨0#128, 1#7⟩))),
    testDecodeLitOk "(E1 \"Alice\")" (.entity ⟨userType, "Alice"⟩),
    testDecodeLitOk "(R3)" (.record Map.empty),
    testDecodeLitOk "(R4 (as none (Option Bool)) #b0000000000000000000000000000000000000000000000000000000000001010 E0_m2)"
      (.record (Map.make [("a", .none .bool), ("b", 10#64), ("c", .entity ⟨colorType, "red"⟩)])),
    testDecodeLitOk "(R6 (R5 true))" (.record (Map.make [("d", .record (Map.make [("e", .bool true)]))])),
  ]

def testsDecodeInvalidLitStrings :=
  suite "Decoder.SExpr.decodeLit for invalid literal expression strings"
  [
    testDecodeLitError "True",
    testDecodeLitError "()",
    testDecodeLitError "(some)",
    testDecodeLitError "(some E0_m0)",
    testDecodeLitError "(as none Bool)",
    testDecodeLitError "(as set.empty Bool)", -- must be a set type
    testDecodeLitError "(set.union (set.singleton true) false)",
    testDecodeLitError "(R4)",
    testDecodeLitError "(R4) true #b0000000000000000000000000000000000000000000000000000000000001010 E0_m2)",
    testDecodeLitError "(R4) (as none (Option Bool)) #b1010 E0_m2)",
    testDecodeLitError "(R4 (as none (Option Bool)) #b0000000000000000000000000000000000000000000000000000000000001010 false)"
  ]

private def testDecodeTableOk := (testDecodeOk (SExpr.decodeUnaryFunctionTable "x" ids))

private def testDecodeTableError := (testDecodeError (SExpr.decodeUnaryFunctionTable "x" ids))

def testsDecodeValidFunctionTableStrings :=
  suite "Decoder.SExpr.decodeUnaryFunctionTable for valid unary function body strings"
  [
    testDecodeTableOk "true" ([], .bool true),
    testDecodeTableOk "(ite (= #b0000 x) #b0001 #b0010)" ([(0#4, 1#4)], 2#4),
    testDecodeTableOk "(ite (= #b0000 x) #b0001 (ite (= #b0001 x) #b0010 #b0011))" ([(0#4, 1#4), (1#4, 2#4)], 3#4),
  ]

def testsDecodeInvalidFunctionTableStrings :=
  suite "Decoder.SExpr.decodeUnaryFunctionTable for invalid unary function body strings"
  [
    testDecodeTableError "foo",
    testDecodeTableError "(ite (= x #b0000) #b0001 #b0010)",
    testDecodeTableError "(ite (= #b0000 y) #b0001 #b0010)", -- we're using x as var name in these tests
    testDecodeTableError "(ite (= #b0000 x) (ite (= #b0001 x) #b0010 #b0011) #b0010)",
  ]

private def testDecodeModelOk := (testDecodeOk (SExpr.decodeModel ids))

private def testDecodeModelError := (testDecodeError (SExpr.decodeModel ids))

private abbrev mkvars : List (TermVar × Term) → VarMap := (List.toRBMap · (compareOfLessAndEq · ·))
private abbrev mkuufs : List (UUF × UDF) → UUFMap := (List.toRBMap · (compareOfLessAndEq · ·))

def testsDecodeValidModelStrings :=
  suite "Decoder.SExpr.decodeModel for valid model strings"
  [
    testDecodeModelOk "()" (mkvars [], mkuufs []),
    testDecodeModelOk "((define-fun t1 () E0 E0_m0))"
      (mkvars [(vars.get! "t1", .entity ⟨colorType, "blue"⟩)],
       mkuufs []),
    testDecodeModelOk "((define-fun t1 () E0 E0_m0) (define-fun t4 () R3 (R3)))"
      (mkvars [
        (vars.get! "t1", .entity ⟨colorType, "blue"⟩),
        (vars.get! "t4", .record Map.empty)],
       mkuufs []),
    testDecodeModelOk "((define-fun f1 ((_arg_1 E1)) (Set E2) (as set.empty (Set E2))))"
      (mkvars [],
       mkuufs [(uufs.get! "f1", ⟨.entity userType, .set (.entity groupType), Map.empty, .set Set.empty (.entity groupType)⟩)]),
    testDecodeModelOk "(
      (define-fun f2 ((_arg_1 E1)) R7
        (ite (= (E1 \"Alice\") _arg_1) (R7 E0_m1) (R7 E0_m2))))"
      (mkvars [],
       mkuufs [
        (uufs.get! "f2",
         ⟨.entity userType,
          .record (Map.make [("r", .entity colorType)]),
          Map.make [(.entity ⟨userType, "Alice"⟩, .record (Map.make [("r", .entity ⟨colorType, "green"⟩)]) )],
          .record (Map.make [("r", .entity ⟨colorType, "red"⟩)])⟩)
      ]),
    testDecodeModelOk "(
      (define-fun t1 () E0 E0_m0)
      (define-fun f1 ((_arg_1 E1)) (Set E2) (as set.empty (Set E2)))
      (define-fun t4 () R3 (R3)))"
      (mkvars [
        (vars.get! "t1", .entity ⟨colorType, "blue"⟩),
        (vars.get! "t4", .record Map.empty)],
       mkuufs [
        (uufs.get! "f1", ⟨.entity userType, .set (.entity groupType), Map.empty, .set Set.empty (.entity groupType)⟩)
        ]),
  ]

def testsDecodeInvalidModelStrings :=
  suite "Decoder.SExpr.decodeModel for invalid model strings"
  [
    testDecodeModelError "true",
    testDecodeModelError "(true)",
    testDecodeModelError "((define-fun foo () E0 E0_m0))",
    testDecodeModelError "((define-fun t1 () E1 E0_m0))",
    testDecodeModelError "((define-fun t1 (()) E0 E0_m0))",
    testDecodeModelError "((define-fun f1 () (Set E2) (as set.empty (Set E2))))",
    testDecodeModelError "((define-fun f1 ((_arg_1 E2)) (Set E2) (as set.empty (Set E2))))",
    testDecodeModelError "((define-fun f1 ((_arg_1 E1) (_arg_2 E2)) (Set E2) (as set.empty (Set E2))))",
  ]

private def eidOf (ety : EntityType) : String :=
  if ety = colorType then "blue" else ""

private def testDefault {α β} [BEq β] [Repr β]
  (desc : String)
  (dflt : (EntityType → String) → α → β) (arg : α) (expected : β) : TestCase IO :=
  test desc ⟨λ _ => checkBEq (dflt eidOf arg) expected⟩

def testsDefaultLit :=
  suite "Decoder.defaultLit"
  [
    testDefault "bool" defaultLit .bool false,
    testDefault "bitvec" defaultLit (.bitvec 64) 0#64,
    testDefault "string" defaultLit .string "",
    testDefault "standard entity" defaultLit (.entity userType) (.entity ⟨userType, ""⟩),
    testDefault "enum entity" defaultLit (.entity colorType) (.entity ⟨colorType, "blue"⟩),
    testDefault "decimal" defaultLit (.ext .decimal) (.ext (.decimal (Int64.ofBitVec 0#64))),
    testDefault "datetime" defaultLit (.ext .datetime) (.ext (.datetime ⟨Int64.ofBitVec 0#64⟩)),
    testDefault "duration" defaultLit (.ext .duration) (.ext (.duration ⟨Int64.ofBitVec 0#64⟩)),
    testDefault "ipaddr" defaultLit (.ext .ipAddr) (.ext (.ipaddr (.V4 ⟨0#32, .none⟩))),
    testDefault "option" defaultLit (.option .bool) (.none .bool),
    testDefault "set" defaultLit (.set .bool) (.set Set.empty .bool),
    testDefault "set of set" defaultLit (.set (.set .bool)) (.set Set.empty (.set .bool)),
    testDefault "empty record" defaultLit (types.get! "R3") (.record Map.empty),
    testDefault "nonempty record" defaultLit (types.get! "R4")
      (.record (Map.make [
        ("a", .none .bool),
        ("b", .bitvec 0#64),
        ("c", .entity ⟨colorType, "blue"⟩)
      ]))
  ]

def testsDefaultUDF :=
  suite "Decoder.defaultUDF"
  [
    testDefault "f1" defaultUDF (uufs.get! "f1")
      ⟨.entity userType,
       .set (.entity groupType),
       Map.empty,
       .set Set.empty (.entity groupType)⟩,
    testDefault "f2" defaultUDF (uufs.get! "f2")
      ⟨.entity userType,
       .record (Map.make [("r", .entity colorType)]),
       Map.empty,
       .record (Map.make [("r", .entity ⟨colorType, "blue"⟩)])⟩,
  ]


def tests := [
  testsParseValidSMTStrings,
  testsParseInvalidSMTStrings,
  testsDecodeValidTypeStrings,
  testsDecodeInvalidTypeStrings,
  testsDecodeValidLitStrings,
  testsDecodeInvalidLitStrings,
  testsDecodeValidFunctionTableStrings,
  testsDecodeInvalidFunctionTableStrings,
  testsDecodeValidModelStrings,
  testsDecodeInvalidModelStrings,
  testsDefaultLit,
  testsDefaultUDF,
]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end SymTest.Decoder
