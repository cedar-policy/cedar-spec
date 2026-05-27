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

import Cedar.Frontend.Parser
import UnitTest.Run

/-! This file defines unit tests for parsing strings, entity UIDs, and identifiers. -/

namespace UnitTest.ParserStrings

open UnitTest Cedar.Spec.Cst Cedar.Spec.Cst.Parser

private def testParseOk (name : String) (input : String) (numPolicies : Nat) : TestCase IO :=
  test name ⟨fun _ => match parse input with
    | .ok ps => checkEq ps.ps.length numPolicies
    | .error e => pure (.error s!"parse failed: {e}")⟩

private def testParseFail (name : String) (input : String) : TestCase IO :=
  test name ⟨fun _ => checkEq (parse input).isOk false⟩

private def testParseFileOk (name : String) (path : String) (numPolicies : Nat) : TestCase IO :=
  test name ⟨fun _ => do
    let input ← IO.FS.readFile path
    match parse input with
    | .ok ps => checkEq ps.ps.length numPolicies
    | .error e => pure (.error s!"parse failed: {e}")⟩

/-- Parse a single expression wrapped in a policy -/
private def parseExpr (input : String) : Except String Expr :=
  let policy := "permit(principal, action, resource) when { " ++ input ++ " };"
  match parse policy with
  | .ok ps => match ps.ps with
    | [.policy p] => match p.conds with
      | [c] => .ok c.body
      | _ => .error "expected one condition"
    | _ => .error "expected one policy"
  | .error e => .error e

/-- Extract string literal value from a parsed expression -/
private def getStringLit (input : String) : Except String String := do
  let e ← parseExpr input
  let .expr impl := e
  let .edOr orE := impl.expr | .error "not edOr"
  if !orE.extended.isEmpty then .error "has or-extensions"
  let andE := orE.initial
  if !andE.extended.isEmpty then .error "has and-extensions"
  match andE.initial with
  | .rCommon addE _ =>
    if !addE.extended.isEmpty then .error "has add-extensions"
    let multE := addE.initial
    if !multE.extended.isEmpty then .error "has mult-extensions"
    let unaryE := multE.initial
    if unaryE.op.isSome then .error "has unary op"
    let memberE := unaryE.item
    if !memberE.access.isEmpty then .error "has member access"
    match memberE.item with
    | .literal (.liStr s) => .ok s
    | _ => .error "not a string literal"
  | _ => .error "not rCommon"

private def identToString : Ident → String
  | .idIdent s => s
  | .idPrincipal => "principal"
  | .idAction => "action"
  | .idResource => "resource"
  | .idContext => "context"
  | .idTrue => "true"
  | .idFalse => "false"
  | .idPermit => "permit"
  | .idForbid => "forbid"
  | .idWhen => "when"
  | .idUnless => "unless"
  | .idIn => "in"
  | .idHas => "has"
  | .idLike => "like"
  | .idIs => "is"
  | .idIf => "if"
  | .idThen => "then"
  | .idElse => "else"

/-- Extract EUID path and eid from `permit(principal == Type::"eid", ...)` -/
private def getEUID (input : String) : Except String (List String × String) := do
  let ps ← parse input
  match ps.ps with
  | [.policy p] =>
    match p.vars with
    | varDef :: _ =>
      match varDef.ineq with
      | some (_, eqExpr) =>
        let .expr impl := eqExpr
        let .edOr orE := impl.expr | .error "not edOr"
        match orE.initial.initial with
        | .rCommon addE _ =>
          match addE.initial.initial.item.item with
          | .ref (.uid name (.string eid)) =>
            let path := (name.path ++ [name.name]).map identToString
            .ok (path, eid)
          | _ => .error "not a ref uid"
        | _ => .error "not rCommon"
      | none => .error "no == constraint"
    | [] => .error "no vars"
  | _ => .error "not one policy"

/-- Extract annotation count -/
private def getAnnotationCount (input : String) : Except String Nat := do
  let ps ← parse input
  match ps.ps with
  | [.policy p] => .ok p.annotations.length
  | _ => .error "not one policy"

/-- Extract annotation name and value at index -/
private def getAnnotation (input : String) (idx : Nat) : Except String (String × Option String) := do
  let ps ← parse input
  match ps.ps with
  | [.policy p] =>
    match p.annotations[idx]? with
    | some ann =>
      let name := identToString ann.name
      let value := ann.value.map fun (.string s) => s
      .ok (name, value)
    | none => .error "annotation index out of bounds"
  | _ => .error "not one policy"

-- Custom check helpers that unwrap Except

private def checkStr (actual : Except String String) (expected : String) : IO TestResult :=
  match actual with
  | .ok s => checkEq s expected
  | .error e => pure (.error s!"extraction failed: {e}")

private def checkEUID (actual : Except String (List String × String)) (path : List String) (eid : String) : IO TestResult :=
  match actual with
  | .ok (p, e) =>
    if p == path && e == eid then pure (.ok ())
    else pure (.error s!"actual: ({p}, \"{e}\")\nexpected: ({path}, \"{eid}\")")
  | .error e => pure (.error s!"extraction failed: {e}")

private def checkAnn (actual : Except String (String × Option String)) (name : String) (value : Option String) : IO TestResult :=
  match actual with
  | .ok (n, v) =>
    if n == name && v == value then pure (.ok ())
    else pure (.error s!"actual: ({n}, {v})\nexpected: ({name}, {value})")
  | .error e => pure (.error s!"extraction failed: {e}")

private def checkNat (actual : Except String Nat) (expected : Nat) : IO TestResult :=
  match actual with
  | .ok n => checkEq n expected
  | .error e => pure (.error s!"extraction failed: {e}")

----- Test suites -----

def testsForStringEscapes :=
  suite "ParserStrings.Escapes"
  [
    test "newline" ⟨fun _ => checkStr (getStringLit "\"hello\\nworld\"") "hello\nworld"⟩,
    test "tab" ⟨fun _ => checkStr (getStringLit "\"tab\\there\"") "tab\there"⟩,
    test "quote" ⟨fun _ => checkStr (getStringLit "\"a\\\"b\"") "a\"b"⟩,
    test "backslash" ⟨fun _ => checkStr (getStringLit "\"a\\\\b\"") "a\\b"⟩,
    test "null" ⟨fun _ => checkStr (getStringLit "\"a\\0b\"") (String.ofList ['a', '\x00', 'b'])⟩,
    test "empty" ⟨fun _ => checkStr (getStringLit "\"\"") ""⟩,
    test "spaces" ⟨fun _ => checkStr (getStringLit "\"   \"") "   "⟩,
    test "special chars" ⟨fun _ => checkStr (getStringLit "\"!@#$%\"") "!@#$%"⟩
  ]

def testsForEntityUIDs :=
  suite "ParserStrings.EntityUIDs"
  [
    test "simple" ⟨fun _ =>
      checkEUID (getEUID "permit(principal == User::\"alice\", action, resource);") ["User"] "alice"⟩,
    test "empty eid" ⟨fun _ =>
      checkEUID (getEUID "permit(principal == User::\"\", action, resource);") ["User"] ""⟩,
    test "eid with space" ⟨fun _ =>
      checkEUID (getEUID "permit(principal == User::\"alice bob\", action, resource);") ["User"] "alice bob"⟩,
    test "eid with escaped quote" ⟨fun _ =>
      checkEUID (getEUID "permit(principal == User::\"a\\\"b\", action, resource);") ["User"] "a\"b"⟩,
    test "eid with backslash" ⟨fun _ =>
      checkEUID (getEUID "permit(principal == User::\"a\\\\b\", action, resource);") ["User"] "a\\b"⟩,
    test "namespaced 2" ⟨fun _ =>
      checkEUID (getEUID "permit(principal == App::User::\"alice\", action, resource);") ["App", "User"] "alice"⟩,
    test "namespaced 3" ⟨fun _ =>
      checkEUID (getEUID "permit(principal == Com::Ex::User::\"x\", action, resource);") ["Com", "Ex", "User"] "x"⟩,
    test "special chars in eid" ⟨fun _ =>
      checkEUID (getEUID "permit(principal == User::\"user@example.com\", action, resource);") ["User"] "user@example.com"⟩,
    testParseFail "missing eid" "permit(principal == User::, action, resource);",
    testParseFail "number as type" "permit(principal == 123::\"alice\", action, resource);"
  ]

def testsForAnnotations :=
  suite "ParserStrings.Annotations"
  [
    test "with value" ⟨fun _ =>
      checkAnn (getAnnotation "@id(\"policy1\")\npermit(principal, action, resource);" 0) "id" (some "policy1")⟩,
    test "without value" ⟨fun _ =>
      checkAnn (getAnnotation "@shadow_mode\npermit(principal, action, resource);" 0) "shadow_mode" none⟩,
    test "count 3" ⟨fun _ =>
      checkNat (getAnnotationCount "@a(\"1\")\n@b(\"2\")\n@c\npermit(principal, action, resource);") 3⟩,
    test "second annotation" ⟨fun _ =>
      checkAnn (getAnnotation "@first(\"x\")\n@second(\"y\")\npermit(principal, action, resource);" 1) "second" (some "y")⟩
  ]

def testsForIdentifiers :=
  suite "ParserStrings.Identifiers"
  [
    testParseOk "camelCase" "permit(principal, action, resource) when { resource.camelCase == \"x\" };" 1,
    testParseOk "snake_case" "permit(principal, action, resource) when { resource.snake_case == \"x\" };" 1,
    testParseOk "leading underscore" "permit(principal, action, resource) when { resource._private == \"x\" };" 1,
    testParseOk "single char" "permit(principal, action, resource) when { resource.x == \"x\" };" 1,
    testParseOk "ALLCAPS" "permit(principal, action, resource) when { resource.ALLCAPS == \"x\" };" 1,
    testParseOk "with digits" "permit(principal, action, resource) when { resource.field123 == \"x\" };" 1,
    testParseOk "has with string key" "permit(principal, action, resource) when { context has \"spaces in name\" };" 1,
    testParseOk "record string keys" "permit(principal, action, resource) when { {\"key with spaces\": 1} == context.x };" 1,
    testParseOk "record ident keys" "permit(principal, action, resource) when { {normalKey: 1} == context.x };" 1
  ]

def testsForFile :=
  suite "ParserStrings.File"
  [
    testParseFileOk "strings_and_identifiers.cedar" "UnitTest/parser_tests/strings_and_identifiers.cedar" 62
  ]

def tests : List (TestSuite IO) :=
  [testsForStringEscapes, testsForEntityUIDs, testsForAnnotations, testsForIdentifiers, testsForFile]

end UnitTest.ParserStrings
