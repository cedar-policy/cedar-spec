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

/-! This file defines unit tests for the Cedar policy parser. -/

namespace UnitTest.Parser

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

private def testParseFail' (name : String) (path : String) : TestCase IO :=
  test s!"neg: {name}" ⟨fun _ => do
    let input ← IO.FS.readFile path
    checkEq (parse input).isOk false⟩

def testsForBasicPolicies :=
  suite "Parser.BasicPolicies"
  [
    testParseOk "minimal permit"
      "permit(principal, action, resource);" 1,
    testParseOk "minimal forbid"
      "forbid(principal, action, resource);" 1,
    testParseOk "multiple policies"
      "permit(principal, action, resource); forbid(principal, action, resource);" 2,
    testParseOk "with line comments"
      "// comment\npermit(principal, action, resource);" 1,
    testParseFail "missing semicolon"
      "permit(principal, action, resource)",
    testParseFail "missing closing paren"
      "permit(principal, action, resource;",
    testParseOk "empty input"
      "" 0
  ]

def testsForScopes :=
  suite "Parser.Scopes"
  [
    testParseOk "principal =="
      "permit(principal == User::\"alice\", action, resource);" 1,
    testParseOk "principal in"
      "permit(principal in Group::\"admins\", action, resource);" 1,
    testParseOk "principal is"
      "permit(principal is User, action, resource);" 1,
    testParseOk "principal is in"
      "permit(principal is User in Group::\"admins\", action, resource);" 1,
    testParseOk "action =="
      "permit(principal, action == Action::\"read\", resource);" 1,
    testParseOk "action in list"
      "permit(principal, action in [Action::\"read\", Action::\"write\"], resource);" 1,
    testParseOk "resource =="
      "permit(principal, action, resource == File::\"x\");" 1,
    testParseOk "resource in"
      "permit(principal, action, resource in Folder::\"docs\");" 1,
    testParseOk "all constrained"
      "forbid(principal == User::\"x\", action == Action::\"y\", resource in Folder::\"z\");" 1
  ]

def testsForConditions :=
  suite "Parser.Conditions"
  [
    testParseOk "when"
      "permit(principal, action, resource) when { true };" 1,
    testParseOk "unless"
      "forbid(principal, action, resource) unless { false };" 1,
    testParseOk "when + unless"
      "permit(principal, action, resource) when { true } unless { false };" 1,
    testParseOk "multiple when"
      "permit(principal, action, resource) when { true } when { true };" 1
  ]

def testsForExpressions :=
  suite "Parser.Expressions"
  [
    testParseOk "if-then-else"
      "permit(principal, action, resource) when { if true then 1 else 2 };" 1,
    testParseOk "nested if-then-else"
      "permit(principal, action, resource) when { if true then if false then 1 else 2 else 3 };" 1,
    testParseOk "or"
      "permit(principal, action, resource) when { true || false };" 1,
    testParseOk "chained or"
      "permit(principal, action, resource) when { true || false || true };" 1,
    testParseOk "and"
      "permit(principal, action, resource) when { true && false };" 1,
    testParseOk "chained and"
      "permit(principal, action, resource) when { true && false && true };" 1,
    testParseOk "or and precedence"
      "permit(principal, action, resource) when { true || false && true };" 1,
    testParseOk "not"
      "permit(principal, action, resource) when { !true };" 1,
    testParseOk "double not"
      "permit(principal, action, resource) when { !!true };" 1,
    testParseOk "numeric negation"
      "permit(principal, action, resource) when { -context.x };" 1
  ]

def testsForArithmetic :=
  suite "Parser.Arithmetic"
  [
    testParseOk "addition"
      "permit(principal, action, resource) when { 1 + 2 };" 1,
    testParseOk "subtraction"
      "permit(principal, action, resource) when { 5 - 3 };" 1,
    testParseOk "multiplication"
      "permit(principal, action, resource) when { 2 * 3 };" 1,
    testParseOk "division"
      "permit(principal, action, resource) when { 10 / 2 };" 1,
    testParseOk "modulo"
      "permit(principal, action, resource) when { 10 % 3 };" 1,
    testParseOk "chained add/sub"
      "permit(principal, action, resource) when { 1 + 2 - 3 + 4 };" 1,
    testParseOk "chained mul/div/mod"
      "permit(principal, action, resource) when { 2 * 3 / 4 % 5 };" 1,
    testParseOk "precedence"
      "permit(principal, action, resource) when { 1 + 2 * 3 };" 1,
    testParseOk "parens override precedence"
      "permit(principal, action, resource) when { (1 + 2) * 3 };" 1
  ]

def testsForComparisons :=
  suite "Parser.Comparisons"
  [
    testParseOk "less"
      "permit(principal, action, resource) when { context.x < 10 };" 1,
    testParseOk "lessEq"
      "permit(principal, action, resource) when { context.x <= 10 };" 1,
    testParseOk "greater"
      "permit(principal, action, resource) when { context.x > 0 };" 1,
    testParseOk "greaterEq"
      "permit(principal, action, resource) when { context.x >= 1 };" 1,
    testParseOk "eq"
      "permit(principal, action, resource) when { context.x == 1 };" 1,
    testParseOk "neq"
      "permit(principal, action, resource) when { context.x != 0 };" 1
  ]

def testsForRelations :=
  suite "Parser.Relations"
  [
    testParseOk "in"
      "permit(principal, action, resource) when { principal in Group::\"x\" };" 1,
    testParseOk "has"
      "permit(principal, action, resource) when { resource has owner };" 1,
    testParseOk "like"
      "permit(principal, action, resource) when { resource.name like \"*.txt\" };" 1,
    testParseOk "is"
      "permit(principal, action, resource) when { resource is Folder };" 1,
    testParseOk "is in"
      "permit(principal, action, resource) when { resource is Folder in Folder::\"root\" };" 1
  ]

def testsForMemberAccess :=
  suite "Parser.MemberAccess"
  [
    testParseOk "field"
      "permit(principal, action, resource) when { resource.owner };" 1,
    testParseOk "chained fields"
      "permit(principal, action, resource) when { context.a.b.c };" 1,
    testParseOk "index"
      "permit(principal, action, resource) when { resource.tags[\"env\"] };" 1,
    testParseOk "call no args"
      "permit(principal, action, resource) when { resource.tags.size() };" 1,
    testParseOk "call one arg"
      "permit(principal, action, resource) when { [1,2].contains(1) };" 1,
    testParseOk "call multiple args"
      "permit(principal, action, resource) when { context.x.foo(1, 2, 3) };" 1,
    testParseOk "mixed access"
      "permit(principal, action, resource) when { resource.tags[\"x\"].size() };" 1
  ]

def testsForPrimary :=
  suite "Parser.Primary"
  [
    testParseOk "true"
      "permit(principal, action, resource) when { true };" 1,
    testParseOk "false"
      "permit(principal, action, resource) when { false };" 1,
    testParseOk "number"
      "permit(principal, action, resource) when { 42 };" 1,
    testParseOk "string"
      "permit(principal, action, resource) when { \"hello\" };" 1,
    testParseOk "string escapes"
      "permit(principal, action, resource) when { \"a\\nb\\tc\\\\d\\\"e\" };" 1,
    testParseOk "entity ref"
      "permit(principal, action, resource) when { User::\"alice\" };" 1,
    testParseOk "namespaced entity ref"
      "permit(principal, action, resource) when { App::User::\"alice\" };" 1,
    testParseOk "empty list"
      "permit(principal, action, resource) when { [] };" 1,
    testParseOk "list"
      "permit(principal, action, resource) when { [1, 2, 3] };" 1,
    testParseOk "empty record"
      "permit(principal, action, resource) when { {} };" 1,
    testParseOk "record"
      "permit(principal, action, resource) when { {\"a\": 1, \"b\": true} };" 1,
    testParseOk "slot ?principal"
      "permit(principal == ?principal, action, resource);" 1,
    testParseOk "slot ?resource"
      "permit(principal, action, resource in ?resource);" 1,
    testParseOk "parenthesized"
      "permit(principal, action, resource) when { (1 + 2) };" 1,
    testParseOk "variables"
      "permit(principal, action, resource) when { principal == resource };" 1
  ]

def testsForFiles :=
  suite "Parser.Files"
  [
    testParseFileOk "comprehensive.cedar"
      "UnitTest/parser_tests/comprehensive.cedar" 100,
    -- Syntactic errors that the parser must reject
    testParseFail' "missing_semicolon" "UnitTest/parser_tests/negative/missing_semicolon.cedar",
    testParseFail' "missing_close_paren" "UnitTest/parser_tests/negative/missing_close_paren.cedar",
    testParseFail' "missing_open_paren" "UnitTest/parser_tests/negative/missing_open_paren.cedar",
    testParseFail' "no_effect" "UnitTest/parser_tests/negative/no_effect.cedar",
    testParseFail' "double_effect" "UnitTest/parser_tests/negative/double_effect.cedar",
    testParseFail' "missing_when_brace" "UnitTest/parser_tests/negative/missing_when_brace.cedar",
    testParseFail' "unclosed_when_brace" "UnitTest/parser_tests/negative/unclosed_when_brace.cedar",
    testParseFail' "unclosed_string" "UnitTest/parser_tests/negative/unclosed_string.cedar",
    testParseFail' "annotation_after_effect" "UnitTest/parser_tests/negative/annotation_after_effect.cedar",
    testParseFail' "double_semicolon" "UnitTest/parser_tests/negative/double_semicolon.cedar",
    testParseFail' "condition_without_braces" "UnitTest/parser_tests/negative/condition_without_braces.cedar",
    testParseFail' "invalid_entity_ref" "UnitTest/parser_tests/negative/invalid_entity_ref.cedar",
    testParseFail' "unclosed_list" "UnitTest/parser_tests/negative/unclosed_list.cedar",
    testParseFail' "unclosed_record" "UnitTest/parser_tests/negative/unclosed_record.cedar",
    testParseFail' "invalid_annotation_placement" "UnitTest/parser_tests/negative/invalid_annotation_placement.cedar",
    testParseFail' "missing_condition_keyword" "UnitTest/parser_tests/negative/missing_condition_keyword.cedar",
    testParseFail' "pipe_instead_of_or" "UnitTest/parser_tests/negative/pipe_instead_of_or.cedar",
    testParseFail' "ampersand_instead_of_and" "UnitTest/parser_tests/negative/ampersand_instead_of_and.cedar",
    testParseFail' "like_without_pattern" "UnitTest/parser_tests/negative/like_without_pattern.cedar",
    testParseFail' "unclosed_paren_expr" "UnitTest/parser_tests/negative/unclosed_paren_expr.cedar",
    testParseFail' "empty_when_body" "UnitTest/parser_tests/negative/empty_when_body.cedar",
    testParseFail' "missing_eid_in_ref" "UnitTest/parser_tests/negative/missing_eid_in_ref.cedar",
    testParseFail' "dot_without_field" "UnitTest/parser_tests/negative/dot_without_field.cedar",
    testParseFail' "eq_instead_of_double_eq" "UnitTest/parser_tests/negative/eq_instead_of_double_eq.cedar",
    testParseFail' "number_as_entity_type" "UnitTest/parser_tests/negative/number_as_entity_type.cedar",
    -- Semantic errors that Cedar rejects at parse time (our CST parser is more permissive)
    -- These are tested to document the difference; our parser accepts them at CST level
    testParseFileOk "neg/invalid_effect (semantic)"
      "UnitTest/parser_tests/negative/invalid_effect.cedar" 1,
    testParseFileOk "neg/missing_action (semantic)"
      "UnitTest/parser_tests/negative/missing_action.cedar" 1,
    testParseFileOk "neg/missing_resource (semantic)"
      "UnitTest/parser_tests/negative/missing_resource.cedar" 1,
    testParseFileOk "neg/missing_principal (semantic)"
      "UnitTest/parser_tests/negative/missing_principal.cedar" 1,
    testParseFileOk "neg/invalid_operator_div (semantic)"
      "UnitTest/parser_tests/negative/invalid_operator_div.cedar" 1,
    testParseFileOk "neg/invalid_operator_mod (semantic)"
      "UnitTest/parser_tests/negative/invalid_operator_mod.cedar" 1,
    testParseFileOk "neg/reserved_word_cedar (semantic)"
      "UnitTest/parser_tests/negative/reserved_word_cedar.cedar" 1,
    testParseFileOk "neg/invalid_slot_name (semantic)"
      "UnitTest/parser_tests/negative/invalid_slot_name.cedar" 1,
    testParseFileOk "neg/slot_in_condition (semantic)"
      "UnitTest/parser_tests/negative/slot_in_condition.cedar" 1,
    testParseFileOk "neg/empty_scope (semantic)"
      "UnitTest/parser_tests/negative/empty_scope.cedar" 1,
    testParseFileOk "neg/extra_scope_element (semantic)"
      "UnitTest/parser_tests/negative/extra_scope_element.cedar" 1,
    testParseFileOk "neg/invalid_has_number (semantic)"
      "UnitTest/parser_tests/negative/invalid_has_number.cedar" 1,
    testParseFileOk "neg/is_with_string (semantic)"
      "UnitTest/parser_tests/negative/is_with_string.cedar" 1,
    testParseFileOk "neg/invalid_method_syntax (semantic)"
      "UnitTest/parser_tests/negative/invalid_method_syntax.cedar" 1,
    testParseFail' "invalid_relop_single_eq" "UnitTest/parser_tests/negative/invalid_relop_single_eq.cedar"
  ]

def tests : List (TestSuite IO) :=
  [testsForBasicPolicies,
   testsForScopes,
   testsForConditions,
   testsForExpressions,
   testsForArithmetic,
   testsForComparisons,
   testsForRelations,
   testsForMemberAccess,
   testsForPrimary,
   testsForFiles]

end UnitTest.Parser
