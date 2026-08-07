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

/-! This file unit tests symbolic compilation of the `has` operator. -/

namespace SymTest.Has

open Cedar Data Spec SymCC Validation
open UnitTest

private def childRecord : RecordType :=
  Map.make [
    ("leaf", .optional (.bool .anyBool)),
  ]

private def hasContext : RecordType :=
  Map.make [
    ("a", .optional (.bool .anyBool)),
    ("x", .required (.bool .anyBool)),
    ("child", .optional (.record childRecord)),
  ]

private def hasTypeEnv := BasicTypes.env Map.empty Map.empty hasContext

private def getₐ : Expr := .getAttr (.var .context) "a"
private def getₓ : Expr := .getAttr (.var .context) "x"

private def hasₐ : Expr := .hasAttr (.var .context) "a"
private def hasₓ : Expr := .hasAttr (.var .context) "x"

private def extHasOptionalLeaf : Expr :=
  .extHasAttr (.var .context) "child" ["leaf"]

private def desugaredExtHasOptionalLeaf : Expr :=
  .and
    (.hasAttr (.var .context) "child")
    (.hasAttr (.getAttr (.var .context) "child") "leaf")

private def extHasMissingIntermediate : Expr :=
  .extHasAttr (.var .context) "child" ["missing", "leaf"]

private def extHasMissingLast : Expr :=
  .extHasAttr (.var .context) "child" ["missing"]

def testsForBasicHasOps :=
  suite "Has.basic" $ List.flatten
  [
    testVerifyEquivalent "True: context has x"
      hasₓ
      (.lit (.bool true))
      hasTypeEnv .unsat,

    [testFailsCompilePolicy "Error: context.a" getₐ hasTypeEnv],
    [testFailsCompilePolicies "Error: context.a" getₐ hasTypeEnv],

    testVerifyNoError "Okay: context has a && context.a"
      (.and hasₐ getₐ)
      hasTypeEnv .unsat,

    -- this policy never errors at runtime, but our current validator is not
    -- powerful enough to validate this policy.
    -- however, if you were to feed this policy directly to the symbolic
    -- compiler (that is, if compilation did not require typechecking first --
    -- see also the notes in SymTest/WellTyped.lean), the symbolic compiler
    -- would correctly handle this policy and `testVerifyNoError` would confirm
    -- it never errors
    [testFailsCompilePolicy "Error: !(!(context has a)) && context.a"
      (.and (.unaryApp .not (.unaryApp .not hasₐ)) getₐ)
      hasTypeEnv],

    -- this policy never errors at runtime, but our current validator is not
    -- powerful enough to validate this policy.
    -- however, if you were to feed this policy directly to the symbolic
    -- compiler (that is, if compilation did not require typechecking first --
    -- see also the notes in SymTest/WellTyped.lean), the symbolic compiler
    -- would correctly handle this policy and `testVerifyNoError` would confirm
    -- it never errors
    [testFailsCompilePolicy "Error: !(context has a) || context.a"
      (.or (.unaryApp .not hasₐ) getₐ)
      hasTypeEnv],

    -- this policy never errors at runtime, but our current validator is not
    -- powerful enough to validate this policy.
    -- however, if you were to feed this policy directly to the symbolic
    -- compiler (that is, if compilation did not require typechecking first --
    -- see also the notes in SymTest/WellTyped.lean), the symbolic compiler
    -- would correctly handle this policy and `testVerifyEquivalent` would give
    -- the Equivalent result
    [testFailsCompilePolicy "Error: (context.x == context has a) && (context.x && context.a)"
      (.and (.binaryApp .eq getₓ hasₐ) (.and getₓ getₐ))
      -- would be equivalent to: (.and getₐ (.and hasₐ getₐ))
      hasTypeEnv],
  ]

private def entityRootAttrs : RecordType :=
  Map.make [
    ("child", .optional (.record childRecord)),
  ]

private def entityRootTypeEnv :=
  BasicTypes.env entityRootAttrs Map.empty Map.empty

private def extHasEntityOptionalLeaf : Expr :=
  .extHasAttr (.var .principal) "child" ["leaf"]

private def desugaredExtHasEntityOptionalLeaf : Expr :=
  .and
    (.hasAttr (.var .principal) "child")
    (.hasAttr (.getAttr (.var .principal) "child") "leaf")

-- simulates the desugared form of exnteded has
private def desugarExtHasAttr (x : Expr) : List Attr → Expr
  | [] => .lit (.bool true)
  | [a] => .hasAttr x a
  | a :: b :: rest =>
    .and
      (.hasAttr x a)
      (desugarExtHasAttr (.getAttr x a) (b :: rest))

private def mixedResourceType : EntityType := ⟨"Resource", []⟩

private def mixedRecord : RecordType :=
  Map.make [
    ("owner", .optional (.entity mixedResourceType)),
    ("label", .required .string),
  ]

private def mixedPrincipalAttrs : RecordType :=
  Map.make [
    ("profile", .optional (.record mixedRecord)),
    ("name", .required .string),
  ]

private def mixedResourceAttrs : RecordType :=
  Map.make [
    ("enabled", .optional (.bool .anyBool)),
    ("metadata", .required (.record childRecord)),
  ]

private def mixedContext : RecordType :=
  Map.make [
    ("owner", .optional (.entity mixedResourceType)),
    ("profile", .required (.record mixedRecord)),
    ("flag", .required (.bool .anyBool)),
  ]

private def mixedTypeEnv :=
  BasicTypes.env mixedPrincipalAttrs mixedResourceAttrs mixedContext

private def extHasEntityRecordEntity : Expr :=
  .extHasAttr (.var .principal) "profile" ["owner", "enabled"]

private def desugaredExtHasEntityRecordEntity : Expr :=
  desugarExtHasAttr (.var .principal) ["profile", "owner", "enabled"]

private def extHasRecordEntity : Expr :=
  .extHasAttr (.var .context) "owner" ["enabled"]

private def desugaredExtHasRecordEntity : Expr :=
  desugarExtHasAttr (.var .context) ["owner", "enabled"]

private def extHasMissingMiddleMixed : Expr :=
  .extHasAttr (.var .context) "profile" ["missing", "enabled"]

private def desugaredExtHasMissingMiddleMixed : Expr :=
  desugarExtHasAttr (.var .context) ["profile", "missing", "enabled"]

def testsForExtHasAttr :=
  suite "Has.extHasAttr" $ List.flatten
  [
    testVerifyEquivalent "Equivalence: extended has optional record-root intermediate matches desugared form"
      extHasOptionalLeaf
      desugaredExtHasOptionalLeaf
      hasTypeEnv .unsat,

    testVerifyEquivalent "Equivalence: extended has optional entity-root intermediate matches desugared form"
      extHasEntityOptionalLeaf
      desugaredExtHasEntityOptionalLeaf
      entityRootTypeEnv .unsat,

    testVerifyEquivalent "Equivalence: extended has entity-record-entity chain matches desugared form"
      extHasEntityRecordEntity
      desugaredExtHasEntityRecordEntity
      mixedTypeEnv .unsat,

    testVerifyEquivalent "Equivalence: extended has record-entity chain matches desugared form"
      extHasRecordEntity
      desugaredExtHasRecordEntity
      mixedTypeEnv .unsat,

    testVerifyEquivalent "Equivalence: extended has missing middle matches desugared form"
      extHasMissingMiddleMixed
      desugaredExtHasMissingMiddleMixed
      mixedTypeEnv .unsat,

    testVerifyEquivalent "Equivalence: extended has missing intermediate is false"
      extHasMissingIntermediate
      (.lit (.bool false))
      hasTypeEnv .unsat,

    testVerifyEquivalent "Equivalence: extended has missing last is false"
      extHasMissingLast
      (.lit (.bool false))
      hasTypeEnv .unsat,
  ]

def tests := [
  testsForBasicHasOps,
  testsForExtHasAttr,
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.Has
