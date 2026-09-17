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

/-!
### Systematic `extHasAttr` equivalence tests for chains of length 1–3

For every attribute chain `root has a₁. ... .aₙ` with `n ∈ {1, 2, 3}`, rooted at
both an entity (`principal`) and a record (`context`), we check the
extended-`has` form against its desugaring
`root has a₁ && root.a₁ has a₂ && ...` (`desugarExtHasAttr`), over all
alternations of:
- required vs. optional at every position, and
- for every *intermediate* position (all but the last), whether the attribute's
  value is a record or an entity — this decides whether the next step descends
  into a record type or into an entity's attribute record.

The root base (entity vs. record) is itself a dimension.

Counting chains per root: each of the `n-1` intermediate positions has 4 choices
(req/opt × record/entity) and the final leaf has 2 (req/opt):
- n = 1: 2 chains
- n = 2: 4 × 2 = 8 chains
- n = 3: 4 × 4 × 2 = 32 chains
→ 42 per root × 2 roots = 84 chains.

To keep the schema finite (record types cannot be self-referential) while making
the record-vs-entity choice independent at each step, we use one distinct entity
type and one distinct record type per *level*, each level carrying both the 4
container attributes and the 2 leaf attributes so a chain may terminate at any
depth. Container names encode (qualifier, value-kind): `rr`/`ro` =
required-record / required-entity, `or_`/`oo` = optional-record /
optional-entity. Leaves are `lreq` (required bool) and `lopt` (optional bool).
-/

namespace Chains

private def e1 : EntityType := ⟨"E1", []⟩
private def e2 : EntityType := ⟨"E2", []⟩

/-- Container attribute names used at any intermediate position. -/
def containers : List Attr := ["rr", "ro", "or_", "oo"]

/-- Leaf attribute names used at the final position. -/
def leaves : List Attr := ["lreq", "lopt"]

/-- A level record: containers descend into `recTy` (record-valued) or `entTy`
(entity-valued); the leaf attributes are bools. -/
private def levelRecord (recTy : CedarType) (entTy : EntityType) : RecordType :=
  Map.make [
    ("rr", .required recTy),
    ("ro", .required (.entity entTy)),
    ("or_", .optional recTy),
    ("oo", .optional (.entity entTy)),
    ("lreq", .required (.bool .anyBool)),
    ("lopt", .optional (.bool .anyBool)),
  ]

/-- Level 3: containers point at a trivial record (never descended past for
length ≤ 3 chains); leaves terminate length-3 chains. -/
private def level3Record : RecordType :=
  Map.make [
    ("rr", .required (.record (Map.make [("lreq", .required (.bool .anyBool))]))),
    ("ro", .required (.entity e2)),
    ("or_", .optional (.record (Map.make [("lreq", .required (.bool .anyBool))]))),
    ("oo", .optional (.entity e2)),
    ("lreq", .required (.bool .anyBool)),
    ("lopt", .optional (.bool .anyBool)),
  ]

/-- Level 2: containers descend into level 3 (`level3Record` or entity `E2`). -/
private def level2Record : RecordType := levelRecord (.record level3Record) e2

/-- Level 1 (root attrs): containers descend into level 2
(`level2Record` or entity `E1`). -/
private def level1Record : RecordType := levelRecord (.record level2Record) e1

def typeEnv : TypeEnv :=
  -- Principal (entity root) and the request context (record root) both carry
  -- `level1Record`, so a chain can be rooted at an entity (`principal`) or a
  -- record (`context`) and traverse the same structure.
  let base := BasicTypes.env level1Record Map.empty level1Record
  let ets : EntitySchema := Map.make [
    (⟨"Principal", []⟩, .standard ⟨Set.empty, level1Record, none⟩),
    (⟨"Resource", []⟩, .standard ⟨Set.empty, Map.empty, none⟩),
    (e1, .standard ⟨Set.empty, level2Record, none⟩),
    (e2, .standard ⟨Set.empty, level3Record, none⟩),
  ]
  { base with ets := ets }

/-- The two roots we test every chain from: an entity root and a record root. -/
def roots : List (String × Expr) := [("principal", .var .principal), ("context", .var .context)]

/-- All attribute paths of a given length: `len-1` intermediate containers
followed by one leaf. -/
def pathsOfLength : Nat → List (List Attr)
  | 0 => []
  | 1 => leaves.map ([·])
  | n+1 => containers.flatMap (fun c => (pathsOfLength n).map (c :: ·))

/-- All chains of length 1 through 3. -/
def allPaths : List (List Attr) :=
  pathsOfLength 1 ++ pathsOfLength 2 ++ pathsOfLength 3

/-- One equivalence test for a chain rooted at `root`: extended-`has` vs. its
desugaring. -/
def mkTest (rootName : String) (root : Expr) : List Attr → List (TestCase SolverM)
  | a :: rest =>
    testVerifyEquivalent
      s!"Equivalence: {rootName} has {String.intercalate "." (a :: rest)} matches desugared form"
      (.extHasAttr root a rest)
      (desugarExtHasAttr root (a :: rest))
      typeEnv .unsat
  | [] => []

end Chains

def testsForExtHasAttrChains :=
  suite "Has.extHasAttr.chains" $ List.flatten $
    Chains.roots.flatMap (fun (name, root) =>
      Chains.allPaths.map (Chains.mkTest name root))

/-!
### Singleton `extHasAttr` vs. plain `hasAttr`

The length-1 chain `x has a` (`.extHasAttr x a []`) must match plain
`.hasAttr x a`, for required/optional attributes over entity and record roots.
-/

private def singletonPrincipal : RecordType :=
  Map.make [
    ("preq", .required (.bool .anyBool)),
    ("popt", .optional (.bool .anyBool)),
  ]

private def singletonContext : RecordType :=
  Map.make [
    ("creq", .required (.bool .anyBool)),
    ("copt", .optional (.bool .anyBool)),
  ]

private def singletonEnv : TypeEnv :=
  BasicTypes.env singletonPrincipal Map.empty singletonContext

private def mkSingletonTest (root : Expr) (a : Attr) : List (TestCase SolverM) :=
  testVerifyEquivalent
    s!"Equivalence: singleton extended has `{a}` matches plain has"
    (.extHasAttr root a [])
    (.hasAttr root a)
    singletonEnv .unsat

def testsForExtHasAttrSingleton :=
  suite "Has.extHasAttr.singleton" $ List.flatten [
    mkSingletonTest (.var .principal) "preq",
    mkSingletonTest (.var .principal) "popt",
    mkSingletonTest (.var .context) "creq",
    mkSingletonTest (.var .context) "copt",
  ]

def tests := [
  testsForBasicHasOps,
  testsForExtHasAttr,
  testsForExtHasAttrChains,
  testsForExtHasAttrSingleton,
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.Has
