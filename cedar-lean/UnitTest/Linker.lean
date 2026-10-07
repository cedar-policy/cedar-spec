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

import Cedar.Validation.Linker
import UnitTest.Run

namespace UnitTest.Linker

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

deriving instance DecidableEq for ActionSchemaEntry
deriving instance DecidableEq for PartialEntitySchemaEntry
deriving instance DecidableEq for PartialActionSchemaEntry
deriving instance DecidableEq for PartialSchema

private def testSuccessfulLink
    (name : String)
    (p c expected : PartialSchema) : TestCase IO :=
  test name ⟨λ _ => checkEq (link p c) (.ok expected)⟩

private def testFailedLink
    (name : String)
    (p c : PartialSchema)
    (expected : LinkError) : TestCase IO :=
  test name ⟨λ _ => checkEq (link p c) (.error expected)⟩

private def testLinkErrorKind
    (name : String)
    (p c : PartialSchema)
    (error_match : LinkError → Bool) : TestCase IO :=
  test name ⟨λ _ => do
    match link p c with
    | .error error => checkMatches (error_match error) error
    | .ok result => return .error s!"link unexpectedly succeeded: {repr result}"⟩

private def A : EntityType := ⟨"A", []⟩
private def B : EntityType := ⟨"B", []⟩
private def D : EntityType := ⟨"D", []⟩
private def E : EntityType := ⟨"E", []⟩
private def F : EntityType := ⟨"F", []⟩
private def G : EntityType := ⟨"G", []⟩
private def H : EntityType := ⟨"H", []⟩
private def X : EntityType := ⟨"X", []⟩
private def User : EntityType := ⟨"User", []⟩
private def Doc : EntityType := ⟨"Doc", []⟩
private def ActionType : EntityType := ⟨"Action", []⟩

private def actionA : EntityUID := ⟨ActionType, "a"⟩
private def actionG : EntityUID := ⟨ActionType, "g"⟩
private def actionR : EntityUID := ⟨ActionType, "r"⟩
private def actionW : EntityUID := ⟨ActionType, "w"⟩
private def actionWrite : EntityUID := ⟨ActionType, "write"⟩

/-!
### Examples 1–7: successful links

```cedar
// 1, P
external entity B;
entity A { b: B };
// 1, C
entity B;

// 2, P
entity User;
entity Doc;
external action write;
// 2, C
external entity User;
external entity Doc;
action write appliesTo { principal: User, resource: Doc };

// 3, P
external entity B;
entity A { b: B };
// 3, C
external entity B;
entity D { b: B };

// 4, P
external entity B;
entity A { b: B };
// 4, C
external entity A;
entity B { a: A };

// 5, P
external entity G;
external entity F in G;
entity A in F;
// 5, C
entity G;
entity F in G;

// 6, P
external entity G;
external entity F in G;
// 6, C
external entity H;
external entity F in H;

// 7, P
external entity G;
external entity F in G;
// 7, C
entity G;
entity H;
entity F in [G, H];
```

The Lean literals contain the transitively closed ancestor sets produced from
this Cedar source.
-/

private def example1P : PartialSchema := ⟨
  Map.make [
    (B, .external Set.empty),
    (A, .defined (.standard ⟨
      Set.empty,
      Map.make [("b", .required (.entity B))],
      none
    ⟩))
  ],
  Map.empty
⟩

private def example1C : PartialSchema := ⟨
  Map.make [(B, .defined (.standard ⟨Set.empty, Map.empty, none⟩))],
  Map.empty
⟩

private def example1Expected : PartialSchema := ⟨
  Map.make [
    (A, .defined (.standard ⟨
      Set.empty,
      Map.make [("b", .required (.entity B))],
      none
    ⟩)),
    (B, .defined (.standard ⟨Set.empty, Map.empty, none⟩))
  ],
  Map.empty
⟩

private def example2P : PartialSchema := ⟨
  Map.make [
    (User, .defined (.standard ⟨Set.empty, Map.empty, none⟩)),
    (Doc, .defined (.standard ⟨Set.empty, Map.empty, none⟩))
  ],
  Map.make [(actionWrite, .external Set.empty)]
⟩

private def example2C : PartialSchema := ⟨
  Map.make [(User, .external Set.empty), (Doc, .external Set.empty)],
  Map.make [(actionWrite, .defined ⟨
    Set.singleton User,
    Set.singleton Doc,
    Set.empty,
    Map.empty
  ⟩)]
⟩

private def example2Expected : PartialSchema := ⟨
  Map.make [
    (User, .defined (.standard ⟨Set.empty, Map.empty, none⟩)),
    (Doc, .defined (.standard ⟨Set.empty, Map.empty, none⟩))
  ],
  Map.make [(actionWrite, .defined ⟨
    Set.singleton User,
    Set.singleton Doc,
    Set.empty,
    Map.empty
  ⟩)]
⟩

private def example3P : PartialSchema := example1P

private def example3C : PartialSchema := ⟨
  Map.make [
    (B, .external Set.empty),
    (D, .defined (.standard ⟨
      Set.empty,
      Map.make [("b", .required (.entity B))],
      none
    ⟩))
  ],
  Map.empty
⟩

private def example3Expected : PartialSchema := ⟨
  Map.make [
    (A, .defined (.standard ⟨
      Set.empty,
      Map.make [("b", .required (.entity B))],
      none
    ⟩)),
    (B, .external Set.empty),
    (D, .defined (.standard ⟨
      Set.empty,
      Map.make [("b", .required (.entity B))],
      none
    ⟩))
  ],
  Map.empty
⟩

private def example4P : PartialSchema := example1P

private def example4C : PartialSchema := ⟨
  Map.make [
    (A, .external Set.empty),
    (B, .defined (.standard ⟨
      Set.empty,
      Map.make [("a", .required (.entity A))],
      none
    ⟩))
  ],
  Map.empty
⟩

private def example4Expected : PartialSchema := ⟨
  Map.make [
    (A, .defined (.standard ⟨
      Set.empty,
      Map.make [("b", .required (.entity B))],
      none
    ⟩)),
    (B, .defined (.standard ⟨
      Set.empty,
      Map.make [("a", .required (.entity A))],
      none
    ⟩))
  ],
  Map.empty
⟩

private def example5P : PartialSchema := ⟨
  Map.make [
    (G, .external Set.empty),
    (F, .external (Set.singleton G)),
    (A, .defined (.standard ⟨Set.make [F, G], Map.empty, none⟩))
  ],
  Map.empty
⟩

private def example5C : PartialSchema := ⟨
  Map.make [
    (G, .defined (.standard ⟨Set.empty, Map.empty, none⟩)),
    (F, .defined (.standard ⟨Set.singleton G, Map.empty, none⟩))
  ],
  Map.empty
⟩

private def example5Expected : PartialSchema := ⟨
  Map.make [
    (A, .defined (.standard ⟨Set.make [F, G], Map.empty, none⟩)),
    (F, .defined (.standard ⟨Set.singleton G, Map.empty, none⟩)),
    (G, .defined (.standard ⟨Set.empty, Map.empty, none⟩))
  ],
  Map.empty
⟩

private def example6P : PartialSchema := ⟨
  Map.make [(G, .external Set.empty), (F, .external (Set.singleton G))],
  Map.empty
⟩

private def example6C : PartialSchema := ⟨
  Map.make [(H, .external Set.empty), (F, .external (Set.singleton H))],
  Map.empty
⟩

private def example6Expected : PartialSchema := ⟨
  Map.make [
    (F, .external (Set.make [G, H])),
    (G, .external Set.empty),
    (H, .external Set.empty)
  ],
  Map.empty
⟩

private def example7P : PartialSchema := example6P

private def example7C : PartialSchema := ⟨
  Map.make [
    (G, .defined (.standard ⟨Set.empty, Map.empty, none⟩)),
    (H, .defined (.standard ⟨Set.empty, Map.empty, none⟩)),
    (F, .defined (.standard ⟨Set.make [G, H], Map.empty, none⟩))
  ],
  Map.empty
⟩

private def example7Expected : PartialSchema := example7C

/-!
### Examples 8–15: closed-ancestor behavior and errors

```cedar
// 8, P
external entity B;
entity A in B;
// 8, C
external entity A;
entity B in A;

// 9, P
external entity G;
external entity F in G;
// 9, C
entity G;
entity X in G;
entity F in X;

// 10, P
external action g;
external action w in g;
// 10, C
action g;
action r;
action w in [g, r];

// 11, P
external entity E;
entity A { e: E };
// 11, C
entity E enum ["x"];

// 12, P and C
entity A;

// 13, P
external entity X;
entity E in X;
// 13, C
external entity G;
external entity E in G;

// 14, P
external entity X;
entity E in X;
// 14, C
external entity G;
external entity X in G;

// 15, P
external entity X;
external entity E in X;
// 15, C
external entity G;
external entity X in G;
```
-/

private def example8P : PartialSchema := ⟨
  Map.make [
    (B, .external Set.empty),
    (A, .defined (.standard ⟨Set.singleton B, Map.empty, none⟩))
  ],
  Map.empty
⟩

private def example8C : PartialSchema := ⟨
  Map.make [
    (A, .external Set.empty),
    (B, .defined (.standard ⟨Set.singleton A, Map.empty, none⟩))
  ],
  Map.empty
⟩

private def example9P : PartialSchema := example6P

private def example9C : PartialSchema := ⟨
  Map.make [
    (G, .defined (.standard ⟨Set.empty, Map.empty, none⟩)),
    (X, .defined (.standard ⟨Set.singleton G, Map.empty, none⟩)),
    (F, .defined (.standard ⟨Set.make [X, G], Map.empty, none⟩))
  ],
  Map.empty
⟩

private def example9Expected : PartialSchema := example9C

private def example10P : PartialSchema := ⟨
  Map.empty,
  Map.make [
    (actionG, .external Set.empty),
    (actionW, .external (Set.singleton actionG))
  ]
⟩

private def example10C : PartialSchema := ⟨
  Map.empty,
  Map.make [
    (actionG, .defined ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩),
    (actionR, .defined ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩),
    (actionW, .defined ⟨Set.empty, Set.empty, Set.make [actionG, actionR], Map.empty⟩)
  ]
⟩

private def example11P : PartialSchema := ⟨
  Map.make [
    (E, .external Set.empty),
    (A, .defined (.standard ⟨
      Set.empty,
      Map.make [("e", .required (.entity E))],
      none
    ⟩))
  ],
  Map.empty
⟩

private def example11C : PartialSchema := ⟨
  Map.make [(E, .defined (.enum (Set.singleton "x")))],
  Map.empty
⟩

private def example12P : PartialSchema := ⟨
  Map.make [(A, .defined (.standard ⟨Set.empty, Map.empty, none⟩))],
  Map.empty
⟩

private def example12C : PartialSchema := example12P

private def example13P : PartialSchema := ⟨
  Map.make [
    (X, .external Set.empty),
    (E, .defined (.standard ⟨Set.singleton X, Map.empty, none⟩))
  ],
  Map.empty
⟩

private def example13C : PartialSchema := ⟨
  Map.make [(G, .external Set.empty), (E, .external (Set.singleton G))],
  Map.empty
⟩

private def example14P : PartialSchema := example13P

private def example14C : PartialSchema := ⟨
  Map.make [(G, .external Set.empty), (X, .external (Set.singleton G))],
  Map.empty
⟩

private def example15P : PartialSchema := ⟨
  Map.make [(X, .external Set.empty), (E, .external (Set.singleton X))],
  Map.empty
⟩

private def example15C : PartialSchema := example14C

private def example15Expected : PartialSchema := ⟨
  Map.make [
    (E, .external (Set.make [X, G])),
    (G, .external Set.empty),
    (X, .external (Set.singleton G))
  ],
  Map.empty
⟩

private def matchingActionDefinition : PartialSchema := ⟨
  Map.empty,
  Map.make [
    (actionG, .defined ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩),
    (actionW, .defined ⟨Set.empty, Set.empty, Set.singleton actionG, Map.empty⟩)
  ]
⟩

private def isDefinedEntityAncestorsChanged : LinkError → Bool
  | .definedEntityAncestorsChanged _ => true
  | _ => false

def successfulLinkTests : TestSuite IO :=
  suite "Successful schema linking"
  [
    testSuccessfulLink "example 1: an entity definition replaces an external"
      example1P example1C example1Expected,
    testSuccessfulLink "example 2: an action definition supplies appliesTo"
      example2P example2C example2Expected,
    testSuccessfulLink "example 3: an unresolved external remains external"
      example3P example3C example3Expected,
    testSuccessfulLink "example 4: mutual externals resolve"
      example4P example4C example4Expected,
    testSuccessfulLink "example 5: a definition preserves closed ancestors through an external"
      example5P example5C example5Expected,
    testSuccessfulLink "example 6: repeated external ancestors are combined"
      example6P example6C example6Expected,
    testSuccessfulLink "example 7: an entity definition may contain more closed ancestors"
      example7P example7C example7Expected,
    testSuccessfulLink "example 9: a transitive ancestor satisfies an external declaration"
      example9P example9C example9Expected,
    testSuccessfulLink "example 15: an external entity's closed ancestors may grow"
      example15P example15C example15Expected,
    testSuccessfulLink "matching external action ancestors link to a definition"
      example10P matchingActionDefinition matchingActionDefinition,
    testSuccessfulLink "matching repeated external action declarations are preserved"
      example10P example10P example10P
  ]

def rejectedLinkTests : TestSuite IO :=
  suite "Rejected schema linking"
  [
    testLinkErrorKind "example 8: a cross-schema cycle would enlarge defined ancestors"
      example8P example8C isDefinedEntityAncestorsChanged,
    testFailedLink "example 10: action ancestors must match exactly"
      example10P example10C (.externalActionParentsMismatch actionW),
    testFailedLink "repeated external action declarations must agree exactly"
      example10P
      ⟨Map.empty, Map.make [
        (actionG, .external Set.empty),
        (actionW, .external Set.empty)
      ]⟩
      (.externalActionParentsMismatch actionW),
    testFailedLink "example 11: an external entity cannot resolve to an enum"
      example11P example11C (.externalIsEnum E),
    testFailedLink "example 12: duplicate entity definitions are rejected"
      example12P example12C (.duplicateEntityType A),
    testFailedLink "duplicate action definitions are rejected"
      ⟨Map.empty, Map.make [(actionA, .defined ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩)]⟩
      ⟨Map.empty, Map.make [(actionA, .defined ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩)]⟩
      (.duplicateAction actionA),
    testFailedLink "linking cannot declare an action's entity type as an entity type"
      ⟨Map.make [(ActionType, .defined (.standard ⟨Set.empty, Map.empty, none⟩))], Map.empty⟩
      ⟨Map.empty, Map.make [(actionA, .defined ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩)]⟩
      (.actionEntityTypeDeclared ActionType),
    testFailedLink "example 13: an external cannot add an ancestor to a definition"
      example13P example13C (.externalAncestorsNotInDefinition E),
    testFailedLink "example 14: linking cannot enlarge a defined entity's ancestors"
      example14P example14C (.definedEntityAncestorsChanged E),
    testFailedLink "linking cannot make a new ancestor valid for a defined entity"
      ⟨Map.make [
        (B, .external Set.empty),
        (D, .external Set.empty),
        (A, .defined (.standard ⟨Set.singleton B, Map.empty, none⟩))
      ], Map.empty⟩
      ⟨Map.make [
        (D, .defined (.standard ⟨Set.empty, Map.empty, none⟩)),
        (B, .defined (.standard ⟨Set.singleton D, Map.empty, none⟩))
      ], Map.empty⟩
      (.definedEntityAncestorsChanged A)
  ]

private def associativeLink
    (p c d : PartialSchema) : Except LinkError PartialSchema := do
  let pc ← link p c
  link pc d

private def rightAssociatedLink
    (p c d : PartialSchema) : Except LinkError PartialSchema := do
  let cd ← link c d
  link p cd

def linkingLawTests : TestSuite IO :=
  suite "Schema linking laws"
  [
    test "linking is commutative for well-formed successful inputs" ⟨λ _ =>
      checkEq (link example6P example6C) (link example6C example6P)⟩,
    test "linking is associative for well-formed successful inputs" ⟨λ _ =>
      checkEq
        (associativeLink example6P example6C example7C)
        (rightAssociatedLink example6P example6C example7C)⟩
  ]

def tests := [successfulLinkTests, rejectedLinkTests, linkingLawTests]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.Linker
