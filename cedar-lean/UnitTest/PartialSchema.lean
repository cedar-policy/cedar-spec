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

import Cedar.Validation.PartialRequestEntityValidator
import Cedar.Validation.PartialSchema
import UnitTest.Run

namespace UnitTest.PartialSchema

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

deriving instance DecidableEq for ActionSchemaEntry
deriving instance DecidableEq for Schema

private def validationSucceeded {ε} : Except ε Unit → Bool
  | .ok () => true
  | .error _ => false

private def testEntityValidation
    (name : String)
    (schema : PartialSchema)
    (entities : Entities)
    (expected : Bool) : TestCase IO :=
  test name ⟨λ _ =>
    checkEq (validationSucceeded (schema.validateEntities entities)) expected⟩

private def testRequestValidation
    (name : String)
    (schema : PartialSchema)
    (request : Request)
    (expected : Bool) : TestCase IO :=
  test name ⟨λ _ =>
    checkEq (validationSucceeded (schema.validateRequest request)) expected⟩

private def A : EntityType := ⟨"A", []⟩
private def B : EntityType := ⟨"B", []⟩
private def C : EntityType := ⟨"C", []⟩
private def D : EntityType := ⟨"D", []⟩
private def R : EntityType := ⟨"R", []⟩
private def ActionType : EntityType := ⟨"Action", []⟩

private def actionAct : EntityUID := ⟨ActionType, "act"⟩
private def actionG : EntityUID := ⟨ActionType, "g"⟩
private def actionW : EntityUID := ⟨ActionType, "w"⟩
private def actionX : EntityUID := ⟨ActionType, "x"⟩
private def missingAction : EntityUID := ⟨ActionType, "missing"⟩

private def aEntity : EntityUID := ⟨A, "a"⟩
private def bEntity : EntityUID := ⟨B, "x"⟩
private def bParent : EntityUID := ⟨B, "y"⟩
private def bOwner : EntityUID := ⟨B, "owner"⟩
private def bReviewer : EntityUID := ⟨B, "reviewer"⟩
private def dParent : EntityUID := ⟨D, "d"⟩
private def dReviewer : EntityUID := ⟨D, "reviewer"⟩
private def rEntity : EntityUID := ⟨R, "r"⟩

/-!
```cedar
external entity B;
external entity D;
entity A in B { b: B } tags B;
entity R { act: Action };
external action g;
external action w in g;
external action x in w;
action act in g appliesTo {
  principal: B,
  resource: A,
  context: {
    reviewer?: B,
    delegate?: Action,
  },
};
```
-/
private def validationSchema : PartialSchema := ⟨
  Map.make [
    (B, .external Set.empty),
    (D, .external Set.empty),
    (A, .defined (.standard ⟨
      Set.singleton B,
      Map.make [("b", .required (.entity B))],
      some (.entity B)
    ⟩)),
    (R, .defined (.standard ⟨
      Set.empty,
      Map.make [("act", .required (.entity ActionType))],
      none
    ⟩))
  ],
  Map.make [
    (actionG, .external Set.empty),
    (actionW, .external (Set.singleton actionG)),
    (actionX, .external (Set.make [actionW, actionG])),
    (actionAct, .defined ⟨
      Set.singleton B,
      Set.singleton A,
      Set.singleton actionG,
      Map.make [
        ("reviewer", .optional (.entity B)),
        ("delegate", .optional (.entity ActionType))
      ]
    ⟩)
  ]
⟩

/-!
```cedar
external action g;
external action w in g;
external action x in w;
```
-/
private def validationSchemaWithoutDefinedAction : PartialSchema := ⟨
  validationSchema.ets,
  Map.make [
    (actionG, .external Set.empty),
    (actionW, .external (Set.singleton actionG)),
    (actionX, .external (Set.make [actionW, actionG]))
  ]
⟩

/-!
A complete partial schema used to test `isComplete`, `asSchema?`, and the
complete-schema bridge:

```cedar
entity C;
entity B in C;
entity A in B { b: B } tags B;
entity R { act: Action };
action g;
action w in g;
action x in w;
action act in g appliesTo {
  principal: B,
  resource: A,
  context: {
    reviewer?: B,
    delegate?: Action,
  },
};
```

The Lean literal stores the closed ancestors `{B, C}` for `A` and `{w, g}` for
`x`.
-/
private def completePartialSchema : PartialSchema := ⟨
  Map.make [
    (A, .defined (.standard ⟨
      Set.make [B, C],
      Map.make [("b", .required (.entity B))],
      some (.entity B)
    ⟩)),
    (B, .defined (.standard ⟨Set.singleton C, Map.empty, none⟩)),
    (C, .defined (.standard ⟨Set.empty, Map.empty, none⟩)),
    (R, .defined (.standard ⟨
      Set.empty,
      Map.make [("act", .required (.entity ActionType))],
      none
    ⟩))
  ],
  Map.make [
    (actionG, .defined ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩),
    (actionW, .defined ⟨Set.empty, Set.empty, Set.singleton actionG, Map.empty⟩),
    (actionX, .defined ⟨Set.empty, Set.empty, Set.make [actionW, actionG], Map.empty⟩),
    (actionAct, .defined ⟨
      Set.singleton B,
      Set.singleton A,
      Set.singleton actionG,
      Map.make [
        ("reviewer", .optional (.entity B)),
        ("delegate", .optional (.entity ActionType))
      ]
    ⟩)
  ]
⟩

/-!
The same Cedar schema as `completePartialSchema`, represented directly as a
`Schema`. It is the expected result of converting `completePartialSchema`, and
converting it to `PartialSchema` and back should return this value unchanged.
-/
private def completeSchema : Schema := ⟨
  Map.make [
    (A, .standard ⟨
      Set.make [B, C],
      Map.make [("b", .required (.entity B))],
      some (.entity B)
    ⟩),
    (B, .standard ⟨Set.singleton C, Map.empty, none⟩),
    (C, .standard ⟨Set.empty, Map.empty, none⟩),
    (R, .standard ⟨
      Set.empty,
      Map.make [("act", .required (.entity ActionType))],
      none
    ⟩)
  ],
  Map.make [
    (actionG, ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩),
    (actionW, ⟨Set.empty, Set.empty, Set.singleton actionG, Map.empty⟩),
    (actionX, ⟨Set.empty, Set.empty, Set.make [actionW, actionG], Map.empty⟩),
    (actionAct, ⟨
      Set.singleton B,
      Set.singleton A,
      Set.singleton actionG,
      Map.make [
        ("reviewer", .optional (.entity B)),
        ("delegate", .optional (.entity ActionType))
      ]
    ⟩)
  ]
⟩

/-!
The validation view expected for `validationSchema`. Every external entity and
action becomes an empty definition while retaining its closed ancestors:

```cedar
entity B;
entity D;
entity A in B { b: B } tags B;
entity R { act: Action };
action g;
action w in g;
action x in w;
action act in g appliesTo {
  principal: B,
  resource: A,
  context: {
    reviewer?: B,
    delegate?: Action,
  },
};
```

The Lean literal records `x`'s closed ancestors as both `w` and `g`.
-/
private def validationViewExpected : Schema := ⟨
  Map.make [
    (B, .standard ⟨Set.empty, Map.empty, none⟩),
    (D, .standard ⟨Set.empty, Map.empty, none⟩),
    (A, .standard ⟨
      Set.singleton B,
      Map.make [("b", .required (.entity B))],
      some (.entity B)
    ⟩),
    (R, .standard ⟨
      Set.empty,
      Map.make [("act", .required (.entity ActionType))],
      none
    ⟩)
  ],
  Map.make [
    (actionG, ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩),
    (actionW, ⟨Set.empty, Set.empty, Set.singleton actionG, Map.empty⟩),
    (actionX, ⟨Set.empty, Set.empty, Set.make [actionW, actionG], Map.empty⟩),
    (actionAct, ⟨
      Set.singleton B,
      Set.singleton A,
      Set.singleton actionG,
      Map.make [
        ("reviewer", .optional (.entity B)),
        ("delegate", .optional (.entity ActionType))
      ]
    ⟩)
  ]
⟩

/-! ### Partial-schema entries, completeness, and conversion -/

def entryTests : TestSuite IO :=
  suite "Partial schema entries"
  [
    test "an external entity has unknown attributes" ⟨λ _ =>
      let entry : PartialEntitySchemaEntry := .external (Set.singleton B)
      checkEq entry.attrs? none⟩,
    test "an external entity has unknown tags" ⟨λ _ =>
      let entry : PartialEntitySchemaEntry := .external (Set.singleton B)
      checkEq entry.tags? none⟩,
    test "an external entity preserves its closed ancestors" ⟨λ _ =>
      let entry : PartialEntitySchemaEntry := .external (Set.make [B, C])
      checkEq entry.ancestors (Set.make [B, C])⟩,
    test "an external action preserves its closed ancestors" ⟨λ _ =>
      let entry : PartialActionSchemaEntry := .external (Set.make [actionW, actionG])
      checkEq entry.ancestors (Set.make [actionW, actionG])⟩
  ]

def completenessTests : TestSuite IO :=
  suite "PartialSchema completeness and conversion"
  [
    test "a schema containing only definitions is complete" ⟨λ _ =>
      checkEq completePartialSchema.isComplete true⟩,
    test "an external entity makes a schema incomplete" ⟨λ _ =>
      let schema : PartialSchema :=
        ⟨Map.make [(A, .external Set.empty)], Map.empty⟩
      checkEq schema.isComplete false⟩,
    test "an external action makes a schema incomplete" ⟨λ _ =>
      let schema : PartialSchema :=
        ⟨Map.empty, Map.make [(actionG, .external Set.empty)]⟩
      checkEq schema.isComplete false⟩,
    test "a complete partial schema converts without changing closed ancestors" ⟨λ _ =>
      checkEq completePartialSchema.asSchema? (some completeSchema)⟩,
    test "an unresolved external entity prevents conversion" ⟨λ _ =>
      let schema : PartialSchema :=
        ⟨Map.make [(A, .external Set.empty)], Map.empty⟩
      checkEq schema.asSchema? none⟩,
    test "an unresolved external action prevents conversion" ⟨λ _ =>
      let schema : PartialSchema :=
        ⟨Map.empty, Map.make [(actionG, .external Set.empty)]⟩
      checkEq schema.asSchema? none⟩,
    test "Schema conversion round-trips" ⟨λ _ =>
      checkEq completeSchema.toPartialSchema.asSchema? (some completeSchema)⟩
  ]

def validationViewTests : TestSuite IO :=
  suite "PartialSchema validation view"
  [
    test "the validation view replaces externals with empty definitions" ⟨λ _ =>
      checkEq validationSchema.validationView validationViewExpected⟩,
    test "a complete schema's validation view is unchanged" ⟨λ _ =>
      checkEq completePartialSchema.validationView completeSchema⟩,
    test "Schema.toPartialSchema has the original schema as its validation view" ⟨λ _ =>
      checkEq completeSchema.toPartialSchema.validationView completeSchema⟩
  ]

/-! ### Entity validation examples -/

def entityValidationTests : TestSuite IO :=
  suite "PartialSchema entity validation"
  [
    testEntityValidation "an empty entity store is valid"
      validationSchema
      Map.empty
      true,
    testEntityValidation "a defined entity may refer to an external entity in an attribute"
      validationSchema
      (Map.make [(aEntity, ⟨
        Map.make [("b", .prim (.entityUID bEntity))],
        Set.empty,
        Map.empty
      ⟩)])
      true,
    testEntityValidation "a tag may refer to an external entity type"
      validationSchema
      (Map.make [(aEntity, ⟨
        Map.make [("b", .prim (.entityUID bEntity))],
        Set.empty,
        Map.make [("owner", .prim (.entityUID bOwner))]
      ⟩)])
      true,
    testEntityValidation "a defined entity may have an ancestor of an external type"
      validationSchema
      (Map.make [(aEntity, ⟨
        Map.make [("b", .prim (.entityUID bEntity))],
        Set.singleton bParent,
        Map.empty
      ⟩)])
      true,
    testEntityValidation "a declared external type is not automatically an allowed ancestor"
      validationSchema
      (Map.make [(aEntity, ⟨
        Map.make [("b", .prim (.entityUID bEntity))],
        Set.singleton dParent,
        Map.empty
      ⟩)])
      false,
    testEntityValidation "an instance of an external entity type cannot be validated"
      validationSchema
      (Map.make [(bEntity, ⟨Map.empty, Set.empty, Map.empty⟩)])
      false,
    testEntityValidation "an entity attribute may contain a declared external action UID"
      validationSchema
      (Map.make [(rEntity, ⟨
        Map.make [("act", .prim (.entityUID actionG))],
        Set.empty,
        Map.empty
      ⟩)])
      true,
    testEntityValidation "an action-valued attribute requires an exact declared action UID"
      validationSchema
      (Map.make [(rEntity, ⟨
        Map.make [("act", .prim (.entityUID missingAction))],
        Set.empty,
        Map.empty
      ⟩)])
      false,
    testEntityValidation "a defined action entity may have an external action ancestor"
      validationSchema
      (Map.make [(actionAct, ⟨Map.empty, Set.singleton actionG, Map.empty⟩)])
      true,
    testEntityValidation "an external action with no ancestors is valid"
      validationSchema
      (Map.make [(actionG, ⟨Map.empty, Set.empty, Map.empty⟩)])
      true,
    testEntityValidation "an external action with its exact ancestors is valid"
      validationSchema
      (Map.make [(actionW, ⟨Map.empty, Set.singleton actionG, Map.empty⟩)])
      true,
    testEntityValidation "an external action with a missing ancestor is invalid"
      validationSchema
      (Map.make [(actionW, ⟨Map.empty, Set.empty, Map.empty⟩)])
      false,
    testEntityValidation "an external action includes all transitive ancestors"
      validationSchema
      (Map.make [(actionX, ⟨Map.empty, Set.make [actionW, actionG], Map.empty⟩)])
      true,
    testEntityValidation "an external action cannot omit a transitive ancestor"
      validationSchema
      (Map.make [(actionX, ⟨Map.empty, Set.singleton actionW, Map.empty⟩)])
      false,
    testEntityValidation "an action entity cannot have attributes"
      validationSchema
      (Map.make [(actionG, ⟨
        Map.make [("x", .prim (.int 1))],
        Set.empty,
        Map.empty
      ⟩)])
      false,
    testEntityValidation "entity validation still checks stores with no request environments"
      validationSchemaWithoutDefinedAction
      (Map.make [(aEntity, ⟨
        Map.make [("b", .prim (.int 1))],
        Set.empty,
        Map.empty
      ⟩)])
      false
  ]

/-! ### Request validation examples -/

def requestValidationTests : TestSuite IO :=
  suite "PartialSchema request validation"
  [
    testRequestValidation "optional context fields may be omitted"
      validationSchema
      ⟨bEntity, actionAct, aEntity, Map.empty⟩
      true,
    testRequestValidation "context may refer to an external entity type"
      validationSchema
      ⟨
        bEntity,
        actionAct,
        aEntity,
        Map.make [("reviewer", .prim (.entityUID bReviewer))]
      ⟩
      true,
    testRequestValidation "context may refer to a declared external action UID"
      validationSchema
      ⟨
        bEntity,
        actionAct,
        aEntity,
        Map.make [("delegate", .prim (.entityUID actionG))]
      ⟩
      true,
    testRequestValidation "context requires the declared external entity type exactly"
      validationSchema
      ⟨
        bEntity,
        actionAct,
        aEntity,
        Map.make [("reviewer", .prim (.entityUID dReviewer))]
      ⟩
      false,
    testRequestValidation "appliesTo requires the principal type exactly"
      validationSchema
      ⟨aEntity, actionAct, aEntity, Map.empty⟩
      false,
    testRequestValidation "a request for an external action is invalid"
      validationSchema
      ⟨bEntity, actionG, aEntity, Map.empty⟩
      false
  ]

def tests :=
  [entryTests, completenessTests, validationViewTests, entityValidationTests,
    requestValidationTests]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.PartialSchema
