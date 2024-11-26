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

import CedarProto
import Protobuf
import UnitTest.Run

/-! This file defines unit tests for CedarProto functions. -/

namespace Cedar.Spec.Expr
open Cedar.Data
/-- Ensures that records are sorted by key, including recursively -/
partial def mkWf : Cedar.Spec.Expr → Cedar.Spec.Expr
  | .lit p => .lit p
  | .var v => .var v
  | .ite a b c => .ite a.mkWf b.mkWf c.mkWf
  | .and a b => .and a.mkWf b.mkWf
  | .or a b => .or a.mkWf b.mkWf
  | .unaryApp op x => .unaryApp op x.mkWf
  | .binaryApp op a b => .binaryApp op a.mkWf b.mkWf
  | .getAttr x attr => .getAttr x.mkWf attr
  | .hasAttr x attr => .hasAttr x.mkWf attr
  | .set xs => .set (xs.map mkWf)
  | .record pairs =>
    let m := Map.make (pairs.map λ (k, v) => (k, v.mkWf))
    .record m.kvs
  | .call xfn xs => .call xfn (xs.map mkWf)
end Cedar.Spec.Expr

namespace Cedar.Spec.Policies
def sortByPolicyId : Cedar.Spec.Policies → Cedar.Spec.Policies
  | ps => ps.mergeSort λ a b => a.id < b.id
end Cedar.Spec.Policies

namespace UnitTest.CedarProto

open CedarProto
open Cedar.Data

/--
  `filename` is expected to be the name of a file containing binary protobuf data.
  This test will ensure that that binary data deserializes into the value `expected`.
-/
def testDeserializeProtodata [Inhabited α] [DecidableEq α] [Repr α] [Proto.Message α]
  (filename : String) (expected : α) : TestCase IO :=
  test s!"Deserialize {filename}" ⟨λ () => do
    let buf ← IO.FS.readBinFile filename
    let parsed : Except String α := Proto.Message.interpret? buf
    match parsed with
    | .ok req => checkEq req expected
    | .error e => pure (.error e)
  ⟩

/--
  Similar to `testDeserializeProtodata`, but `f` is applied to the deserialized
  value before comparing to `expected`
-/
def testDeserializeProtodata' [Inhabited α] [DecidableEq β] [Repr β] [Proto.Message α]
  (filename : String) (f : α → β) (expected : β) : TestCase IO :=
  test s!"Deserialize {filename}" ⟨λ () => do
    let buf ← IO.FS.readBinFile filename
    let parsed : Except String α := Proto.Message.interpret? buf
    match parsed with
    | .ok req => checkEq (f req) expected
    | .error e => pure (.error e)
  ⟩

private def mkUid (path : List String) (ty : String) (eid : String) : Cedar.Spec.EntityUID :=
  { ty := { path, id := ty }, eid }

def tests := [
  suite (m := IO) "Cedar Protobuf deserialization tests" [
    testDeserializeProtodata "UnitTest/CedarProto-test-data/false.protodata"
      (Cedar.Spec.Expr.lit (.bool false)),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/true.protodata"
      (Cedar.Spec.Expr.lit (.bool true)),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/345.protodata"
      (Cedar.Spec.Expr.lit (.int (Int64.mk 345 (by decide)))),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/emptystring.protodata"
      (Cedar.Spec.Expr.lit (.string "")),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/thisiscedar.protodata"
      (Cedar.Spec.Expr.lit (.string "this is Cedar")),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/action.protodata"
      (Cedar.Spec.Expr.var .action),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/user_alice.protodata"
      (Cedar.Spec.Expr.lit (.entityUID (mkUid [] "User" "alice"))),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/app_widget_123.protodata"
      (Cedar.Spec.Expr.lit (.entityUID (mkUid ["App"] "Widget" "123"))),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/emptyset.protodata"
      (Cedar.Spec.Expr.set []),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/set.protodata"
      (Cedar.Spec.Expr.set [
        .lit (.int (Int64.mk (-2) (by decide))),
        .lit (.string "minustwo"),
      ]),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/nested_set.protodata"
      (Cedar.Spec.Expr.set [
        .set [ .lit (.int (Int64.mk 1 (by decide))), .lit (.int (Int64.mk 2 (by decide))) ],
        .set [ .lit (.int (Int64.mk 3 (by decide))), .getAttr (.var .principal) "foo" ],
        .lit (.bool false),
      ]),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/emptyrecord.protodata"
      (Cedar.Spec.Expr.record []),
    testDeserializeProtodata' "UnitTest/CedarProto-test-data/record.protodata"
      Cedar.Spec.Expr.mkWf
      (.record [
        ("eggs", .lit (.int (Int64.mk 7 (by decide)))),
        ("ham", .lit (.int (Int64.mk 3 (by decide)))),
      ]),
    testDeserializeProtodata' "UnitTest/CedarProto-test-data/nested_record.protodata"
      Cedar.Spec.Expr.mkWf
      (.record [
        ("eggs", .set [ .lit (.string "this is"), .lit (.string "a set") ]),
        ("ham", .record [
          ("a", .lit (.int (Int64.mk 0 (by decide)))),
          ("b", .lit (.bool false)),
        ]),
      ]),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/principal_in_resource_owners.protodata"
      (Cedar.Spec.Expr.binaryApp .mem (.var .principal) (.getAttr (.var .resource) "owners")),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/has_and_get.protodata"
      (Cedar.Spec.Expr.and
        (.hasAttr (.var .principal) "department")
        (.binaryApp .eq (.getAttr (.var .principal) "department") (.lit (.string "Sales")))
      ),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/has_and_get_tags.protodata"
      (Cedar.Spec.Expr.and
        (.binaryApp .hasTag (.var .principal) (.lit (.string "department")))
        (.binaryApp .eq (.binaryApp .getTag (.var .principal) (.lit (.string "department"))) (.lit (.string "Sales")))
      ),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/not_and_neg.protodata"
      (Cedar.Spec.Expr.or
        (.unaryApp .not (.getAttr (.var .principal) "foo"))
        (.unaryApp .not (.binaryApp .eq
          (.unaryApp .neg (.getAttr (.var .principal) "bar"))
          (.lit (.int (Int64.mk 3 (by decide))))
        ))
      ),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/plus_and_minus_and_times.protodata"
      (Cedar.Spec.Expr.binaryApp .sub
        (.binaryApp .add (.lit (.int (Int64.mk 32 (by decide)))) (.getAttr (.var .context) "count"))
        (.binaryApp .mul (.lit (.int (Int64.mk 7 (by decide)))) (.lit (.int (Int64.mk 4 (by decide)))))
      ),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/contains.protodata"
      (Cedar.Spec.Expr.binaryApp .contains
        (.set [
          (.lit (.int (Int64.mk 2 (by decide)))),
          (.lit (.int (Int64.mk 3 (by decide)))),
          (.lit (.entityUID (mkUid [] "User" "alice"))),
        ])
        (.getAttr (.var .context) "foo")
      ),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/like.protodata"
      (Cedar.Spec.Expr.unaryApp (.like ['a', .star, 'b', .star, .star, 'c', 'd'])
        (.getAttr (.getAttr (.getAttr (.getAttr (.var .context) "a") "b") "c") "d")
      ),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/is.protodata"
      (Cedar.Spec.Expr.and
        (.unaryApp (.is { id := "Widget", path := ["App"] })
          (.lit (.entityUID (mkUid ["App"] "Widget" "123")))
        )
        (.and
          (.unaryApp (.is { id := "Widget", path := ["App"] }) (.getAttr (.var .resource) "widget"))
          (.binaryApp .mem (.getAttr (.var .resource) "widget") (.getAttr (.var .principal) "widgets"))
        )
      ),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/complicated.protodata"
      (Cedar.Spec.Expr.binaryApp .contains
        (.getAttr
          (.getAttr
            (.ite
              (.binaryApp .less (.getAttr (.var .context) "foo") (.lit (.int (Int64.mk 3 (by decide)))))
              (.getAttr (.var .principal) "foo")
              (.getAttr (.var .principal) "bar")
            )
            "a"
          )
          "b"
        )
        (.getAttr (.var .context) "abc")
      ),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/ip.protodata"
      (Cedar.Spec.Expr.call .isInRange [
        (.call .ip [.lit (.string "192.168.0.1")]),
        (.call .ip [.lit (.string "192.0.0.0/8")]),
      ]),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/decimal.protodata"
      (Cedar.Spec.Expr.call .lessThan [
        (.call .decimal [.lit (.string "3.14")]),
        (.call .decimal [.lit (.string "3.1416")]),
      ]),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/rbac.protodata"
      ({
        effect := .permit
        principalScope := .principalScope (.eq (.entityUID (mkUid [] "User" "a b c")))
        actionScope := .actionScope .any
        resourceScope := .resourceScope (.is { id := "Widget", path := ["App"] })
        condition := [{ kind := .when, body := .lit (.bool true) }]
      } : Cedar.Spec.Template),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/abac.protodata"
      ({
        effect := .permit
        principalScope := .principalScope .any
        actionScope := .actionScope .any
        resourceScope := .resourceScope .any
        condition := [
          -- On the Rust side, the `when` and `unless` were collapsed into a
          -- single condition before serializing to protobuf
          {
            kind := .when
            body := .and
              (.binaryApp .eq (.var .principal) (.getAttr (.var .resource) "owner"))
              (.unaryApp .not (.getAttr (.var .resource) "sensitive"))
          },
        ]
      } : Cedar.Spec.Template),
    testDeserializeProtodata' "UnitTest/CedarProto-test-data/policyset.protodata"
      (Cedar.Spec.Policies.sortByPolicyId ∘ Cedar.Spec.Policies.fromLiteralPolicySet)
      [
        {
          id := "linkedpolicy"
          effect := .permit
          principalScope := .principalScope (.eq (mkUid [] "User" "alice"))
          actionScope := .actionScope .any
          resourceScope := .resourceScope .any
          condition := [{
            kind := .when
            body := .unaryApp .not (.binaryApp .lessEq
              (.getAttr (.var .resource) "eligibility")
              (.lit (.int (Int64.mk 2 (by decide))))
            )
          }]
        },
        {
          id := "policy0"
          effect := .permit
          principalScope := .principalScope .any
          actionScope := .actionScope (.eq (mkUid [] "Action" "do"))
          resourceScope := .resourceScope (.eq (mkUid [] "Blob" "thing"))
          condition := [{
            kind := .when
            body := .binaryApp .eq
              (.binaryApp .sub
                (.getAttr (.var .context) "foo")
                (.lit (.int (Int64.mk 7 (by decide))))
              )
              (.getAttr (.var .context) "bar")
          }]
        },
        {
          id := "policy1"
          effect := .forbid
          principalScope := .principalScope (.is { id := "UnauthenticatedUser", path := [] })
          actionScope := .actionScope .any
          resourceScope := .resourceScope .any
          condition := [{
            kind := .when
            body := .getAttr (.var .resource) "requiresAuthentication"
          }]
        },
        {
          id := "policy2"
          effect := .permit
          principalScope := .principalScope .any
          actionScope := .actionInAny [
            (mkUid [] "Action" "1"),
            (mkUid [] "Action" "2"),
          ]
          resourceScope := .resourceScope .any
          condition := [{
            kind := .when
            body := .binaryApp .contains
              (.set [.lit (.string "a"), .lit (.string "b"), .lit (.string "c")])
              (.getAttr (.var .resource) "type")
          }]
        },
      ],
    testDeserializeProtodata "UnitTest/CedarProto-test-data/request.protodata"
      ({
        principal := mkUid [] "User" "alice"
        action := mkUid [] "Action" "access"
        resource := mkUid [] "Folder" "data"
        context := Map.make [ ("foo", .prim (.bool true)) ]
      } : Cedar.Spec.Request),
    testDeserializeProtodata' "UnitTest/CedarProto-test-data/entity.protodata"
      Cedar.Spec.EntityProto.mkWf
      ({
        uid := mkUid ["A"] "B" "C"
        data := {
          attrs := Map.make [
            ("foo", .set (Set.make [
              (.prim (.int (Int64.mk 1 (by decide)))),
              (.prim (.int (Int64.mk (-1) (by decide)))),
            ])),
            ("bar", .prim (.bool false)),
          ]
          ancestors := Set.make [
            (mkUid [] "Parent" "1"),
            (mkUid [] "Grandparent" "A"),
          ]
          tags := Map.make [
            ("tag1", .prim (.string "val1")),
            ("tag2", .prim (.string "val2")),
          ]
        }
      }),
    testDeserializeProtodata' "UnitTest/CedarProto-test-data/entities.protodata"
      Cedar.Spec.EntitiesProto.toEntities
      ((Map.make [
        (mkUid [] "ABC" "123", { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }),
        (mkUid [] "DEF" "234", { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }),
      ]) : Cedar.Spec.Entities),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/type_true.protodata"
      (Cedar.Validation.CedarType.bool .tt),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/type_false.protodata"
      (Cedar.Validation.CedarType.bool .ff),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/type_bool.protodata"
      (Cedar.Validation.CedarType.bool .anyBool),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/type_long.protodata"
      (Cedar.Validation.CedarType.int),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/type_string.protodata"
      (Cedar.Validation.CedarType.string),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/type_set_of_string.protodata"
      (Cedar.Validation.CedarType.set Cedar.Validation.CedarType.string),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/type_ip.protodata"
      (Cedar.Validation.CedarType.ext .ipAddr),
    testDeserializeProtodata "UnitTest/CedarProto-test-data/type_record.protodata"
      (Cedar.Validation.CedarType.record (Map.make [
        ("eggs", .optional .int),
        ("ham", .required .string),
      ])),
    testDeserializeProtodata' "UnitTest/CedarProto-test-data/schema_basic.protodata"
      Cedar.Validation.Proto.ValidatorSchema.toSchema
      {
        ets := Map.make [
          ({ id := "A", path := [] }, {
            attrs := Map.empty
            ancestors := Set.empty
            tags := none
          }),
          ({ id := "B", path := [] }, {
            attrs := Map.empty
            ancestors := Set.make [{ id := "A", path := [] }]
            tags := none
          }),
        ]
        acts := Map.make [
          (mkUid [] "Action" "Read", {
            appliesToPrincipal := Set.empty
            appliesToResource := Set.empty
            ancestors := Set.empty
            context := Map.empty
          }),
          (mkUid [] "Action" "Write", {
            appliesToPrincipal := Set.empty
            appliesToResource := Set.empty
            ancestors := Set.empty
            context := Map.empty
          }),
          (mkUid [] "Action" "ReadX", {
            appliesToPrincipal := Set.make [{ id := "A", path := [] }]
            appliesToResource := Set.make [{ id := "A", path := [] }, { id := "B", path := [] }]
            ancestors := Set.make [mkUid [] "Action" "Read"]
            context := Map.empty
          }),
        ]
      },
    testDeserializeProtodata' "UnitTest/CedarProto-test-data/schema_attrs.protodata"
      Cedar.Validation.Proto.ValidatorSchema.toSchema
      {
        ets := Map.make [
          ({ id := "A", path := [] }, {
            attrs := Map.empty
            ancestors := Set.empty
            tags := none
          }),
          ({ id := "B", path := [] }, {
            attrs := Map.empty
            ancestors := Set.empty
            tags := none
          }),
          ({ id := "C", path := [] }, {
            attrs := Map.make [
              ("a", .required (.bool .anyBool)),
              ("b", .required .int),
              ("c", .optional .string),
              ("d", .required (.entity { id := "A", path := [] })),
              ("e", .required (.set (.entity {id := "B", path := [] }))),
              ("f", .required (.ext .ipAddr)),
              ("g", .required (.record (Map.make [
                ("ham", .required .string),
                ("eggs", .optional .int),
                ("owner", .required (.entity { id := "C", path := [] })),
              ]))),
            ]
            ancestors := Set.empty
            tags := none
          }),
        ]
        acts := Map.make [
          (mkUid [] "Action" "Read", {
            appliesToPrincipal := Set.empty
            appliesToResource := Set.empty
            ancestors := Set.empty
            context := Map.empty
          }),
          (mkUid [] "Action" "Write", {
            appliesToPrincipal := Set.empty
            appliesToResource := Set.empty
            ancestors := Set.empty
            context := Map.empty
          }),
          (mkUid [] "Action" "ReadX", {
            appliesToPrincipal := Set.make [{ id := "A", path := [] }, { id := "B", path := [] }]
            appliesToResource := Set.make [{ id := "B", path := [] }, { id := "C", path := [] }]
            ancestors := Set.make [mkUid [] "Action" "Read"]
            context := Map.make [
              ("a", .required .string),
              ("b", .optional (.entity { id := "B", path := [] })),
              ("c", .required (.set (.entity { id := "A", path := [] }))),
              ("d", .required (.ext .decimal)),
              ("e", .required (.record (Map.make [
                ("ham", .optional (.bool .anyBool)),
                ("eggs", .required .int),
                ("manager", .required (.entity { id := "B", path := [] })),
              ])))
            ]
          }),
        ]
      },
    testDeserializeProtodata' "UnitTest/CedarProto-test-data/schema_commontypes.protodata"
      Cedar.Validation.Proto.ValidatorSchema.toSchema
      {
        ets := Map.make [
          ({ id := "A", path := [] }, {
            attrs := Map.empty
            ancestors := Set.empty
            tags := none
          }),
          ({ id := "B", path := [] }, {
            attrs := Map.empty
            ancestors := Set.empty
            tags := none
          }),
          ({ id := "C", path := [] }, {
            attrs := Map.empty
            ancestors := Set.empty
            tags := none
          }),
          ({ id := "F", path := [] }, {
            attrs := Map.make [
              ("z", .required .string),
              ("y", .optional (.set (.set (.entity { id := "C", path := [] })))),
            ]
            ancestors := Set.make [{ id := "A", path := [] }, { id := "B", path := [] }]
            tags := none
          }),
        ]
        acts := Map.make [
          (mkUid [] "Action" "Read", {
            appliesToPrincipal := Set.make [{ id := "A", path := [] }, { id := "B", path := [] }]
            appliesToResource := Set.make [{ id := "C", path := [] }]
            ancestors := Set.empty
            context := Map.make [
              ("a", .optional (.record (Map.make [
                ("z", .optional .string),
                ("y", .required (.record (Map.make [
                  ("foo", .required (.set (.entity { id := "C", path := [] }))),
                ])))
              ]))),
              ("y", .required (.set (.entity { id := "C", path := [] }))),
            ]
          })
        ]
      },
    testDeserializeProtodata' "UnitTest/CedarProto-test-data/schema_tags.protodata"
      Cedar.Validation.Proto.ValidatorSchema.toSchema
      {
        ets := Map.make [
          ({ id := "A", path := [] }, {
            attrs := Map.empty
            ancestors := Set.empty
            tags := none
          }),
          ({ id := "B", path := [] }, {
            attrs := Map.empty
            ancestors := Set.empty
            tags := none
          }),
          ({ id := "C", path := [] }, {
            attrs := Map.empty
            ancestors := Set.empty
            tags := some .string
          }),
          ({ id := "D", path := [] }, {
            attrs := Map.empty
            ancestors := Set.make [{ id := "B", path := [] }]
            tags := some (.set .string)
          }),
          ({ id := "E", path := [] }, {
            attrs := Map.empty
            ancestors := Set.empty
            tags := some (.set (.entity { id := "A", path := [] }))
          }),
          ({ id := "F", path := [] }, {
            attrs := Map.make [
              ("z", .required (.set .string)),
            ]
            ancestors := Set.make [{ id := "A", path := [] }, { id := "B", path := [] }]
            tags := some .string
          }),
        ]
        acts := Map.empty
      }
  ]
]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.CedarProto
